use ast::analyzed::{Expression, Identity, IdentityKind, PolyID, PolynomialReference};
use itertools::Itertools;
use number::{DegreeType, FieldElement};
use parser_util::lines::indent;
use std::cmp::max;
use std::collections::{BTreeMap, HashSet};
use std::time::Instant;

use crate::witgen::identity_processor::{self, IdentityProcessor};
use crate::witgen::rows::RowUpdater;
use crate::witgen::util::try_to_simple_poly;
use crate::witgen::Constraint;

use super::processor::OuterQuery;
use super::query_processor::QueryProcessor;

use super::rows::{CellValue, Row, RowFactory, RowPair, UnknownStrategy};
use super::{
    Constraints, EvalError, EvalResult, EvalValue, FixedData, MutableState, QueryCallback,
};

/// A list of identities with a flag whether it is complete.
struct CompletableIdentities<'a, T: FieldElement> {
    identities_with_complete: Vec<(&'a Identity<Expression<T>>, bool)>,
}

impl<'a, T: FieldElement> CompletableIdentities<'a, T> {
    fn new(identities: impl Iterator<Item = &'a Identity<Expression<T>>>) -> Self {
        Self {
            identities_with_complete: identities.map(|identity| (identity, false)).collect(),
        }
    }

    /// Yields immutable references to the identity and mutable references to the complete flag.
    fn iter_mut(&mut self) -> impl Iterator<Item = (&'a Identity<Expression<T>>, &mut bool)> {
        self.identities_with_complete
            .iter_mut()
            .map(|(identity, complete)| (*identity, complete))
    }
}

pub struct VmProcessor<'a, T: FieldElement> {
    /// The global index of the first row of [VmProcessor::data].
    row_offset: DegreeType,
    /// The witness columns belonging to this machine
    witnesses: HashSet<PolyID>,
    fixed_data: &'a FixedData<'a, T>,
    /// The subset of identities that contains a reference to the next row
    /// (precomputed once for performance reasons)
    identities_with_next_ref: Vec<&'a Identity<Expression<T>>>,
    /// The subset of identities that does not contain a reference to the next row
    /// (precomputed once for performance reasons)
    identities_without_next_ref: Vec<&'a Identity<Expression<T>>>,
    data: Vec<Row<'a, T>>,
    last_report: DegreeType,
    last_report_time: Instant,
    row_factory: RowFactory<'a, T>,
    latch: Option<Expression<T>>,
    outer_query: Option<OuterQuery<'a, T>>,
    inputs: Option<BTreeMap<PolyID, T>>,
}

impl<'a, T: FieldElement> VmProcessor<'a, T> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        row_offset: DegreeType,
        fixed_data: &'a FixedData<'a, T>,
        identities: &[&'a Identity<Expression<T>>],
        witnesses: HashSet<PolyID>,
        data: Vec<Row<'a, T>>,
        row_factory: RowFactory<'a, T>,
        latch: Option<Expression<T>>,
        outer_query: Option<OuterQuery<'a, T>>,
    ) -> Self {
        let (identities_with_next, identities_without_next): (Vec<_>, Vec<_>) = identities
            .iter()
            .partition(|identity| identity.contains_next_ref());

        let inputs = outer_query.as_ref().map(|outer_query| {
            assert!(latch.is_some());

            let mut inputs = BTreeMap::new();
            for (l, r) in outer_query.left.iter().zip(&outer_query.right.expressions) {
                if let Some(right_poly) = try_to_simple_poly(r).map(|p| p.poly_id()) {
                    if let Some(l) = l.constant_value() {
                        inputs.insert(right_poly, l);
                    }
                }
            }
            inputs
        });

        VmProcessor {
            row_offset,
            witnesses,
            fixed_data,
            identities_with_next_ref: identities_with_next,
            identities_without_next_ref: identities_without_next,
            data,
            row_factory,
            last_report: 0,
            last_report_time: Instant::now(),
            latch,
            outer_query,
            inputs,
        }
    }

    pub fn finish(self) -> (Vec<Row<'a, T>>, bool) {
        (
            self.data,
            self.outer_query
                .map(|outer_query| outer_query.left.iter().all(|v| v.is_constant()))
                .unwrap_or(false),
        )
    }

    /// Starting out with a single row (at a given offset), iteratively append rows
    /// until we have exhausted the rows or the latch expression (if available) evaluates to 1.
    pub fn run<Q: QueryCallback<T>>(
        &mut self,
        mutable_state: &mut MutableState<'a, '_, T, Q>,
    ) -> Constraints<&'a PolynomialReference, T> {
        assert!(!self.data.is_empty());

        let mut outer_assignments = vec![];

        // Are we in an infinite loop and can just re-use the old values?
        let mut looping_period = None;
        let mut loop_detection_log_level = log::Level::Info;
        let rows_left = self.fixed_data.degree - self.row_offset + 1;
        for row_index in 0..rows_left {
            self.maybe_log_performance(row_index);
            // Check if we are in a loop.
            if looping_period.is_none() && row_index % 100 == 0 && row_index > 0 {
                looping_period = self.rows_are_repeating(row_index);
                if let Some(p) = looping_period {
                    log::log!(
                        loop_detection_log_level,
                        "Found loop with period {p} starting at row {row_index}"
                    );
                }
            }
            if let Some(period) = looping_period {
                let proposed_row = self.data[row_index as usize - period].clone();
                if !self.try_proposed_row(row_index, proposed_row, mutable_state) {
                    log::log!(
                        loop_detection_log_level,
                        "Looping failed. Trying to generate regularly again. (Use RUST_LOG=debug to see whether this happens more often.)"
                    );
                    looping_period = None;
                    // For some programs, loop detection will often find loops and then fail.
                    // In this case, we don't want to spam the user with debug messages.
                    loop_detection_log_level = log::Level::Debug;
                }
            }
            // Note that we exit one iteration early in the non-loop case,
            // because ensure_has_next_row() + compute_row() will already
            // add and compute some values for the next row as well.
            if looping_period.is_none() && row_index != rows_left - 1 {
                self.ensure_has_next_row(row_index);
                outer_assignments.extend(self.compute_row(row_index, mutable_state).into_iter());

                if let Some(latch) = self.latch.as_ref() {
                    // Evaluate latch expression and return if it evaluates to 1.
                    let row_pair = RowPair::from_single_row(
                        self.row(row_index),
                        row_index + self.row_offset,
                        self.fixed_data,
                        UnknownStrategy::Unknown,
                    );
                    let latch_value = row_pair.evaluate(latch).unwrap().constant_value().unwrap();
                    if latch_value.is_one() {
                        log::trace!("Machine returns!");
                        return outer_assignments;
                    }
                }
            };
        }

        assert_eq!(
            self.data.len() as DegreeType + self.row_offset,
            self.fixed_data.degree + 1
        );

        outer_assignments
    }

    /// Checks if the last rows are repeating and returns the period.
    /// Only checks for periods of 1, 2, 3 and 4.
    fn rows_are_repeating(&self, row_index: DegreeType) -> Option<usize> {
        if row_index < 4 {
            return None;
        }

        let row = row_index as usize;
        (1..=3).find(|&period| {
            (1..=period).all(|i| {
                self.data[row - i - period]
                    .values()
                    .zip(self.data[row - i].values())
                    .all(|(a, b)| a.value == b.value)
            })
        })
    }

    // Returns a reference to a given row
    fn row(&self, row_index: DegreeType) -> &Row<'a, T> {
        &self.data[row_index as usize]
    }

    fn ensure_has_next_row(&mut self, row_index: DegreeType) {
        assert!(self.data.len() as DegreeType > row_index);
        if row_index == self.data.len() as DegreeType - 1 {
            self.data.push(self.row_factory.fresh_row());
        }
    }

    fn compute_row<Q: QueryCallback<T>>(
        &mut self,
        row_index: DegreeType,
        mutable_state: &mut MutableState<'a, '_, T, Q>,
    ) -> Constraints<&'a PolynomialReference, T> {
        log::trace!("Row: {}", row_index + self.row_offset);

        let mut identity_processor = IdentityProcessor::new(
            self.fixed_data,
            mutable_state.fixed_lookup,
            mutable_state.machines.iter_mut().into(),
        );
        let mut query_processor = mutable_state
            .query_callback
            .as_mut()
            .map(|query| QueryProcessor::new(self.fixed_data, query));

        log::trace!("  Going over all identities until no more progress is made");
        // First, go over identities that don't reference the next row,
        // Second, propagate values to the next row by going over identities that do reference the next row.
        let mut identities_without_next_ref =
            CompletableIdentities::new(self.identities_without_next_ref.iter().cloned());
        let mut identities_with_next_ref =
            CompletableIdentities::new(self.identities_with_next_ref.iter().cloned());
        let outer_assignments = self
            .loop_until_no_progress(
                row_index,
                &mut identities_without_next_ref,
                &mut identity_processor,
                &mut query_processor,
            )
            .and_then(|outer_assignments| {
                Ok(outer_assignments
                    .into_iter()
                    .chain(self.loop_until_no_progress(
                        row_index,
                        &mut identities_with_next_ref,
                        &mut identity_processor,
                        &mut query_processor,
                    )?)
                    .collect::<Vec<_>>())
            })
            .map_err(|e| self.report_failure_and_panic_unsatisfiable(row_index, e))
            .unwrap();

        // TODO: If we fail here, we should return as incomplete
        // Check that the computed row is "final" by asserting that all unknown values can
        // be set to 0.
        log::trace!("  Checking that remaining identities hold when unknown values are set to 0");
        self.process_identities(
            row_index,
            &mut identities_without_next_ref,
            UnknownStrategy::Zero,
            &mut identity_processor,
        )
        .and_then(|_| {
            self.process_identities(
                row_index,
                &mut identities_with_next_ref,
                UnknownStrategy::Zero,
                &mut identity_processor,
            )
        })
        .map_err(|e| self.report_failure_and_panic_underconstrained(row_index, e))
        .unwrap();

        log::trace!(
            "{}",
            self.row(row_index)
                .render(&format!("===== Row {}", row_index), true, &self.witnesses)
        );

        outer_assignments
    }

    /// Loops over all identities and queries, until no further progress is made.
    /// @returns the "incomplete" identities, i.e. identities that contain unknown values.
    fn loop_until_no_progress<Q>(
        &mut self,
        row_index: DegreeType,
        identities: &mut CompletableIdentities<'a, T>,
        identity_processor: &mut IdentityProcessor<'a, '_, T>,
        query_processor: &mut Option<QueryProcessor<'a, '_, T, Q>>,
    ) -> Result<Constraints<&'a PolynomialReference, T>, Vec<EvalError<T>>>
    where
        Q: FnMut(&str) -> Option<T> + Send + Sync,
    {
        let mut outer_assignments = vec![];
        loop {
            let mut progress = self.process_identities(
                row_index,
                identities,
                UnknownStrategy::Unknown,
                identity_processor,
            )?;

            if let Some(outer_query) = self.outer_query.as_ref() {
                let row_pair = RowPair::new(
                    self.row(row_index),
                    self.row(row_index + 1),
                    row_index + self.row_offset,
                    self.fixed_data,
                    UnknownStrategy::Unknown,
                );
                let latch_value = row_pair
                    .evaluate(outer_query.right.selector.as_ref().unwrap())
                    .unwrap()
                    .constant_value()
                    .unwrap();
                if latch_value.is_one() {
                    let (_progress, new_outer_assignments) = self
                        .process_outer_query(row_index, identity_processor)
                        .unwrap();
                    outer_assignments.extend(new_outer_assignments);
                }
            }
            if let Some(query_processor) = query_processor.as_mut() {
                let row_pair = RowPair::new(
                    self.row(row_index),
                    self.row(row_index + 1),
                    row_index + self.row_offset,
                    self.fixed_data,
                    UnknownStrategy::Unknown,
                );
                let updates =
                    query_processor.process_queries_on_current_row(&row_pair, &self.witnesses);
                progress |= self.apply_updates(row_index, &updates, || "query".to_string());
            }
            let input_updates = self.inputs.as_ref().map(|inputs| {
                let mut updates = EvalValue::complete(vec![]);
                for (poly_id, value) in inputs.iter() {
                    match &self.data[row_index as usize][poly_id].value {
                        CellValue::Known(_) => {}
                        CellValue::RangeConstraint(_) | CellValue::Unknown => {
                            updates.combine(EvalValue::complete([(
                                &self.fixed_data.witness_poly_refs[poly_id],
                                Constraint::Assignment(*value),
                            )]));
                        }
                    };
                }
                updates
            });

            if let Some(input_updates) = input_updates {
                // TODO: This should be helpful to make sure that we fail if the inputs are not held constant
                // for the duration of the block. So far it causes a failure, because it takes the input out
                // twice, before and after the reset instruction.
                // for (poly_ref, _) in &input_updates.constraints {
                //     self.inputs.as_mut().unwrap().remove(&poly_ref.poly_id());
                // }
                progress |= self.apply_updates(row_index, &input_updates, || "input".to_string());
            }

            if !progress {
                break;
            }
        }
        Ok(outer_assignments)
    }

    /// Loops over all identities once and updates the current row and next row.
    /// Arguments:
    /// * `identities`: Identities to process. Completed identities are removed from the list.
    /// * `unknown_strategy`: How to process unknown variables. Either use zero or keep it symbolic.
    /// Returns:
    /// * `Ok(true)`: If progress was made.
    /// * `Ok(false)`: If no progress was made.
    /// * `Err(errors)`: If an error occurred.
    fn process_identities(
        &mut self,
        row_index: DegreeType,
        identities: &mut CompletableIdentities<'a, T>,
        unknown_strategy: UnknownStrategy,
        identity_processor: &mut IdentityProcessor<'a, '_, T>,
    ) -> Result<bool, Vec<EvalError<T>>> {
        let mut progress = false;
        let mut errors = vec![];

        for (identity, is_complete) in identities.iter_mut() {
            if *is_complete {
                continue;
            }

            let is_machine_call = matches!(
                identity.kind,
                IdentityKind::Plookup | IdentityKind::Permutation
            );
            if is_machine_call && unknown_strategy == UnknownStrategy::Zero {
                // The fact that we got to the point where we assume 0 for unknown cells, but this identity
                // is still not complete, means that either the inputs or the machine is under-constrained.
                errors.push(format!("{identity}:\n{}",
                    indent("This machine call could not be completed. Either some inputs are missing or the machine is under-constrained.", "    ")).into());
                continue;
            }

            let row_pair = RowPair::new(
                self.row(row_index),
                self.row(row_index + 1),
                row_index + self.row_offset,
                self.fixed_data,
                unknown_strategy,
            );
            let result: EvalResult<'a, T> = identity_processor
                .process_identity(identity, &row_pair)
                .map_err(|err| {
                    format!("{identity}:\n{}", indent(&format!("{err}"), "    ")).into()
                });

            match result {
                Ok(eval_value) => {
                    if unknown_strategy == UnknownStrategy::Zero {
                        assert!(eval_value.constraints.is_empty())
                    } else {
                        *is_complete = eval_value.is_complete();
                        progress |=
                            self.apply_updates(row_index, &eval_value, || format!("{identity}"));
                    }
                }
                Err(e) => {
                    errors.push(e);
                }
            };
        }

        if errors.is_empty() {
            Ok(progress)
        } else {
            Err(errors)
        }
    }

    fn process_outer_query(
        &mut self,
        row_index: DegreeType,
        identity_processor: &mut IdentityProcessor<'a, '_, T>,
    ) -> Result<(bool, Constraints<&'a PolynomialReference, T>), EvalError<T>> {
        let OuterQuery { left, right } = self
            .outer_query
            .as_ref()
            .expect("Asked to process outer query, but it was not set!");

        let row_pair = RowPair::new(
            self.row(row_index),
            self.row(row_index + 1),
            (row_index + self.row_offset) % self.fixed_data.degree,
            self.fixed_data,
            UnknownStrategy::Unknown,
        );

        let updates = identity_processor
            .process_link(left, right, &row_pair)
            .map_err(|e| {
                log::warn!("Error in outer query: {e}");
                log::warn!("Some of the following entries could not be matched:");
                for (l, r) in left.iter().zip(right.expressions.iter()) {
                    if let Ok(r) = row_pair.evaluate(r) {
                        log::warn!("  => {} = {}", l, r);
                    }
                }
                e
            })?;

        let progress = self.apply_updates(row_index, &updates, || "outer query".to_string());

        let outer_assignments = updates
            .constraints
            .into_iter()
            .filter(|(poly, _)| !self.witnesses.contains(&poly.poly_id()))
            .collect::<Vec<_>>();

        Ok((progress, outer_assignments))
    }

    fn apply_updates(
        &mut self,
        row_index: DegreeType,
        updates: &EvalValue<&'a PolynomialReference, T>,
        source_name: impl Fn() -> String,
    ) -> bool {
        if updates.constraints.is_empty() {
            return false;
        }

        log::trace!("    Updates from: {}", source_name());

        // Build RowUpdater
        // (a bit complicated, because we need two mutable
        // references to elements of the same vector)
        let (before, after) = self.data.split_at_mut(row_index as usize + 1);
        let current = before.last_mut().unwrap();
        let next = after.first_mut().unwrap();
        let mut row_updater = RowUpdater::new(current, next, row_index + self.row_offset);

        for (poly, c) in &updates.constraints {
            if self.witnesses.contains(&poly.poly_id()) {
                row_updater.apply_update(poly, c);
            } else if let Constraint::Assignment(v) = c {
                let left = &mut self.outer_query.as_mut().unwrap().left;
                log::trace!("      => {} (outer) = {}", poly, v);
                for l in left.iter_mut() {
                    l.assign(poly, *v);
                }
            };
        }

        true
    }

    fn report_failure_and_panic_unsatisfiable(
        &self,
        row_index: DegreeType,
        failures: Vec<EvalError<T>>,
    ) -> ! {
        log::error!(
            "\nError: Row {} failed. Set RUST_LOG=debug for more information.\n",
            row_index + self.row_offset
        );
        log::debug!("Some identities where not satisfiable after the following values were uniquely determined (known nonzero first, then zero, unknown omitted):");
        log::debug!(
            "{}",
            self.row(row_index)
                .render("Current Row", false, &self.witnesses)
        );
        log::debug!(
            "{}",
            self.row(row_index + 1)
                .render("Next Row", false, &self.witnesses)
        );
        log::debug!("Set RUST_LOG=trace to understand why these values were chosen.");
        log::debug!(
            "Assuming these values are correct, the following identities fail:\n{}\n",
            failures
                .iter()
                .map(|r| indent(&r.to_string(), "    "))
                .join("\n")
        );
        panic!("Witness generation failed.");
    }

    fn report_failure_and_panic_underconstrained(
        &self,
        row_index: DegreeType,
        failures: Vec<EvalError<T>>,
    ) -> ! {
        log::error!(
            "\nError: Row {} failed. Set RUST_LOG=debug for more information.\n",
            row_index + self.row_offset
        );

        log::debug!("Some columns could not be determined, but setting them to zero does not satisfy the constraints. This typically means that the system is underconstrained!");
        log::debug!(
            "{}",
            self.row(row_index)
                .render("Current Row", true, &self.witnesses)
        );
        log::debug!(
            "{}",
            self.row(row_index)
                .render("Next Row", true, &self.witnesses)
        );
        log::debug!("\nSet RUST_LOG=trace to understand why these values were (not) chosen.");
        log::debug!(
            "Assuming zero for unknown values, the following identities fail:\n{}\n",
            failures
                .iter()
                .map(|r| indent(&r.to_string(), "    "))
                .join("\n")
        );
        panic!("Witness generation failed.");
    }

    /// Verifies the proposed values for the next row.
    /// TODO this is bad for machines because we might introduce rows in the machine that are then
    /// not used.
    fn try_proposed_row<Q: QueryCallback<T>>(
        &mut self,
        row_index: DegreeType,
        proposed_row: Row<'a, T>,
        mutable_state: &mut MutableState<'a, '_, T, Q>,
    ) -> bool {
        let mut identity_processor = IdentityProcessor::new(
            self.fixed_data,
            mutable_state.fixed_lookup,
            mutable_state.machines.iter_mut().into(),
        );
        let constraints_valid =
            self.check_row_pair(row_index, &proposed_row, false, &mut identity_processor)
                && self.check_row_pair(row_index, &proposed_row, true, &mut identity_processor);

        if constraints_valid {
            if row_index as usize == self.data.len() - 1 {
                // We might already have added the row in [VmProcessor::ensure_has_next_row]
                self.data[row_index as usize] = proposed_row;
            } else {
                // If the previous row was also added by [VmProcessor::try_propose_row], we won't have an entry
                // for the current row yet.
                assert_eq!(row_index as usize, self.data.len());
                self.data.push(proposed_row);
            }
        } else {
            // Note that we never update the next row if proposing a row succeeds (the happy path).
            // If it doesn't, we re-run compute_next_row on the previous row in order to
            // correctly forward-propagate values via next references.
            self.ensure_has_next_row(row_index - 1);
            self.compute_row(row_index - 1, mutable_state);
        }
        constraints_valid
    }

    fn check_row_pair(
        &self,
        row_index: DegreeType,
        proposed_row: &Row<'a, T>,
        previous: bool,
        identity_processor: &mut IdentityProcessor<'a, '_, T>,
    ) -> bool {
        let row_pair = match previous {
            // Check whether identities with a reference to the next row are satisfied
            // when applied to the previous row and the proposed row.
            true => RowPair::new(
                self.row(row_index - 1),
                proposed_row,
                row_index + self.row_offset - 1,
                self.fixed_data,
                UnknownStrategy::Zero,
            ),
            // Check whether identities without a reference to the next row are satisfied
            // when applied to the proposed row.
            // Because we never access the next row, we can use [RowPair::from_single_row] here.
            false => RowPair::from_single_row(
                proposed_row,
                row_index + self.row_offset,
                self.fixed_data,
                UnknownStrategy::Zero,
            ),
        };

        // Check identities depending on whether or not they have a reference to the next row:
        // - Those that do should be checked on the previous and proposed row
        // - All others should be checked on the proposed row
        let identities = match previous {
            true => &self.identities_with_next_ref,
            false => &self.identities_without_next_ref,
        };

        for identity in identities.iter() {
            if identity_processor
                .process_identity(identity, &row_pair)
                .is_err()
            {
                log::trace!("Previous {:?}", self.row(row_index - 1));
                log::trace!("Proposed {:?}", proposed_row);
                log::trace!("Failed on identity: {}", identity);

                return false;
            }
        }
        true
    }

    fn maybe_log_performance(&mut self, row_index: DegreeType) {
        if row_index >= self.last_report + 1000 {
            let duration = self.last_report_time.elapsed();
            self.last_report_time = Instant::now();

            let identity_statistics = identity_processor::get_and_reset_solving_statistics();
            let identities_per_sec =
                ((identity_statistics.values().map(|s| s.success).sum::<u64>() as u128 * 1000)
                    / duration.as_micros()) as u64;
            let identities_count = max(identity_statistics.len() as u64, 1);
            let progress_percentage = identity_statistics
                .values()
                .map(|s| s.success * 100 / s.invocations)
                .sum::<u64>()
                / identities_count;

            let row = row_index + self.row_offset;
            log::info!(
                "{row} of {} rows ({}%) - {} rows/s, {identities_per_sec}k identities/s, {progress_percentage}% progress",
                self.fixed_data.degree,
                row * 100 / self.fixed_data.degree,
                1_000_000_000 / duration.as_micros()
            );
            self.last_report = row_index;
        }
    }
}
