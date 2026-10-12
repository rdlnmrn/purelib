module
import Purelib.Data.List.OfFn.Basic

import Purelib.Data.Gaussian.Basic
public import Purelib.RootIsolation.Progressive.Extraction.Majorants
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.List.Minimum
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Bezout
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Data
import Purelib.RootIsolation.Progressive.Chamber.Basic
public import Purelib.RootIsolation.Progressive.Chamber.State
import Purelib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Bounds
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Stability
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.RootIsolation.Owner.Local.Basic

/-!
# Joint coefficient targets for a retained simple-root chamber

Each retained owner supplies its predicted clearance and next perturbation
target. The common coefficient request is bounded by the permanent chamber
request, the current transport guard and every computed next-step guard.
-/

public section

namespace Purelib.RootIsolation.Progressive.Chamber.State.ChamberContinuationState

open Purelib.Data.Rat
open Purelib
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Data.Gaussian

/-- Exact lower bound for the clearance after coefficient transport.

The retained stability gap is squared and divided by four times the current
polynomial's norm majorant on the original owner box. -/
@[expose] def transportedClearanceBound
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (index : chamber.Index) :
    Fraction.Rational :=
  ((state.family.owner index).clearance.bound -
      state.table.refinementEvaluationBound state.guardTarget
        (state.budgetBox index)) ^ 2 /
    (4 * Dense.Gaussian.Bounds.Box.denseEvalNormMajorant state.table.polynomial
      (state.family.owner index).box)

/-- Pre-reading lower bound for the clearance of the next extracted owner.

The bound uses the retained transported clearance, reference extraction
majorants and the supplied perturbation size on the same original box. -/
@[expose] def predictedOwnerClearance
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (index : chamber.Index)
    (epsilon : Fraction.Rational) : Fraction.Rational :=
  Dense.Gaussian.Newton.Box.Budget.Data.predictedExtractionClearanceData
    (state.family.owner index).box
    (Dense.Gaussian.Derivative.Separation.Bezout.approximateMargin chamber.squarefree.right
      (chamber.owners.owner index).box)
    (state.transportedClearanceBound index)
    (reference.admittedExtractionLipschitz chamber.target
      (state.family.owner index).box)
    (reference.admittedExtractionTaylor chamber.target
      (state.family.owner index).box)
    (reference.admittedExtractionDerivative chamber.target
      (state.family.owner index).box)
    epsilon

/-- Per-owner perturbation target for the predicted extracted clearance.

The current coefficient table computes its stability target on the original
owner box using that owner's predicted clearance. -/
@[expose] def nextOwnerGuardTarget
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (index : chamber.Index)
    (epsilon : Fraction.Rational) : Fraction.Rational :=
  state.table.stabilityTargetForBound (state.family.owner index).box
    (state.predictedOwnerClearance index epsilon)

/-- Collect the next perturbation targets of the original retained owner family in index order. -/
@[expose] def nextOwnerGuardTargets
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational) :
    List Fraction.Rational :=
  List.ofFn fun index : chamber.Index =>
    state.nextOwnerGuardTarget index epsilon

/-- Compute the positive minimum of the retained per-owner next-step targets. -/
@[expose] def nextGuardTarget
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational) :
    Fraction.Rational :=
  Data.Rat.List.Minimum.positiveMinimum (state.nextOwnerGuardTargets epsilon)

/-- Single simultaneous coefficient request for the retained chamber.

The nested minimum bounds the request by the permanent chamber target, the
current transport guard and the common predicted next-step guard. -/
@[expose] def coefficientTarget
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational) :
    Fraction.Rational :=
  min chamber.target (min state.guardTarget (state.nextGuardTarget epsilon))

/-- The joint coefficient request fits the original permanent chamber target. -/
theorem coefficientTarget_le_chamber
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational) :
    state.coefficientTarget epsilon ≤ chamber.target := Fraction.Order.Basic.min_le_left _ _

/-- The joint coefficient request fits the currently retained guard target. -/
theorem coefficientTarget_le_guard
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational) :
    state.coefficientTarget epsilon ≤ state.guardTarget :=
  (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)

/-- The joint coefficient request fits the computed next-step guard target. -/
theorem coefficientTarget_le_nextGuard
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational) :
    state.coefficientTarget epsilon ≤ state.nextGuardTarget epsilon :=
  (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)

/-- The common next-step target fits each original owner's individual target. -/
theorem nextGuardTarget_le_owner
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (epsilon : Fraction.Rational)
    (index : chamber.Index) :
    state.nextGuardTarget epsilon ≤
      state.nextOwnerGuardTarget index epsilon := by
  apply Data.Rat.List.Minimum.positiveMinimum_le_of_mem
  exact Data.List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩

/-- The retained stable refinement leaves a strictly positive transported clearance bound. -/
theorem transportedClearanceBound_pos
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (index : chamber.Index) :
    0 < state.transportedClearanceBound index := by
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct
      (Fraction.Order.Arithmetic.sub_pos_direct (state.stable index)) 2)
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Dense.Gaussian.Bounds.Box.denseEvalNormMajorant_pos
        state.table.polynomial (state.family.owner index).box))

/-- The predicted clearance of each retained owner is strictly positive. -/
theorem predictedOwnerClearance_pos
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (index : chamber.Index)
    {epsilon : Fraction.Rational} (positive : 0 < epsilon) :
    0 < state.predictedOwnerClearance index epsilon := by
  exact Dense.Gaussian.Newton.Box.Budget.Data.predictedExtractionClearanceData_pos
    (state.family.owner index).proper
    (Dense.Gaussian.Derivative.Separation.Bezout.approximateMargin_pos
      chamber.squarefree.right (chamber.owners.owner index).box)
    (state.transportedClearanceBound_pos index)
    (reference.admittedExtractionLipschitz_pos chamber.target
      (state.family.owner index).box)
    (reference.admittedExtractionTaylor_pos chamber.target
      (state.family.owner index).box)
    (reference.admittedExtractionDerivative_pos chamber.target
      (state.family.owner index).box)
    positive

/-- Each original owner has a strictly positive next-step perturbation target. -/
theorem nextOwnerGuardTarget_pos
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) (index : chamber.Index)
    {epsilon : Fraction.Rational} (positive : 0 < epsilon) :
    0 < state.nextOwnerGuardTarget index epsilon :=
  state.table.stabilityTargetForBound_pos (state.family.owner index).box
    (state.predictedOwnerClearance_pos index positive)

/-- The finite family's computed common next-step target is strictly positive. -/
theorem nextGuardTarget_pos
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) {epsilon : Fraction.Rational}
    (positive : 0 < epsilon) : 0 < state.nextGuardTarget epsilon := by
  apply Data.Rat.List.Minimum.positiveMinimum_pos
  intro target member
  rcases Data.List.OfFn.Basic.mem_ofFn.mp member with ⟨index, rfl⟩
  exact state.nextOwnerGuardTarget_pos index positive

/-- The joint chamber, current-guard and next-guard coefficient request is strictly positive. -/
theorem coefficientTarget_pos
    {reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable} {chamber :
      Progressive.Chamber.Basic.SimpleRootChamber reference}
    (state : Progressive.Chamber.State.ChamberContinuationState chamber) {epsilon : Fraction.Rational}
    (positive : 0 < epsilon) : 0 < state.coefficientTarget epsilon :=
  Fraction.Order.Basic.lt_min chamber.target_pos
    (Fraction.Order.Basic.lt_min state.guardPositive (state.nextGuardTarget_pos positive))

end Purelib.RootIsolation.Progressive.Chamber.State.ChamberContinuationState

end
