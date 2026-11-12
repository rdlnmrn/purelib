module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry.Between.Reference.Requested
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global
import Purelib.Approximation.AccuracyRequest.Scaling
import Purelib.Data.Fin.Two
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Requested accuracy for the four fixed-reference parameter quotients

One positive quadrance radius pays all four original-geometry factors and
the unit-increment condition. The given reference jets remain fixed before
accuracy; the retained all-later bounds supply their actual sample errors.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {remaining : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: remaining)}

/-- The fixed-reference quotient factor depends only on the original covered parent geometry. -/
@[expose] def referenceFactor (order coordinate : Fin 2) : Rational :=
  4 * (ValueBlocks.factor (covered := covered) order coordinate + 3)

/-- Every original fixed-reference quotient factor is nonnegative. -/
theorem referenceFactor_nonnegative (order coordinate : Fin 2) :
    0 ≤ referenceFactor (covered := covered) order coordinate :=
  Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 4)
    ((Field.zero_add (0 : Rational)).symm.trans_le
      (Order.Arithmetic.add_le_add_direct
        (ValueBlocks.factor_nonnegative (covered := covered) order coordinate)
        (by decide +kernel : (0 : Rational) ≤ 3)))

/-- The original quotient factor plus one is a strictly positive request divisor. -/
private theorem divisor_positive (order coordinate : Fin 2) :
    0 < referenceFactor (covered := covered) order coordinate + 1 :=
  Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (referenceFactor_nonnegative (covered := covered) order coordinate)
    (by decide +kernel : (0 : Rational) < 1)

/-- Compute a positive quadrance radius for one original fixed-reference quotient error. -/
def referenceIncrementRequest (accuracy : AccuracyRequest) (order coordinate : Fin 2) : AccuracyRequest :=
  accuracy.divide (referenceFactor (covered := covered) order coordinate + 1)
    (divisor_positive (covered := covered) order coordinate)

/-- The retained row radius is the original requested error divided by its actual factor plus one. -/
theorem referenceIncrementRequest_tolerance (accuracy : AccuracyRequest) (order coordinate : Fin 2) :
    (referenceIncrementRequest (covered := covered) accuracy order coordinate).tolerance =
      accuracy.tolerance / (referenceFactor (covered := covered) order coordinate + 1) := by
  unfold referenceIncrementRequest
  rfl

/-- Compute one positive quadrance radius paying all four quotient rows and the unit-increment condition.

Only the original covered geometry and requested error enter this finite
minimum. Reference preparations, jets, request stages and adaptive child
counts do not participate in choosing the radius.
-/
def referenceRequest (accuracy : AccuracyRequest) : AccuracyRequest :=
  let valueZero := referenceIncrementRequest (covered := covered) accuracy 0 0
  let valueOne := referenceIncrementRequest (covered := covered) accuracy 0 1
  let firstZero := referenceIncrementRequest (covered := covered) accuracy 1 0
  let firstOne := referenceIncrementRequest (covered := covered) accuracy 1 1
  let unit : AccuracyRequest := ⟨1, by decide +kernel⟩
  unit.minimum ((valueZero.minimum valueOne).minimum (firstZero.minimum firstOne))

/-- The same computed radius pays the original unit-increment condition. -/
theorem referenceRequest_le_unit (accuracy : AccuracyRequest) :
    (referenceRequest (covered := covered) accuracy).tolerance ≤ 1 := by
  unfold referenceRequest
  exact AccuracyRequest.minimum_le_left _ _

/-- Every original row receives payment from the one computed quadrance radius. -/
theorem referenceRequest_le_row (accuracy : AccuracyRequest) (order coordinate : Fin 2) :
    (referenceRequest (covered := covered) accuracy).tolerance ≤
      (referenceIncrementRequest (covered := covered) accuracy order coordinate).tolerance := by
  let valueZero := referenceIncrementRequest (covered := covered) accuracy 0 0
  let valueOne := referenceIncrementRequest (covered := covered) accuracy 0 1
  let firstZero := referenceIncrementRequest (covered := covered) accuracy 1 0
  let firstOne := referenceIncrementRequest (covered := covered) accuracy 1 1
  let unit : AccuracyRequest := ⟨1, by decide +kernel⟩
  have paid := unit.minimum_le_right ((valueZero.minimum valueOne).minimum (firstZero.minimum firstOne))
  have valuePaid := paid.trans ((valueZero.minimum valueOne).minimum_le_left (firstZero.minimum firstOne))
  have firstPaid := paid.trans ((valueZero.minimum valueOne).minimum_le_right (firstZero.minimum firstOne))
  unfold referenceRequest
  refine Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index)) order
  · exact Fin.cases (valuePaid.trans (valueZero.minimum_le_left valueOne))
      (Fin.cases (valuePaid.trans (valueZero.minimum_le_right valueOne))
        (fun index => Fin.elim0 index)) coordinate
  · exact Fin.cases (firstPaid.trans (firstZero.minimum_le_left firstOne))
      (Fin.cases (firstPaid.trans (firstZero.minimum_le_right firstOne))
        (fun index => Fin.elim0 index)) coordinate

/-- The computed row radius makes its actual factor-times-quadrance error strictly smaller than requested. -/
private theorem factor_error_lt (accuracy : AccuracyRequest) (order coordinate : Fin 2)
    {increment : Canonical} (nonzero : increment ≠ 0)
    (small : Norm.Basic.normSq increment ≤
      (referenceIncrementRequest (covered := covered) accuracy order coordinate).tolerance) :
    referenceFactor (covered := covered) order coordinate * Canonical.normSq increment < accuracy.tolerance := by
  have smallCanonical := (Norm.Basic.normSq_eq_canonical increment).symm.trans_le small
  have paid := (Order.Field.le_div_iff_pos (divisor_positive (covered := covered) order coordinate)).mp
    (smallCanonical.trans_eq (referenceIncrementRequest_tolerance (covered := covered) accuracy order coordinate))
  have positive : (0 : Rational) < Canonical.normSq increment :=
    (Norm.Basic.normSq_pos nonzero).trans_eq (Norm.Basic.normSq_eq_canonical increment)
  let factor := referenceFactor (covered := covered) order coordinate
  have strict : factor * Canonical.normSq increment < Canonical.normSq increment * (factor + 1) :=
    (show factor * Canonical.normSq increment = factor * Canonical.normSq increment + 0 by ring1).trans_lt
      ((Order.Arithmetic.add_lt_add_left_direct positive (factor * Canonical.normSq increment)).trans_eq
        (by ring1))
  exact strict.trans_le paid

/-- The one positive radius pays every sufficiently late actual quotient of the two retained reference jets.

The original quantified bound retains the jet owners and its two sampling
floors. The only extra conditions are a nonzero offset difference and its
quadrance payment to the computed radius; no sample-error bound is added.
-/
theorem QuotientBounds.accurate
    {firstOffset lastOffset : Canonical}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {firstJet : SynchronizedPeriodJet firstFrame} {lastJet : SynchronizedPeriodJet lastFrame}
    {firstFloor lastFloor : Nat}
    (bounds : QuotientBounds covered firstJet lastJet firstFloor lastFloor)
    (accuracy : AccuracyRequest) (nonzero : lastOffset - firstOffset ≠ 0)
    (small : Norm.Basic.normSq (lastOffset - firstOffset) ≤
      (referenceRequest (covered := covered) accuracy).tolerance)
    (order coordinate : Fin 2) (firstIndex lastIndex : Nat)
    (firstAfter : firstFloor ≤ firstIndex) (lastAfter : lastFloor ≤ lastIndex) :
    Canonical.normSq
      ((((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((lastJet.value coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((lastJet.first coordinate).integral)
            (fun index => Fin.elim0 index)) order).model lastIndex).integralSample -
        ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((firstJet.value coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((firstJet.first coordinate).integral)
            (fun index => Fin.elim0 index)) order).model firstIndex).integralSample) / (lastOffset - firstOffset) -
        ((Fin.cases (motive := fun _ : Fin 2 => RefinementProgram) ((firstJet.first coordinate).integral)
          (Fin.cases (motive := fun _ : Fin 1 => RefinementProgram) ((firstJet.second coordinate).integral)
            (fun index => Fin.elim0 index)) order).model firstIndex).integralSample) < accuracy.tolerance :=
  (bounds order coordinate firstIndex lastIndex firstAfter lastAfter).trans_lt
    (factor_error_lt (covered := covered) accuracy order coordinate nonzero
      (small.trans (referenceRequest_le_row (covered := covered) accuracy order coordinate)))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows

end
