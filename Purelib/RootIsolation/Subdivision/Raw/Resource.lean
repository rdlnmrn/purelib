module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Interval.Candidates.Resource
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Resource
import Purelib.Polynomial.Clearance.Box.Grid.Four.Resource
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.Subdivision.Raw.Grid.Elimination
public import Purelib.RootIsolation.Subdivision.Raw.Iteration
import Purelib.RootIsolation.Subdivision.Raw.Iteration.Forward
public import Purelib.RootIsolation.Subdivision.Raw.Request
import Purelib.RootIsolation.Subdivision.Raw.Selection
import Purelib.RootIsolation.Subdivision.Raw.Step

import Purelib.Data.Nat.Multiplication
import Purelib.Polynomial.Clearance.Box.Grid.Four.Basic
import Purelib.Polynomial.Clearance.Box.Grid.Four.Elimination

/-!
# Resource bounds for raw subdivision

The search budget counts the two coordinate scans and four child windings in each round. The magnitude envelope iterates
the rational safe-cut bound along the retained child boxes for the supplied finite depth.
-/

namespace Purelib.RootIsolation.Subdivision.Raw.Resource

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation

/-- Two safe-coordinate scans and at most four child windings are accounted
for in every raw subdivision round.

The two coordinate searches use the finite candidate evaluation budget. The remaining four units account for the child
winding searches. -/
@[expose] public def subdivisionRoundSearchBudget (degreeBound : Nat) : Nat :=
  2 * Data.Rat.Interval.Candidates.Resource.safeCandidateEvaluationBudget degreeBound + 4

/-- Multiply the per-round safe-coordinate and child-winding search budget by the retained depth.

The finite depth multiplies the same per-round count of coordinate scans and child windings. -/
@[expose] public def subdivisionSearchBudget (degreeBound depth : Nat) : Nat :=
  depth * Subdivision.Raw.Resource.subdivisionRoundSearchBudget degreeBound

/-- One additional subdivision round adds exactly the per-round search budget.

Distributivity over the successor depth separates the previous budget from the single additional round. -/
public theorem subdivisionSearchBudget_succ (degreeBound depth : Nat) :
    Subdivision.Raw.Resource.subdivisionSearchBudget degreeBound (depth + 1) =
      Subdivision.Raw.Resource.subdivisionSearchBudget degreeBound depth +
        Subdivision.Raw.Resource.subdivisionRoundSearchBudget degreeBound := by
  unfold Subdivision.Raw.Resource.subdivisionSearchBudget
  rw [Data.Nat.Multiplication.right_distrib, Nat.one_mul]

/-- One safe raw subdivision keeps the selected child coordinates within the computed safe-cut magnitude envelope.

Each of the four retained child boxes satisfies the same safe-cut bound. Selecting the first nonzero child preserves
that coordinate certificate. -/
public theorem refineOnce_box_within
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
      bound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : State.Raw.RawWindingState p ambient)
    (boxWithin : Box.Resource.BoxWithin state.box bound) :
    Box.Resource.BoxWithin (Subdivision.Raw.Step.refineOnce elimination state).box
      (Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound degreeBound) := by
  let grid := Subdivision.Raw.Grid.Elimination.safeRawFourGrid elimination state
  have children := Clearance.Box.Grid.Four.Resource.clearFourGrid_children_within elimination state.box
    state.proper boxWithin
  have lowerLeft : Box.Resource.BoxWithin grid.lowerLeft.box
      (Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound degreeBound) := by
    simpa only [grid, Subdivision.Raw.Grid.Elimination.safeRawFourGrid_lowerLeft_box]
      using children.1
  have upperLeft : Box.Resource.BoxWithin grid.upperLeft.box
      (Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound degreeBound) := by
    simpa only [grid, Subdivision.Raw.Grid.Elimination.safeRawFourGrid_upperLeft_box]
      using children.2.1
  have lowerRight : Box.Resource.BoxWithin grid.lowerRight.box
      (Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound degreeBound) := by
    simpa only [grid, Subdivision.Raw.Grid.Elimination.safeRawFourGrid_lowerRight_box]
      using children.2.2.1
  have upperRight : Box.Resource.BoxWithin grid.upperRight.box
      (Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound degreeBound) := by
    simpa only [grid, Subdivision.Raw.Grid.Elimination.safeRawFourGrid_upperRight_box]
      using children.2.2.2
  change Box.Resource.BoxWithin (Subdivision.Raw.Selection.firstNonzeroChild grid).box _
  unfold Subdivision.Raw.Selection.firstNonzeroChild
  split
  · exact lowerLeft
  · split
    · exact upperLeft
    · split
      · exact lowerRight
      · exact upperRight

/-- Iterate the safe-cut magnitude envelope for the supplied finite subdivision depth.

The zero-depth result is the supplied initial magnitude. Each successor applies one safe-cut envelope to the preceding
retained bound. -/
@[expose] public def refinementMagnitudeEnvelope (degreeBound : Nat) : Nat → Nat → Nat
  | initial, 0 => initial
  | initial, depth + 1 =>
      Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope
        (Purelib.RootIsolation.Subdivision.Raw.Resource.refinementMagnitudeEnvelope degreeBound initial depth)
          degreeBound

/-- Fixed-depth raw refinement stays within the iterated coordinate magnitude envelope.

The initial box certificate starts the iteration. Each retained child adds one safe-cut envelope at the same supplied
degree bound. -/
public theorem refineN_box_within
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
      initial : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : State.Raw.RawWindingState p ambient)
    (initialWithin : Box.Resource.BoxWithin state.box initial) (depth : Nat) :
    Box.Resource.BoxWithin (Subdivision.Raw.Iteration.refineN elimination depth state).box
      (Subdivision.Raw.Resource.refinementMagnitudeEnvelope degreeBound initial depth) := by
  induction depth with
  | zero => exact initialWithin
  | succ depth inductionHypothesis =>
      exact Subdivision.Raw.Resource.refineOnce_box_within elimination
        (Subdivision.Raw.Iteration.refineN elimination depth state)
        inductionHypothesis

/-- Starting after one safe-cut envelope equals adding one round to the envelope iteration.

Induction on the finite depth identifies the same ordered sequence of safe-cut envelope steps on both sides. -/
public theorem refinementMagnitudeEnvelope_after_safeCut
    (degreeBound initial depth : Nat) :
    Subdivision.Raw.Resource.refinementMagnitudeEnvelope degreeBound
        (Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope initial degreeBound) depth =
      Subdivision.Raw.Resource.refinementMagnitudeEnvelope degreeBound initial (depth + 1) := by
  induction depth with
  | zero =>
      rw [Subdivision.Raw.Resource.refinementMagnitudeEnvelope.eq_1,
        Subdivision.Raw.Resource.refinementMagnitudeEnvelope.eq_2,
        Subdivision.Raw.Resource.refinementMagnitudeEnvelope.eq_1]
  | succ depth inductionHypothesis =>
      rw [Subdivision.Raw.Resource.refinementMagnitudeEnvelope.eq_2,
        Subdivision.Raw.Resource.refinementMagnitudeEnvelope.eq_2]
      exact congrArg
        (fun bound => Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope bound degreeBound)
        inductionHypothesis

/-- Forward raw refinement stays within the same fixed-depth coordinate magnitude envelope.

The forward iteration selects the same certified child at each round. Its recursive coordinate bound agrees with the
displayed envelope iteration. -/
public theorem refineForwardN_box_within
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
      initial : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : State.Raw.RawWindingState p ambient)
    (initialWithin : Box.Resource.BoxWithin state.box initial) (depth : Nat) :
    Box.Resource.BoxWithin (Subdivision.Raw.Iteration.Forward.refineForwardN elimination depth state).box
      (Subdivision.Raw.Resource.refinementMagnitudeEnvelope degreeBound initial depth) := by
  induction depth generalizing state initial with
  | zero => exact initialWithin
  | succ depth inductionHypothesis =>
      let next := Subdivision.Raw.Step.refineOnce elimination state
      have nextWithin :
          Box.Resource.BoxWithin next.box (Data.Rat.Interval.Candidates.Resource.safeCutMagnitudeEnvelope initial
            degreeBound) :=
        Subdivision.Raw.Resource.refineOnce_box_within elimination state initialWithin
      have recursive := inductionHypothesis next nextWithin
      rw [Subdivision.Raw.Resource.refinementMagnitudeEnvelope_after_safeCut] at recursive
      exact recursive

/-- The threshold-requested raw refinement stays within the envelope computed from the box magnitude and refinement
depth.

The threshold request computes a finite depth from the original state. Starting with the box endpoint maximum bounds the
resulting selected box. -/
public theorem refineTo_box_within
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (state : State.Raw.RawWindingState p ambient)
    (threshold : Fraction.Rational) :
    Box.Resource.BoxWithin (Subdivision.Raw.Request.refineTo elimination state threshold).box
      (Subdivision.Raw.Resource.refinementMagnitudeEnvelope degreeBound (Box.Resource.boxMagnitude state.box)
        (Subdivision.Raw.Request.refinementDepth state threshold)) := by
  exact Subdivision.Raw.Resource.refineForwardN_box_within elimination state (Box.Resource.box_within_boxMagnitude
    state.box)
    (Subdivision.Raw.Request.refinementDepth state threshold)

end Purelib.RootIsolation.Subdivision.Raw.Resource
