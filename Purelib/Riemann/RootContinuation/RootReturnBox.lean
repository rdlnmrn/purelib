module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
public import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
public import Purelib.RootIsolation.SquareRoot.Replay.MovingRecenterReplay
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Track.Basic
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

namespace Purelib.Riemann.RootContinuation.RootReturnBox
open Purelib.Riemann.Integration Purelib.Riemann.Topology
open Purelib.Data.Rat in
/-- The rational coordinate carrier of return-box enclosures. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of root parameters. -/
abbrev Gaussian := Basic.Canonical
/-- The rational rectangle carrier of retained root boxes. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root continuation owner at the fixed parameter. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner

section
open Purelib.Data.Rat
/-- Enclose two root boxes with padding equal to one sixteenth of the first box's width.

Properness of the first box makes the padding positive in both coordinates; componentwise minima and maxima retain both
input boxes inside the result. -/
@[expose] def enclosure (first second : Box) (proper : first.Proper) : Box :=
  let padding := first.widthX / 16
  have paddingNonnegative : 0 ≤ padding :=
    (Fraction.Order.Field.div_pos_direct (Fraction.Order.Arithmetic.sub_pos_direct proper.1) (by decide)).le
  have below (value : Coordinate) : value - padding ≤ value := by
    calc
      value - padding ≤ value - 0 :=
        Fraction.Order.Arithmetic.sub_le_sub_left_direct paddingNonnegative value
      _ = value := by ring1
  have above (value : Coordinate) : value ≤ value + padding := by
    calc
      value = value + 0 := by ring1
      _ ≤ value + padding :=
        Fraction.Order.Arithmetic.add_le_add_direct (le_refl value) paddingNonnegative
  { xLower := min first.xLower second.xLower - padding
    xUpper := max first.xUpper second.xUpper + padding
    yLower := min first.yLower second.yLower - padding
    yUpper := max first.yUpper second.yUpper + padding
    x_valid := (below _).trans
      ((Fraction.Order.Basic.min_le_left _ _).trans (first.x_valid.trans
        ((Fraction.Order.Basic.le_max_left _ _).trans (above _))))
    y_valid := (below _).trans
      ((Fraction.Order.Basic.min_le_left _ _).trans (first.y_valid.trans
        ((Fraction.Order.Basic.le_max_left _ _).trans (above _)))) }

/-- The first original box lies strictly inside the padded enclosure.

The first box retains its original coordinate bounds. Positive padding is combined with the corresponding minimum and
maximum projections to give all four strict interior inequalities. -/
theorem first_strict (first second : Box) (proper : first.Proper) :
    first.StrictInterior (enclosure first second proper) := by
  have positive : 0 < first.widthX / 16 :=
    Fraction.Order.Field.div_pos_direct (Fraction.Order.Arithmetic.sub_pos_direct proper.1) (by decide)
  have below (value : Coordinate) : value - first.widthX / 16 < value := by
    calc
      value - first.widthX / 16 < value - 0 :=
        Fraction.Order.Arithmetic.sub_lt_sub_left_direct positive value
      _ = value := by ring1
  have above (value : Coordinate) : value < value + first.widthX / 16 := by
    calc
      value = value + 0 := by ring1
      _ < value + first.widthX / 16 :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct positive value
  exact ⟨(below _).trans_le (Fraction.Order.Basic.min_le_left _ _),
    (Fraction.Order.Basic.le_max_left _ _).trans_lt (above _),
    (below _).trans_le (Fraction.Order.Basic.min_le_left _ _),
    (Fraction.Order.Basic.le_max_left _ _).trans_lt (above _)⟩

/-- The second original box lies strictly inside the padded enclosure.

The second box retains its original coordinate bounds. Positive padding from the first proper box and the opposite
minimum and maximum projections give all four strict interior inequalities. -/
theorem second_strict (first second : Box) (proper : first.Proper) :
    second.StrictInterior (enclosure first second proper) := by
  have positive : 0 < first.widthX / 16 :=
    Fraction.Order.Field.div_pos_direct (Fraction.Order.Arithmetic.sub_pos_direct proper.1) (by decide)
  have below (value : Coordinate) : value - first.widthX / 16 < value := by
    calc
      value - first.widthX / 16 < value - 0 :=
        Fraction.Order.Arithmetic.sub_lt_sub_left_direct positive value
      _ = value := by ring1
  have above (value : Coordinate) : value < value + first.widthX / 16 := by
    calc
      value = value + 0 := by ring1
      _ < value + first.widthX / 16 :=
        Fraction.Order.Arithmetic.add_lt_add_left_direct positive value
  exact ⟨(below _).trans_le (Fraction.Order.Basic.min_le_right _ _),
    (Fraction.Order.Basic.le_max_right _ _).trans_lt (above _),
    (below _).trans_le (Fraction.Order.Basic.min_le_right _ _),
    (Fraction.Order.Basic.le_max_right _ _).trans_lt (above _)⟩

end

/-- The padded enclosure is proper whenever the first original box is proper. -/
theorem enclosure_proper (first second : Box) (proper : first.Proper) :
    (enclosure first second proper).Proper :=
  let inside := first_strict first second proper
  ⟨(inside.left.trans proper.1).trans inside.right,
    (inside.bottom.trans proper.2).trans inside.top⟩

open Purelib.Approximation.Gaussian in
/-- Compare the two original root names through the supplied common owner.

Both initial boxes must lie strictly inside the common owner's box; the result keeps the final-to-initial comparison
direction and original root-name conventions. -/
@[expose] def equivalent {parameter : Gaussian} (first last common : Owner parameter)
    (firstInside : first.track.initial.box.StrictInterior common.track.initial.box)
    (lastInside : last.track.initial.box.StrictInterior common.track.initial.box) :
    Equivalence.NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName first.parameterNonzero last)
      (SquareRootTrackEquivalence.ownerRootName first.parameterNonzero first) :=
  (SquareRootTrackEquivalence.rootEquivalent_of_initial_strict first.parameterNonzero
    common.track last.track lastInside).symm.trans
    (SquareRootTrackEquivalence.rootEquivalent_of_initial_strict first.parameterNonzero
      common.track first.track firstInside)

variable {parameter : Gaussian} (first last : Owner parameter)

set_option genInjectivity false in
/-- The exact candidate enclosure retained for a two-owner return check.

The box equality ties the attempt to the prescribed padded enclosure of the original first and last owner boxes. -/
structure Attempt where
  /-- The retained candidate rectangle for the original two-owner return attempt. -/ box : Box
  /-- The retained rectangle is exactly the prescribed candidate enclosure. -/ box_eq : box = enclosure
    first.track.initial.box last.track.initial.box first.track.initial.proper

constructive_injectivity Attempt

/-- Retain the prescribed padded enclosure of the two original owner boxes. -/
@[expose] def Attempt.build : Attempt first last :=
  ⟨enclosure first.track.initial.box last.track.initial.box first.track.initial.proper, rfl⟩

namespace Attempt
variable {first last}

/-- The retained return-check enclosure is proper. -/
theorem proper (attempt : Attempt first last) : attempt.box.Proper := by
  rw [attempt.box_eq]
  exact enclosure_proper _ _ _

/-- The first owner's original box lies strictly inside the retained attempt. -/
theorem firstInside (attempt : Attempt first last) : first.track.initial.box.StrictInterior attempt.box := by
  rw [attempt.box_eq]
  exact first_strict _ _ _

/-- The last owner's original box lies strictly inside the retained attempt. -/
theorem lastInside (attempt : Attempt first last) : last.track.initial.box.StrictInterior attempt.box := by
  rw [attempt.box_eq]
  exact second_strict _ _ _
end Attempt

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
set_option genInjectivity false in
/-- The exact finite obstruction encountered while checking the candidate return box.

The ordered alternatives retain earlier nonzero axis tests, the first zero determinant or the observed non-unit winding
value. They establish only why this enclosure attempt did not certify a common root. -/
inductive Reason (box : Box) where
  /-- The candidate's left-axis determinant is zero. -/ | leftZero (zero : QuadraticAxisElimination.verticalDeterminant
    parameter box.xLower = 0)
  /-- The left test passed and the candidate's right-axis determinant is zero. -/ | rightZero
      (left : QuadraticAxisElimination.verticalDeterminant parameter box.xLower ≠ 0)
      (zero : QuadraticAxisElimination.verticalDeterminant parameter box.xUpper = 0)
  /-- Both vertical-axis tests passed and the bottom-axis determinant is zero. -/ | bottomZero
      (left : QuadraticAxisElimination.verticalDeterminant parameter box.xLower ≠ 0)
      (right : QuadraticAxisElimination.verticalDeterminant parameter box.xUpper ≠ 0)
      (zero : QuadraticAxisElimination.horizontalDeterminant parameter box.yLower = 0)
  /-- The preceding three tests passed and the top-axis determinant is zero. -/ | topZero
      (left : QuadraticAxisElimination.verticalDeterminant parameter box.xLower ≠ 0)
      (right : QuadraticAxisElimination.verticalDeterminant parameter box.xUpper ≠ 0)
      (bottom : QuadraticAxisElimination.horizontalDeterminant parameter box.yLower ≠ 0)
      (zero : QuadraticAxisElimination.horizontalDeterminant parameter box.yUpper = 0)
  /-- All axis tests passed but the exact retained quadrupled winding differs from four. -/ | windingMiss
      (left : QuadraticAxisElimination.verticalDeterminant parameter box.xLower ≠ 0)
      (right : QuadraticAxisElimination.verticalDeterminant parameter box.xUpper ≠ 0)
      (bottom : QuadraticAxisElimination.horizontalDeterminant parameter box.yLower ≠ 0)
      (top : QuadraticAxisElimination.horizontalDeterminant parameter box.yUpper ≠ 0)
      (winding : Int)
      (winding_eq : winding = Winding.Box.Basic.quadrupledBoxWinding
        (ExactQuadraticOwnerClearance.rootPolynomial parameter) box)
      (miss : winding ≠ 4)

constructive_injectivity Reason

set_option genInjectivity false in
/-- The unsuccessful return-box attempt with its original owners and stopping evidence.

The report retains both failed strict-inclusion tests, the exact candidate box, its axis or winding obstruction, and the
one-query budget. -/
structure Inconclusive where
  /-- The exact candidate enclosure used by the unsuccessful return check. -/ attempt : Attempt first last
  /-- The last owner's initial box is not strictly inside the first owner's box. -/ lastNotInside : ¬
    last.track.initial.box.StrictInterior first.track.initial.box
  /-- The first owner's initial box is not strictly inside the last owner's box. -/ firstNotInside : ¬
    first.track.initial.box.StrictInterior last.track.initial.box
  /-- The retained axis or winding obstruction for this exact candidate enclosure. -/ reason : Reason (parameter :=
    parameter) attempt.box
  /-- The retained finite winding-query budget. -/ windingBudget : Nat := 1
  /-- The retained winding-query budget is exactly one. -/ windingBudget_eq : windingBudget = 1 := by rfl

constructive_injectivity Inconclusive

/-- Count the winding query used by a stopping reason: zero for axis tests and one for a winding miss. -/
@[expose] def Reason.windingQueries {box : Box} : Reason (parameter := parameter) box → Nat
  | .leftZero .. | .rightZero .. | .bottomZero .. | .topZero .. => 0
  | .windingMiss .. => 1

/-- The retained inconclusive check used no more winding queries than its stated budget. -/
theorem Inconclusive.queries_le_budget (report : Inconclusive first last) :
    report.reason.windingQueries ≤ report.windingBudget := by
  rw [report.windingBudget_eq]
  cases report.reason <;> simp only [Reason.windingQueries] <;> decide

open Purelib.Polynomial in
open Purelib.RootIsolation.SquareRoot.Clearance in
set_option genInjectivity false in
/-- A root-return certificate from strict inclusion or one retained common enclosure.

The common-box case keeps the actual winding observation, its value-four proof and the constructed owner with its exact
enclosure identity. -/
inductive Certificate where
  /-- The last owner's box lies strictly inside the first owner's box. -/ | lastInside (inside :
    last.track.initial.box.StrictInterior first.track.initial.box)
  /-- The first owner's box lies strictly inside the last owner's box. -/ | firstInside (inside :
    first.track.initial.box.StrictInterior last.track.initial.box)
  /-- A retained value-four winding observation and common root owner for the exact candidate enclosure. -/ | common
    (attempt : Attempt first last)
      (winding : Int)
      (winding_eq : winding = Winding.Box.Basic.quadrupledBoxWinding
        (ExactQuadraticOwnerClearance.rootPolynomial parameter) attempt.box)
      (winding_four : winding = 4)
      (owner : Owner parameter) (box_eq : owner.track.initial.box = attempt.box)

constructive_injectivity Certificate

open Purelib.Approximation.Gaussian in
/-- Read the certified equivalence of the original final root name with the original initial root name. -/
@[expose] def Certificate.comparison : Certificate first last →
    Equivalence.NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName first.parameterNonzero last)
      (SquareRootTrackEquivalence.ownerRootName first.parameterNonzero first)
  | .lastInside inside =>
      (SquareRootTrackEquivalence.rootEquivalent_of_initial_strict first.parameterNonzero
        first.track last.track inside).symm
  | .firstInside inside =>
      SquareRootTrackEquivalence.rootEquivalent_of_initial_strict first.parameterNonzero
        last.track first.track inside
  | .common attempt _ _ _ owner boxEq =>
      equivalent first last owner
        (by rw [boxEq]; exact attempt.firstInside)
        (by rw [boxEq]; exact attempt.lastInside)

open Purelib.RootIsolation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Check root return with at most one winding query.

The plan first checks strict inclusion in either direction, then the candidate enclosure's four axis determinants, and
finally its winding. Every unsuccessful branch retains the precise attempted data and stopping reason. -/
@[expose] def plan : SquareRoot.Replay.MovingRecenterReplay.Plan (ExactQuadraticOwnerClearance.rootPolynomial parameter)
    (Except (Inconclusive first last) (Certificate first last)) 1 :=
  if lastInside : last.track.initial.box.StrictInterior first.track.initial.box then
    .done (.ok (.lastInside lastInside))
  else if firstInside : first.track.initial.box.StrictInterior last.track.initial.box then
    .done (.ok (.firstInside firstInside))
  else
    let attempt := Attempt.build first last
    if leftZero : QuadraticAxisElimination.verticalDeterminant parameter attempt.box.xLower = 0 then
      .done (.error ⟨attempt, lastInside, firstInside, .leftZero leftZero, 1, rfl⟩)
    else if rightZero : QuadraticAxisElimination.verticalDeterminant parameter attempt.box.xUpper = 0 then
      .done (.error ⟨attempt, lastInside, firstInside, .rightZero leftZero rightZero, 1, rfl⟩)
    else if bottomZero : QuadraticAxisElimination.horizontalDeterminant parameter attempt.box.yLower = 0 then
      .done (.error ⟨attempt, lastInside, firstInside, .bottomZero leftZero rightZero bottomZero, 1, rfl⟩)
    else if topZero : QuadraticAxisElimination.horizontalDeterminant parameter attempt.box.yUpper = 0 then
      .done (.error ⟨attempt, lastInside, firstInside, .topZero leftZero rightZero bottomZero topZero, 1, rfl⟩)
    else
      .query attempt.box fun winding =>
        if four : winding.val = 4 then
          let common := ExactQuadraticOwnerClearance.directOwnerOfBox parameter first.parameterNonzero
            attempt.box attempt.proper leftZero rightZero bottomZero topZero (winding.property.symm.trans four)
          .done (.ok (.common attempt winding.val winding.property four common rfl))
        else .done (.error ⟨attempt, lastInside, firstInside,
          .windingMiss leftZero rightZero bottomZero topZero winding.val winding.property four, 1, rfl⟩)

open Purelib.RootIsolation in
/-- Execute the finite return-box plan and retain either its certificate or inconclusive report. -/
@[expose] def check : Except (Inconclusive first last) (Certificate first last) :=
  SquareRoot.Replay.MovingRecenterReplay.Plan.run (plan first last)

open Purelib.RootIsolation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- The checked replay plan bound to this exact return-box check result and one-query budget. -/
@[expose] def replay : SquareRoot.Replay.MovingRecenterReplay.Plan (ExactQuadraticOwnerClearance.rootPolynomial
  parameter)
    (SquareRoot.Replay.MovingRecenterReplay.Checked (check first last)) 1 :=
  SquareRoot.Replay.MovingRecenterReplay.Plan.checked (plan first last)

/-- The typed return-check result for the exact first and last root owners. -/
@[expose, reducible] def Outcome (first last : Owner parameter) :=
  Except (Inconclusive first last) (Certificate first last)

/-- The retained outcome equals the result of the original two-owner check. -/
@[expose, reducible] def OutcomeIdentity (first last : Owner parameter)
    (retained : Outcome first last) : Prop := retained = check first last

set_option genInjectivity false in
/-- A retained return-check observation with exact input-owner and outcome identities.

Both original owners remain explicit, and the stored result is linked to the same finite checking procedure. -/
structure Observation (first last : Owner parameter) where
  /-- The retained initial input owner. -/ firstOwner : Owner parameter
  /-- The retained initial owner equals the original first input. -/ firstOwner_eq : firstOwner = first
  /-- The retained final input owner. -/ lastOwner : Owner parameter
  /-- The retained final owner equals the original last input. -/ lastOwner_eq : lastOwner = last
  /-- The typed result retained from the original finite return check. -/ outcome : Outcome first last
  /-- The retained result is exactly the outcome of the original two-owner check. -/ outcome_eq : OutcomeIdentity first
    last outcome

constructive_injectivity Observation

/-- Run and retain the exact two-owner return check with its input and outcome identities. -/
@[expose] def observe (first last : Owner parameter) : Observation first last :=
  { firstOwner := first
    firstOwner_eq := rfl
    lastOwner := last
    lastOwner_eq := rfl
    outcome := check first last
    outcome_eq := rfl }

namespace Observation

variable {first last : Owner parameter}

/-- An accepted retained observation identifies the exact successful check result. -/
theorem accepted_readback (observation : Observation first last)
    (certificate : Certificate first last)
    (accepted : observation.outcome = .ok certificate) :
    check first last = .ok certificate :=
  observation.outcome_eq.symm.trans accepted

/-- An inconclusive retained observation identifies the exact unsuccessful check result. -/
theorem inconclusive_readback (observation : Observation first last)
    (failure : Inconclusive first last)
    (reported : observation.outcome = .error failure) :
    check first last = .error failure :=
  observation.outcome_eq.symm.trans reported

end Observation

end Purelib.Riemann.RootContinuation.RootReturnBox
