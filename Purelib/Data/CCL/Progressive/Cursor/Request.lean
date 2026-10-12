module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Step
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Encoding.Parser.State
public import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Progressive.Cursor.Refinement
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Committed
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Chordal.Affine
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Transport
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Data.List.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

namespace Purelib.Data.CCL.Progressive.Cursor.Request

section
public section

/-!
# Persistent finite requests for progressive CCL cursors

The raw arithmetic cursor already extends one finite `List Bool` prefix.  This
module adds the missing accuracy operation: refine the finite enclosure carried
by its current quantitative mode without changing either exposed or buffered
bits.  The refined ball is transported through the exact current projective
chart, giving an arbitrarily small rational squared-chordal cylinder bound.

Everything here is a finite request on an explicit machine.  No stream, limit,
intersection, or completed value is formed.
-/

namespace Machine

section
open Purelib.Data.CCL.Progressive
open Purelib.Data.CCL.Transducer
open Purelib.Data.Rat
open Purelib.Geometry.Projective
/-- Divide the requested squared chordal tolerance by four times the exact retained image-matrix transport coefficient.
-/
@[expose] def cylinderBallTarget (machine : Transducer.Machine) (epsilonSq : Fraction.Rational) :
    Fraction.Rational :=
  epsilonSq /
    (4 * Chordal.Transport.transportCoefficient
      (Cursor.Image.Machine.imageMatrix machine))

/-- A positive squared chordal tolerance gives a positive exact ball-refinement target. -/
theorem cylinderBallTarget_pos
    (machine : Transducer.Machine) {epsilonSq : Fraction.Rational} (positive : 0 < epsilonSq) :
    0 < (Cursor.Request.Machine.cylinderBallTarget machine) epsilonSq := by
  apply Fraction.Order.Field.div_pos_direct positive
  exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Chordal.Transport.transportCoefficient_pos
      (Cursor.Image.Machine.imageMatrix machine) (Cursor.Image.Machine.imageMatrix_det_ne machine))

end

section
open Purelib.Data.CCL.Progressive
open Purelib.Data.CCL.Transducer
open Purelib.Data.Rat
/-- Refine the retained machine at the ball target computed from its exact image matrix and positive squared chordal
tolerance.

The same mode process receives the scaled request. Its image matrix, emitted prefix and pending queue remain unchanged
while the ball accuracy controls projective image separation. -/
@[expose] def refineCylinder
    (machine : Transducer.Machine) (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) :
    Transducer.Machine :=
  (Cursor.Refinement.Machine.refine machine) ((Cursor.Request.Machine.cylinderBallTarget machine) epsilonSq)
    ((Cursor.Request.Machine.cylinderBallTarget_pos machine) positive)

/-- Cylinder refinement preserves the exact retained emitted prefix. -/
@[simp] theorem refineCylinder_emitted
    (machine : Transducer.Machine) (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) :
    ((Cursor.Request.Machine.refineCylinder machine) epsilonSq positive).emitted = machine.emitted := rfl

/-- Cylinder refinement preserves the exact retained committed word. -/
@[simp] theorem refineCylinder_committed
    (machine : Transducer.Machine) (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) :
    Transducer.Machine.committed
        ((Cursor.Request.Machine.refineCylinder machine) epsilonSq positive) =
      Transducer.Machine.committed machine :=
  rfl

end

open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Any two possible values after cylinder refinement have machine images within the requested squared chordal
tolerance.

Their retained ball bounds give a four-radius-squared Euclidean estimate. The unchanged nonsingular image matrix
transports this estimate with the same coefficient used to compute the refinement target. -/
theorem refineCylinder_pair_chordalSq_le
    (machine : Transducer.Machine) (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq)
    {left right : Basic.Canonical}
    (leftPossible : Mode.Semantics.SemanticMode.possible
      ((Cursor.Request.Machine.refineCylinder machine) epsilonSq positive).mode left)
    (rightPossible : Mode.Semantics.SemanticMode.possible
      ((Cursor.Request.Machine.refineCylinder machine) epsilonSq positive).mode right) :
    Chordal.Basic.chordalSq
        ((Cursor.Image.Machine.image ((Cursor.Request.Machine.refineCylinder machine) epsilonSq positive)) left)
        ((Cursor.Image.Machine.image ((Cursor.Request.Machine.refineCylinder machine) epsilonSq positive)) right) ≤
      epsilonSq := by
  let coefficient :=
    Chordal.Transport.transportCoefficient (Cursor.Image.Machine.imageMatrix machine)
  let target := (Cursor.Request.Machine.cylinderBallTarget machine) epsilonSq
  let refined := (Cursor.Request.Machine.refineCylinder machine) epsilonSq positive
  have coefficientPositive : 0 < coefficient :=
    Chordal.Transport.transportCoefficient_pos
      (Cursor.Image.Machine.imageMatrix machine) (Cursor.Image.Machine.imageMatrix_det_ne machine)
  have targetPositive : 0 < target := (Cursor.Request.Machine.cylinderBallTarget_pos machine) positive
  have radiusSmall : (Cursor.Refinement.Mode.ball refined.mode).radiusSq < target := by
    exact Cursor.Refinement.Mode.refine_ball_radiusSq_lt machine.mode target targetPositive
  have leftInside := Cursor.Refinement.Mode.possible_inside refined.mode leftPossible
  have rightInside := Cursor.Refinement.Mode.possible_inside refined.mode rightPossible
  have centerRight :
      Gaussian.Norm.Basic.normSq ((Cursor.Refinement.Mode.ball refined.mode).center - right) =
        Gaussian.Norm.Basic.normSq (right - (Cursor.Refinement.Mode.ball refined.mode).center) := by
    have negated : (Cursor.Refinement.Mode.ball refined.mode).center - right =
        -(right - (Cursor.Refinement.Mode.ball refined.mode).center) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im] <;>
        ring1
    rw [negated, Norm.Basic.normSq_neg]
  have pairDistance : Gaussian.Norm.Basic.normSq (left - right) ≤
      4 * (Cursor.Refinement.Mode.ball refined.mode).radiusSq := by
    calc
      Gaussian.Norm.Basic.normSq (left - right) ≤
          2 * (Gaussian.Norm.Basic.normSq (left - (Cursor.Refinement.Mode.ball refined.mode).center) +
            Gaussian.Norm.Basic.normSq ((Cursor.Refinement.Mode.ball refined.mode).center - right)) :=
        Norm.Bounds.normSq_sub_le_via left (Cursor.Refinement.Mode.ball refined.mode).center right
      _ = 2 * (Gaussian.Norm.Basic.normSq (left - (Cursor.Refinement.Mode.ball refined.mode).center) +
            Gaussian.Norm.Basic.normSq (right - (Cursor.Refinement.Mode.ball refined.mode).center)) := by
        rw [centerRight]
      _ ≤ 2 * ((Cursor.Refinement.Mode.ball refined.mode).radiusSq +
            (Cursor.Refinement.Mode.ball refined.mode).radiusSq) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct leftInside rightInside) (by decide)
      _ = 4 * (Cursor.Refinement.Mode.ball refined.mode).radiusSq := by ring1
  have scaledRadius :
      (Cursor.Refinement.Mode.ball refined.mode).radiusSq * (4 * coefficient) < epsilonSq := by
    exact (Fraction.Order.Field.lt_div_iff_pos
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        coefficientPositive)).1 radiusSmall
  have transported :=
    Chordal.Transport.chordalSq_act_le_transportCoefficient
      (Cursor.Image.Machine.imageMatrix machine) (Cursor.Image.Machine.imageMatrix_det_ne machine)
      (Line.Proj.affine left) (Line.Proj.affine right)
      (Line.Gaussian.Proj.affine_hasNonzeroCoordinate left)
      (Line.Gaussian.Proj.affine_hasNonzeroCoordinate right)
  change Chordal.Basic.chordalSq
      ((Cursor.Image.Machine.image refined) left) ((Cursor.Image.Machine.image refined) right) ≤ epsilonSq
  apply le_of_lt
  calc
    Chordal.Basic.chordalSq ((Cursor.Image.Machine.image refined) left)
        ((Cursor.Image.Machine.image refined) right) =
        Chordal.Basic.chordalSq
          (Line.Matrix.act (Cursor.Image.Machine.imageMatrix machine) (Line.Proj.affine left))
          (Line.Matrix.act (Cursor.Image.Machine.imageMatrix machine) (Line.Proj.affine right)) := by
      rw [(Cursor.Image.Machine.image_eq_act_imageMatrix refined),
        (Cursor.Image.Machine.image_eq_act_imageMatrix refined)]
      dsimp only [refined, Cursor.Request.Machine.refineCylinder]
      rewrite [Cursor.Image.Machine.refine_imageMatrix]
      exact Eq.refl _
    _ ≤ coefficient *
        Chordal.Basic.chordalSq
          (Line.Proj.affine left) (Line.Proj.affine right) := transported
    _ ≤ coefficient * Gaussian.Norm.Basic.normSq (left - right) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Chordal.Affine.chordalSq_affine_le_normSq left right)
        coefficientPositive.le
    _ ≤ coefficient * (4 * (Cursor.Refinement.Mode.ball refined.mode).radiusSq) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        pairDistance coefficientPositive.le
    _ < epsilonSq := by
      calc
        coefficient * (4 * (Cursor.Refinement.Mode.ball refined.mode).radiusSq) =
            (Cursor.Refinement.Mode.ball refined.mode).radiusSq * (4 * coefficient) := by ring1
        _ < epsilonSq := scaledRadius

end Machine

namespace ExactCursor

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Refining the retained machine preserves its exact cursor certificate relative to the same original process state. -/
theorem refine
    {origin : Approximation.Gaussian.Process} {originState : origin.State} {machine : Transducer.Machine}
    (cursor : Machine.Semantics.Basic.SourcePersistentProgressiveExactCursorAlias origin originState machine)
    (target : Fraction.Rational) (positive : 0 < target) :
    Machine.Semantics.Basic.SourcePersistentProgressiveExactCursorAlias origin originState
      ((Cursor.Refinement.Machine.refine machine) target positive) := by
  refine
    { grammar := (Cursor.Refinement.Machine.refine_grammar machine) target positive cursor.grammar
      exact := ?_ }
  intro tail possible
  change Mode.Semantics.SemanticMode.possible
    (Cursor.Refinement.Mode.refine machine.mode target positive) tail at possible
  have previousPossible :=
    Cursor.Refinement.Mode.refine_possible machine.mode target positive possible
  change ∃ value : Basic.Canonical,
    origin.Possible originState value ∧
      (Line.Matrix.act
        (Parser.State.parse
          (Transducer.Machine.committed
            machine)).matrix
        (Mode.Semantics.SemanticMode.parserTail
          (Cursor.Refinement.Mode.refine machine.mode target positive) tail)).Equivalent
            (Line.Proj.affine value)
  rw [Cursor.Refinement.Mode.refine_parserTail]
  exact cursor.exact previousPossible

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- Cylinder refinement preserves the exact cursor certificate for the same original process and dependent state. -/
theorem refineCylinder
    {origin : Approximation.Gaussian.Process} {originState : origin.State} {machine : Transducer.Machine}
    (cursor : Machine.Semantics.Basic.SourcePersistentProgressiveExactCursorAlias origin originState machine)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) :
    Machine.Semantics.Basic.SourcePersistentProgressiveExactCursorAlias origin originState
      ((Cursor.Request.Machine.refineCylinder machine) epsilonSq positive) :=
  (Cursor.Request.ExactCursor.refine cursor) ((Cursor.Request.Machine.cylinderBallTarget machine) epsilonSq)
    ((Cursor.Request.Machine.cylinderBallTarget_pos machine) positive)

end ExactCursor

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
set_option genInjectivity false in
/-- Retain a machine with its exact cursor certificate for the original process and dependent state.

The certificate links every possible current tail to an original-state witness through the same committed parser image
and preserves the machine grammar invariant. -/
structure State (origin : Approximation.Gaussian.Process) (originState : origin.State) where
  /-- The exact current machine, including its mode, emitted prefix and pending queue. -/ machine :
    Transducer.Machine
  /-- The exact grammar and projective representation certificate for this machine relative to the same original process
    state. -/ exact : Machine.Semantics.Basic.SourcePersistentProgressiveExactCursorAlias origin originState machine

constructive_injectivity State

namespace State

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
/-- Construct the exact initial cursor for the supplied original process and dependent state. -/
@[expose] def initial (origin : Approximation.Gaussian.Process) (originState : origin.State) :
    State origin originState :=
  { machine := Transducer.Machine.initial origin originState
    exact := Machine.Semantics.Basic.ExactCursor.initial origin originState }

section
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Progressive
open Purelib.Data.CCL.Transducer
open Purelib.Data.Rat
/-- Advance the retained cursor by the requested bit count, then refine that exact advanced machine to the positive
chordal tolerance.

Keep the same origin process and state. The new certificate composes exact finite advancement with cylinder refinement;
the final machine retains the advanced emitted word and queue. -/
@[expose] def request
    {origin : Approximation.Gaussian.Process} {originState : origin.State}
    (cursor : State origin originState)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    State origin originState :=
  let advanced := Machine.Advance.advance
    cursor.machine count
  { machine := Cursor.Request.Machine.refineCylinder advanced epsilonSq positive
    exact := Cursor.Request.ExactCursor.refineCylinder ((Machine.Semantics.Basic.ExactCursor.advance cursor.exact)
      count)
      epsilonSq positive }

/-- A cursor request retains the original emitted word as a prefix of the resulting machine's emitted word. -/
theorem request_extends
    {origin : Approximation.Gaussian.Process} {originState : origin.State}
    (cursor : State origin originState)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    cursor.machine.emitted.IsPrefix
      ((request cursor) epsilonSq positive count).machine.emitted := by
  change cursor.machine.emitted.IsPrefix
    (Machine.Advance.advance cursor.machine count).emitted
  exact
    Machine.Advance.advance_extends cursor.machine count

/-- A cursor request increases the emitted length by exactly its requested bit count. -/
theorem request_length
    {origin : Approximation.Gaussian.Process} {originState : origin.State}
    (cursor : State origin originState)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    ((request cursor) epsilonSq positive count).machine.emitted.length =
      cursor.machine.emitted.length + count := by
  change (Machine.Advance.advance cursor.machine count).emitted.length =
    cursor.machine.emitted.length + count
  exact
    Machine.Advance.advance_length cursor.machine count

end

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
/-- Any two possible tails after a cursor request have retained machine images within its squared chordal tolerance. -/
theorem request_pair_chordalSq_le
    {origin : Approximation.Gaussian.Process} {originState : origin.State}
    (cursor : State origin originState)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat)
    {left right : Basic.Canonical}
    (leftPossible : Mode.Semantics.SemanticMode.possible
      ((request cursor) epsilonSq positive count).machine.mode left)
    (rightPossible : Mode.Semantics.SemanticMode.possible
      ((request cursor) epsilonSq positive count).machine.mode right) :
    Chordal.Basic.chordalSq
        ((Cursor.Image.Machine.image ((request cursor) epsilonSq positive count).machine) left)
        ((Cursor.Image.Machine.image ((request cursor) epsilonSq positive count).machine) right) ≤
      epsilonSq := by
  exact Cursor.Request.Machine.refineCylinder_pair_chordalSq_le
    (Machine.Advance.advance cursor.machine count)
    epsilonSq positive leftPossible rightPossible

end State

end

section

public section

/-!
# Persistent output after retryable division preflight

Readiness returns an ordinary coherent name unchanged.  Consequently the
existing persistent cursor supplies exact raw-parser semantics, prefix
extension, and finite request lengths without any weakened partial variant.
-/

end

end
end

end Purelib.Data.CCL.Progressive.Cursor.Request
