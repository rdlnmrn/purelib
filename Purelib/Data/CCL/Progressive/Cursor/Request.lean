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

open Purelib.Data.CCL.Transducer.Mode.Semantics
open Purelib.Data.Rat.Fraction.Order

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
@[expose] def cylinderBallTarget (machine : Machine) (epsilonSq : Fraction.Rational) :
    Fraction.Rational :=
  epsilonSq /
    (4 * Chordal.Transport.transportCoefficient
      (Image.Machine.imageMatrix machine))

/-- A positive squared chordal tolerance gives a positive exact ball-refinement target. -/
theorem cylinderBallTarget_pos
    (machine : Machine) {epsilonSq : Fraction.Rational} (positive : 0 < epsilonSq) :
    0 < (cylinderBallTarget machine) epsilonSq := by
  apply Field.div_pos_direct positive
  exact Arithmetic.mul_pos_direct (by decide)
    (Chordal.Transport.transportCoefficient_pos
      (Image.Machine.imageMatrix machine) (Image.Machine.imageMatrix_det_ne machine))

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
    (machine : Machine) (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) :
    Machine :=
  (Refinement.Machine.refine machine) ((cylinderBallTarget machine) epsilonSq)
    ((cylinderBallTarget_pos machine) positive)

/-- Cylinder refinement preserves the exact retained emitted prefix. -/
@[simp] theorem refineCylinder_emitted
    (machine : Machine) (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) :
    ((refineCylinder machine) epsilonSq positive).emitted = machine.emitted := rfl

/-- Cylinder refinement preserves the exact retained committed word. -/
@[simp] theorem refineCylinder_committed
    (machine : Machine) (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) :
    Machine.committed
        ((refineCylinder machine) epsilonSq positive) =
      Machine.committed machine :=
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
    (machine : Machine) (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq)
    {left right : Basic.Canonical}
    (leftPossible : SemanticMode.possible
      ((refineCylinder machine) epsilonSq positive).mode left)
    (rightPossible : SemanticMode.possible
      ((refineCylinder machine) epsilonSq positive).mode right) :
    Chordal.Basic.chordalSq
        ((Image.Machine.image ((refineCylinder machine) epsilonSq positive)) left)
        ((Image.Machine.image ((refineCylinder machine) epsilonSq positive)) right) ≤
      epsilonSq := by
  let coefficient :=
    Chordal.Transport.transportCoefficient (Image.Machine.imageMatrix machine)
  let target := (cylinderBallTarget machine) epsilonSq
  let refined := (refineCylinder machine) epsilonSq positive
  have coefficientPositive : 0 < coefficient :=
    Chordal.Transport.transportCoefficient_pos
      (Image.Machine.imageMatrix machine) (Image.Machine.imageMatrix_det_ne machine)
  have targetPositive : 0 < target := (cylinderBallTarget_pos machine) positive
  have radiusSmall : (Refinement.Mode.ball refined.mode).radiusSq < target := by
    exact Refinement.Mode.refine_ball_radiusSq_lt machine.mode target targetPositive
  have leftInside := Refinement.Mode.possible_inside refined.mode leftPossible
  have rightInside := Refinement.Mode.possible_inside refined.mode rightPossible
  have centerRight :
      Norm.Basic.normSq ((Refinement.Mode.ball refined.mode).center - right) =
        Norm.Basic.normSq (right - (Refinement.Mode.ball refined.mode).center) := by
    have negated : (Refinement.Mode.ball refined.mode).center - right =
        -(right - (Refinement.Mode.ball refined.mode).center) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im] <;>
        ring1
    rw [negated, Norm.Basic.normSq_neg]
  have pairDistance : Norm.Basic.normSq (left - right) ≤
      4 * (Refinement.Mode.ball refined.mode).radiusSq := by
    calc
      Norm.Basic.normSq (left - right) ≤
          2 * (Norm.Basic.normSq (left - (Refinement.Mode.ball refined.mode).center) +
            Norm.Basic.normSq ((Refinement.Mode.ball refined.mode).center - right)) :=
        Norm.Bounds.normSq_sub_le_via left (Refinement.Mode.ball refined.mode).center right
      _ = 2 * (Norm.Basic.normSq (left - (Refinement.Mode.ball refined.mode).center) +
            Norm.Basic.normSq (right - (Refinement.Mode.ball refined.mode).center)) := by
        rw [centerRight]
      _ ≤ 2 * ((Refinement.Mode.ball refined.mode).radiusSq +
            (Refinement.Mode.ball refined.mode).radiusSq) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct leftInside rightInside) (by decide)
      _ = 4 * (Refinement.Mode.ball refined.mode).radiusSq := by ring1
  have scaledRadius :
      (Refinement.Mode.ball refined.mode).radiusSq * (4 * coefficient) < epsilonSq := by
    exact (Field.lt_div_iff_pos
      (Arithmetic.mul_pos_direct (by decide)
        coefficientPositive)).1 radiusSmall
  have transported :=
    Chordal.Transport.chordalSq_act_le_transportCoefficient
      (Image.Machine.imageMatrix machine) (Image.Machine.imageMatrix_det_ne machine)
      (Line.Proj.affine left) (Line.Proj.affine right)
      (Line.Gaussian.Proj.affine_hasNonzeroCoordinate left)
      (Line.Gaussian.Proj.affine_hasNonzeroCoordinate right)
  change Chordal.Basic.chordalSq
      ((Image.Machine.image refined) left) ((Image.Machine.image refined) right) ≤ epsilonSq
  apply le_of_lt
  calc
    Chordal.Basic.chordalSq ((Image.Machine.image refined) left)
        ((Image.Machine.image refined) right) =
        Chordal.Basic.chordalSq
          (Line.Matrix.act (Image.Machine.imageMatrix machine) (Line.Proj.affine left))
          (Line.Matrix.act (Image.Machine.imageMatrix machine) (Line.Proj.affine right)) := by
      rw [(Image.Machine.image_eq_act_imageMatrix refined),
        (Image.Machine.image_eq_act_imageMatrix refined)]
      dsimp only [refined, refineCylinder]
      rewrite [Image.Machine.refine_imageMatrix]
      exact Eq.refl _
    _ ≤ coefficient *
        Chordal.Basic.chordalSq
          (Line.Proj.affine left) (Line.Proj.affine right) := transported
    _ ≤ coefficient * Norm.Basic.normSq (left - right) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Chordal.Affine.chordalSq_affine_le_normSq left right)
        coefficientPositive.le
    _ ≤ coefficient * (4 * (Refinement.Mode.ball refined.mode).radiusSq) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        pairDistance coefficientPositive.le
    _ < epsilonSq := by
      calc
        coefficient * (4 * (Refinement.Mode.ball refined.mode).radiusSq) =
            (Refinement.Mode.ball refined.mode).radiusSq * (4 * coefficient) := by ring1
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
    {origin : Process} {originState : origin.State} {machine : Machine}
    (cursor : Machine.Semantics.Basic.SourcePersistentProgressiveExactCursorAlias origin originState machine)
    (target : Fraction.Rational) (positive : 0 < target) :
    Machine.Semantics.Basic.SourcePersistentProgressiveExactCursorAlias origin originState
      ((Refinement.Machine.refine machine) target positive) := by
  refine
    { grammar := (Refinement.Machine.refine_grammar machine) target positive cursor.grammar
      exact := ?_ }
  intro tail possible
  change SemanticMode.possible
    (Refinement.Mode.refine machine.mode target positive) tail at possible
  have previousPossible :=
    Refinement.Mode.refine_possible machine.mode target positive possible
  change ∃ value : Basic.Canonical,
    origin.Possible originState value ∧
      (Line.Matrix.act
        (Parser.State.parse
          (Machine.committed
            machine)).matrix
        (SemanticMode.parserTail
          (Refinement.Mode.refine machine.mode target positive) tail)).Equivalent
            (Line.Proj.affine value)
  rw [Refinement.Mode.refine_parserTail]
  exact cursor.exact previousPossible

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
/-- Cylinder refinement preserves the exact cursor certificate for the same original process and dependent state. -/
theorem refineCylinder
    {origin : Process} {originState : origin.State} {machine : Machine}
    (cursor : Machine.Semantics.Basic.SourcePersistentProgressiveExactCursorAlias origin originState machine)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) :
    Machine.Semantics.Basic.SourcePersistentProgressiveExactCursorAlias origin originState
      ((Machine.refineCylinder machine) epsilonSq positive) :=
  (refine cursor) ((Machine.cylinderBallTarget machine) epsilonSq)
    ((Machine.cylinderBallTarget_pos machine) positive)

end ExactCursor

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
set_option genInjectivity false in
/-- Retain a machine with its exact cursor certificate for the original process and dependent state.

The certificate links every possible current tail to an original-state witness through the same committed parser image
and preserves the machine grammar invariant. -/
structure State (origin : Process) (originState : origin.State) where
  /-- The exact current machine, including its mode, emitted prefix and pending queue. -/ machine :
    Machine
  /-- The exact grammar and projective representation certificate for this machine relative to the same original process
    state. -/ exact : Machine.Semantics.Basic.SourcePersistentProgressiveExactCursorAlias origin originState machine

constructive_injectivity State

namespace State

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Progressive in
open Purelib.Data.CCL.Transducer in
/-- Construct the exact initial cursor for the supplied original process and dependent state. -/
@[expose] def initial (origin : Process) (originState : origin.State) :
    State origin originState :=
  { machine := Machine.initial origin originState
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
    {origin : Process} {originState : origin.State}
    (cursor : State origin originState)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat) :
    State origin originState :=
  let advanced := Machine.Advance.advance
    cursor.machine count
  { machine := Machine.refineCylinder advanced epsilonSq positive
    exact := ExactCursor.refineCylinder ((Machine.Semantics.Basic.ExactCursor.advance cursor.exact)
      count)
      epsilonSq positive }

/-- Assemble the original persistent cursor result from its exact already returned request machine.

The supplied machine is retained as executable data. Its original cursor
certificate is transported through the complete machine identity, so no bit
advance, refinement or source observation is repeated by this constructor.
-/
def ofRequestMachine {origin : Process} {originState : origin.State}
    (cursor : State origin originState) (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat)
    (machine : Transducer.Machine) (same : machine = (cursor.request epsilonSq positive count).machine) :
    { next : State origin originState // next = cursor.request epsilonSq positive count } :=
  let next : State origin originState :=
    ⟨machine, same.symm ▸ (cursor.request epsilonSq positive count).exact⟩
  ⟨next, by cases same; rfl⟩

/-- A cursor request retains the original emitted word as a prefix of the resulting machine's emitted word. -/
theorem request_extends
    {origin : Process} {originState : origin.State}
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
    {origin : Process} {originState : origin.State}
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
    {origin : Process} {originState : origin.State}
    (cursor : State origin originState)
    (epsilonSq : Fraction.Rational) (positive : 0 < epsilonSq) (count : Nat)
    {left right : Basic.Canonical}
    (leftPossible : SemanticMode.possible
      ((request cursor) epsilonSq positive count).machine.mode left)
    (rightPossible : SemanticMode.possible
      ((request cursor) epsilonSq positive count).machine.mode right) :
    Chordal.Basic.chordalSq
        ((Image.Machine.image ((request cursor) epsilonSq positive count).machine) left)
        ((Image.Machine.image ((request cursor) epsilonSq positive count).machine) right) ≤
      epsilonSq := by
  exact Machine.refineCylinder_pair_chordalSq_le
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

public section

namespace Purelib.Data.CCL.Progressive.Cursor.Image.Machine.Frame

open Purelib.Data.CCL
open Purelib.Data.CCL.Progressive
open Purelib.Data.CCL.Transducer
open Purelib.Data.Rat
open Purelib.Geometry.Projective

/-- Compute the original cylinder ball target from the actual retained image matrix.

The supplied squared chordal tolerance is divided by the same exact transport
coefficient as the original machine request. The committed word is not parsed
again to recover a matrix that is already cached in this frame.
-/
@[expose] def cylinderBallTarget {machine : Machine} (frame : Frame machine) (epsilonSq : Fraction.Rational) :
    Fraction.Rational :=
  epsilonSq / (4 * Chordal.Transport.transportCoefficient frame.matrix)

/-- The cached-frame target equals the original machine's complete exact request target. -/
theorem cylinderBallTarget_eq {machine : Machine} (frame : Frame machine) (epsilonSq : Fraction.Rational) :
    frame.cylinderBallTarget epsilonSq = Cursor.Request.Machine.cylinderBallTarget machine epsilonSq :=
  congrArg (fun matrix => epsilonSq / (4 * Chordal.Transport.transportCoefficient matrix)) frame.matrixEq

/-- A positive squared chordal tolerance gives a positive target using the same retained nonsingular frame. -/
theorem cylinderBallTarget_pos {machine : Machine} (frame : Frame machine)
    {epsilonSq : Fraction.Rational} (positive : 0 < epsilonSq) : 0 < frame.cylinderBallTarget epsilonSq :=
  Fraction.Order.Field.div_pos_direct positive
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Chordal.Transport.transportCoefficient_pos frame.matrix frame.determinantNonzero))

end Purelib.Data.CCL.Progressive.Cursor.Image.Machine.Frame

end
