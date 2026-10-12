module

import Purelib.Data.CCL.Encoding.Parser.Constraint
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
public import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.All
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Homography.Injectivity
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Geometry.Projective.Homography.Composition

/-!
# Constraints and affine representations of retained parser states

The state predicates read the original constraint history, active phase and
cached decoder matrix. An affine representation retains its input and tail
alongside the denominator witness and those exact state constraints.
-/

section

namespace Purelib.Data.CCL.Encoding.Parser.State

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
/-- Require every retained history constraint and the current phase condition at the same Gaussian tail.

The history and active phase are evaluated against the same supplied tail. The
proposition retains the original constraint list and phase of the parser state.
-/
@[expose] public def Holds (state : State) (tail : Basic.Canonical) : Prop :=
  (∀ constraint ∈ state.history, constraint.Holds tail) ∧
    Parser.Semantics.Basic.activeHolds state.phase tail

/-- Check all retained history constraints and the active phase at the supplied Gaussian tail.

The original ordered history is checked with its existing decision procedures,
then combined with the decision for the retained active phase. The Boolean check
uses the same tail for both parts.
-/
@[expose] public def holdsBool (state : State) (tail : Basic.Canonical) : Bool :=
  (state.history.all fun constraint => decide (constraint.Holds tail)) &&
    decide (Parser.Semantics.Basic.activeHolds state.phase tail)

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
/-- The retained Boolean state check succeeds exactly when its history and active-phase proposition holds.

Every constraint keeps its occurrence in the retained history and is checked at
the same supplied tail as the active phase. Direct Boolean cases and decision
certificates establish both parts without rewriting proposition equivalences. -/
public theorem holdsBool_eq_true (state : State) (tail : Basic.Canonical) :
    state.holdsBool tail = true ↔ state.Holds tail := by
  constructor
  · intro accepted
    change ((state.history.all fun constraint => decide (constraint.Holds tail)) &&
      decide (Parser.Semantics.Basic.activeHolds state.phase tail)) = true at accepted
    have passed :
        (state.history.all fun constraint => decide (constraint.Holds tail)) = true ∧
          decide (Parser.Semantics.Basic.activeHolds state.phase tail) = true := by
      generalize (state.history.all fun constraint => decide (constraint.Holds tail)) =
        historyResult at accepted ⊢
      generalize decide (Parser.Semantics.Basic.activeHolds state.phase tail) =
        activeResult at accepted ⊢
      cases historyResult <;> cases activeResult <;> cases accepted
      exact ⟨Eq.refl true, Eq.refl true⟩
    have historyAccepted := All.all_eq_true.mp passed.1
    exact ⟨fun constraint member =>
      of_decide_eq_true (historyAccepted constraint member),
      of_decide_eq_true passed.2⟩
  · rintro ⟨historyHolds, activeHolds⟩
    have historyAccepted :
        (state.history.all fun constraint => decide (constraint.Holds tail)) = true :=
      All.all_eq_true.mpr (fun constraint member =>
        decide_eq_true (historyHolds constraint member))
    have activeAccepted : decide (Parser.Semantics.Basic.activeHolds state.phase tail) = true :=
      decide_eq_true activeHolds
    change ((state.history.all fun constraint => decide (constraint.Holds tail)) &&
      decide (Parser.Semantics.Basic.activeHolds state.phase tail)) = true
    rewrite [historyAccepted, activeAccepted]
    exact Eq.refl true

open Purelib.Data.CCL.Encoding in
open Purelib.Geometry.Projective in
/-- Act on the projective point at infinity by the exact retained parser matrix.

The truncation uses the original projective action and infinity point. It reads
the matrix already stored in the parser state without reconstructing a decoder.
-/
@[expose] public def truncation (state : State) : Line.GaussianLine :=
  Line.Matrix.act state.matrix (Line.Proj.omega : Line.GaussianLine)

end Purelib.Data.CCL.Encoding.Parser.State
end

namespace Purelib.Data.CCL.Encoding.Parser.Semantics.State

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Require the input to equal the retained matrix homography of the tail with nonzero denominator and all state
constraints.

The representation keeps the same input, tail, matrix, history and active phase. The denominator witness ensures the
exact affine homography is defined at that retained tail. -/
@[expose] public def Represents (state : State) (input tail : Basic.Canonical) : Prop :=
  Homography.Basic.denominator state.matrix tail ≠ 0 ∧
    input = Homography.Basic.homographic state.matrix tail ∧ state.Holds tail

open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
namespace Represents

/-- A nonsingular parser matrix makes the tail of a retained input representation unique.

Both representations retain the same state and input with nonzero affine
denominators. Injectivity of that original matrix therefore identifies their
tails; the history and active-phase conditions remain part of each representation.
-/
public theorem tail_unique
    {state : State} {input left right : Basic.Canonical}
    (determinant : Matrix2.Matrix2.determinant state.matrix ≠ 0)
    (leftRepresents : Parser.Semantics.State.Represents state input left)
    (rightRepresents : Parser.Semantics.State.Represents state input right) : left = right := by
  apply Homography.Injectivity.homographic_injective state.matrix determinant leftRepresents.1
    rightRepresents.1
  exact leftRepresents.2.1.symm.trans rightRepresents.2.1

end Represents
/-- The initial parser state represents every Gaussian input with that same value as its exact tail.

The retained identity matrix fixes the input and has unit denominator. Its empty
history and initial phase impose no additional constraint on that exact tail. -/
public theorem initialState_represents (input : Basic.Canonical) :
    Parser.Semantics.State.Represents Parser.State.initialState input input := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Homography.Basic.denominator, Parser.State.initialState, Matrix2.identityMatrix,
      Basic.zero_mul,
      Basic.zero_add]
    decide
  · change input = ((1 : Basic.Canonical) * input + 0) *
      ((0 : Basic.Canonical) * input + 1)⁻¹
    rw [Basic.one_mul,
      Basic.add_zero,
      Basic.zero_mul,
      Basic.zero_add, Field.inv_eq,
      Field.inv_one_direct,
      Basic.mul_one]
  · change (∀ constraint ∈ ([] : List Constraint),
        constraint.Holds input) ∧ True
    constructor
    · intro _constraint member
      nomatch member
    · exact True.intro
end Purelib.Data.CCL.Encoding.Parser.Semantics.State
