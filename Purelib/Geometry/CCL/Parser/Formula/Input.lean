module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.CCL.Encoding.Parser.Inverse
import Purelib.Data.CCL.Encoding.Parser.Next
import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
import Purelib.Data.CCL.Encoding.Parser.Semantics.State
import Purelib.Data.CCL.Encoding.Parser.State
public import Purelib.Geometry.CCL.Parser.Formula.Advance
import Purelib.Geometry.Projective.Hermitian.Formula.Pullback
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude
import Purelib.Geometry.Projective.Hermitian.Formula.Basic

public section

open Purelib

open Purelib.Data.CCL.Encoding

open Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.CCL.Encoding.Parser.Semantics

open Purelib.Geometry.CCL.Parser

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Formula

open Purelib.LinearAlgebra.Coordinates2.Matrix

/-!
# Finite Hermitian formulas for one raw CCL bit

Before a completed sector, the proposed child is just the next parser-state
formula at the unchanged affine tail.  On the third sector bit, the formula
checks the selected completed block and excludes its zero residual.  The
result is exactly the constructive one-bit semantic decision.
-/

namespace Purelib.Geometry.CCL.Parser.Formula

/-- Proposed child formula expressed in the original input coordinate by pulling it back through the explicit adjugate
chart. -/
@[expose] def inputAdvanceFormula (state : Data.CCL.Encoding.Parser.State)
  (bit : Bool) :
  Formula.BoundaryFormula :=
  (Formula.advanceFormula state bit).pullback
    (BoundaryAdjugate.adjugate state.matrix)

/-- History-free child formula in the original input coordinate. -/
@[expose] def inputIncrementalAdvanceFormula (state :
  Data.CCL.Encoding.Parser.State) (bit :
  Bool) : Formula.BoundaryFormula :=
  (Formula.incrementalAdvanceFormula state bit).pullback
    (BoundaryAdjugate.adjugate state.matrix)

/-- The input-coordinate formula expresses next-bit admissibility at the inverse homographic tail.

The adjugate denominator must be nonzero at the supplied input. -/
theorem inputAdvanceFormula_iff
    (state : Data.CCL.Encoding.Parser.State) (bit : Bool) (input : Data.Gaussian.Basic.Canonical)
    (inverseDenominator : Homography.Basic.denominator
      (BoundaryAdjugate.adjugate state.matrix) input ≠ 0) :
    (inputAdvanceFormula state bit).Holds input ↔
      Next.CanAdvanceAt state bit
        (Homography.Basic.homographic (BoundaryAdjugate.adjugate state.matrix)
          input) := by
  exact (BoundaryFormula.pullback_iff
    (BoundaryAdjugate.adjugate state.matrix)
    (Formula.advanceFormula state bit) input inverseDenominator).trans
    (Formula.advanceFormula_iff _ _ _)

/-- At a represented state, the original-coordinate child formula is exactly semantic possibility of that bit. -/
theorem inputAdvanceFormula_canStep_iff
    (state : Data.CCL.Encoding.Parser.State) (input tail : Data.Gaussian.Basic.Canonical)
    (determinantNonzero :
      BoundaryAdjugate.determinant state.matrix ≠ 0)
    (represented : State.Represents state input tail)
    (bit : Bool) :
    (inputAdvanceFormula state bit).Holds input ↔
      Prefix.CanStep state input bit := by
  have inverseDenominator := Parser.inverseDenominator_of_represents state input tail
    determinantNonzero represented
  have advance := inputAdvanceFormula_iff state bit input inverseDenominator
  rewrite [Parser.inverseTail_eq state input tail determinantNonzero represented] at advance
  exact advance.trans (Next.canStep_iff_canAdvanceAt state input tail determinantNonzero
    represented bit).symm

/-- At a represented state, the history-free input formula is exactly semantic possibility of the same next bit.

The retained current representation supplies all earlier history and active
constraints. Pullback through the original inverse chart therefore leaves
only the newly introduced child conditions, with the same terminal residual
and half-open boundary tests as the complete local decision.
-/
theorem inputIncrementalAdvanceFormula_canStep_iff
    (state : Data.CCL.Encoding.Parser.State) (input tail : Data.Gaussian.Basic.Canonical)
    (determinantNonzero : BoundaryAdjugate.determinant state.matrix ≠ 0)
    (represented : State.Represents state input tail) (bit : Bool) :
    (inputIncrementalAdvanceFormula state bit).Holds input ↔ Prefix.CanStep state input bit := by
  have inverseDenominator := Parser.inverseDenominator_of_represents state input tail
    determinantNonzero represented
  have pulled := BoundaryFormula.pullback_iff (BoundaryAdjugate.adjugate state.matrix)
    (incrementalAdvanceFormula state bit) input inverseDenominator
  rewrite [Parser.inverseTail_eq state input tail determinantNonzero represented] at pulled
  have current := (stateFormula_iff state tail).mpr represented.2.2
  have incremental : (incrementalAdvanceFormula state bit).Holds tail ↔
      (advanceFormula state bit).Holds tail :=
    ⟨advanceFormula_holds_of_current_incremental state bit tail current,
      incrementalAdvanceFormula_holds_of_advance state bit tail⟩
  exact pulled.trans (incremental.trans ((advanceFormula_iff state bit tail).trans
    (Next.canStep_iff_canAdvanceAt state input tail determinantNonzero represented bit).symm))

/-- The two input-coordinate child regions are disjoint at every represented rational input. -/
theorem inputAdvanceFormula_unique
    (state : Data.CCL.Encoding.Parser.State) (input tail : Data.Gaussian.Basic.Canonical)
    (determinantNonzero :
      BoundaryAdjugate.determinant state.matrix ≠ 0)
    (represented : State.Represents state input tail)
    {left right : Bool}
    (leftHolds : (inputAdvanceFormula state left).Holds input)
    (rightHolds : (inputAdvanceFormula state right).Holds input) :
    left = right := by
  apply Prefix.canStep_unique determinantNonzero
  · exact (inputAdvanceFormula_canStep_iff state input tail
      determinantNonzero represented left).1 leftHolds
  · exact (inputAdvanceFormula_canStep_iff state input tail
      determinantNonzero represented right).1 rightHolds

set_option genInjectivity false in
/-- Formula-facing result of the total local semantic decision. -/
inductive Decision (state : Data.CCL.Encoding.Parser.State) (input before :
  Data.Gaussian.Basic.Canonical) where
  /-- Neither proposed bit satisfies the affine next-step formula. -/ | terminal
      (none : ∀ bit, ¬(Formula.advanceFormula state bit).Holds before)
  /-- A displayed bit satisfies the affine next-step formula and every other satisfying bit equals it. -/ | next (bit :
    Bool) (holds : (Formula.advanceFormula state bit).Holds before)
      (unique : ∀ other, (Formula.advanceFormula state other).Holds before →
        other = bit)

constructive_injectivity Decision

/-- Evaluate the two finite formulas and return their unique bit or the affine-terminal outcome. -/
@[expose] def decide
    (state : Data.CCL.Encoding.Parser.State) (input before : Data.Gaussian.Basic.Canonical)
    (determinantNonzero :
      Matrix2.determinant state.matrix ≠ 0)
    (represented : State.Represents state input before) :
    Decision state input before := by
  cases Next.decideLocal state input before determinantNonzero represented with
  | terminal none =>
      exact .terminal (by
        intro bit holds
        apply none bit
        apply (Next.canStep_iff_canAdvanceAt state input before determinantNonzero
          represented bit).2
        exact (Formula.advanceFormula_iff state bit before).1 holds)
  | next bit possible unique =>
      refine .next bit ?_ ?_
      · apply (Formula.advanceFormula_iff state bit before).2
        exact (Next.canStep_iff_canAdvanceAt state input before determinantNonzero
          represented bit).1 possible
      · intro other holds
        apply unique other
        apply (Next.canStep_iff_canAdvanceAt state input before determinantNonzero
          represented other).2
        exact (Formula.advanceFormula_iff state other before).1 holds

end Purelib.Geometry.CCL.Parser.Formula

end
