module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.CCL.Encoding.Parser.Next
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.SignTest
import Purelib.Geometry.CCL.Parser.Formula.Radial
public import Purelib.Geometry.CCL.Parser.Formula.Residual
import Purelib.Geometry.CCL.Parser.Formula.Sector
public import Purelib.Geometry.CCL.Parser.Formula.State
import Purelib.Geometry.CCL.Parser.Normalization
import Purelib.Geometry.CCL.Sector.Formula
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Geometry.Projective.Homography.Identity
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Init.Prelude
import Purelib.Data.CCL.Encoding.Parser.Constraint
import Purelib.Data.CCL.Encoding.Parser.Syntax
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

public section

open Purelib

open Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.ComplexContinuedFraction.Encoding.Sector

open Purelib.Data.Rat

open Purelib.Geometry.CCL

open Purelib.Geometry.CCL.Parser

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.Geometry.Projective.Hermitian.Formula

open Purelib.LinearAlgebra

/-!
# Finite Hermitian formulas for one raw CCL bit

Before a completed sector, the proposed child is just the next parser-state
formula at the unchanged affine tail.  On the third sector bit, the formula
checks the selected completed block and excludes its zero residual.  The
result is exactly the constructive one-bit semantic decision.
-/

namespace Purelib.Geometry.CCL.Parser.Formula

/-- Complete finite formula for a proposed next raw bit. -/
@[expose] def advanceFormula (state : Data.CCL.Encoding.Parser.State) (bit :
  Bool) :
  Formula.BoundaryFormula :=
  match state.phase with
  | .initial => Formula.stateFormula (State.step state bit)
  | .highUnary _ => Formula.stateFormula (State.step state bit)
  | .lowUnary _ => Formula.stateFormula (State.step state bit)
  | .loopUnary _ => Formula.stateFormula (State.step state bit)
  | .sector kind exponent bits =>
      match bits with
      | .zero => Formula.stateFormula (State.step state bit)
      | .one _ => Formula.stateFormula (State.step state bit)
      | .two first second =>
          let sector := Code.sectorOfBits first second bit
          .and
            (Formula.radialFormula kind exponent Coordinates2.Matrix.identityMatrix)
            (.and
              (Sector.sectorFormula sector
                (Parser.normalizedMatrix kind exponent Coordinates2.Matrix.identityMatrix))
              (.atom ⟨Formula.residualForm kind exponent sector, .positive⟩))

/-- Only the newly introduced part of a proposed child predicate. Retained history is supplied by the persistent-prefix
invariant. -/
@[expose] def incrementalAdvanceFormula (state :
  Data.CCL.Encoding.Parser.State) (bit : Bool) :
  Formula.BoundaryFormula :=
  match state.phase with
  | .initial => Formula.activeFormula (State.step state bit).phase
  | .highUnary _ => Formula.activeFormula (State.step state bit).phase
  | .lowUnary _ => Formula.activeFormula (State.step state bit).phase
  | .loopUnary _ => Formula.activeFormula (State.step state bit).phase
  | .sector _ _ bits =>
      match bits with
      | .zero => Formula.activeFormula (State.step state bit).phase
      | .one _ => Formula.activeFormula (State.step state bit).phase
      | .two _ _ => advanceFormula state bit

/-- A current state formula plus the new child predicate entails the full child formula. -/
theorem advanceFormula_holds_of_current_incremental
    (state : Data.CCL.Encoding.Parser.State) (bit : Bool) (value : Data.Gaussian.Basic.Canonical)
    (current : (Formula.stateFormula state).Holds value)
    (incremental : (incrementalAdvanceFormula state bit).Holds value) :
    (advanceFormula state bit).Holds value := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula,
          Formula.stateFormula,
          State.step, BoundaryFormula.Holds, if_pos (Eq.refl true), if_neg (show false ≠ true from Bool.noConfusion),
            -eq_self, -iff_self]
          using And.intro current.1 incremental
  | highUnary count =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula,
          Formula.stateFormula,
          State.step, BoundaryFormula.Holds, if_pos (Eq.refl true), if_neg (show false ≠ true from Bool.noConfusion),
            -eq_self, -iff_self]
          using And.intro current.1 incremental
  | lowUnary count =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula,
          Formula.stateFormula,
          State.step, BoundaryFormula.Holds, if_pos (Eq.refl true), if_neg (show false ≠ true from Bool.noConfusion),
            -eq_self, -iff_self]
          using And.intro current.1 incremental
  | loopUnary count =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula,
          Formula.stateFormula,
          State.step, BoundaryFormula.Holds, if_pos (Eq.refl true), if_neg (show false ≠ true from Bool.noConfusion),
            -eq_self, -iff_self]
          using And.intro current.1 incremental
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simpa only [advanceFormula, incrementalAdvanceFormula,
            Formula.stateFormula,
            State.step, BoundaryFormula.Holds, -eq_self, -iff_self]
            using And.intro current.1 incremental
      | one first =>
          simpa only [advanceFormula, incrementalAdvanceFormula,
            Formula.stateFormula,
            State.step, BoundaryFormula.Holds, -eq_self, -iff_self]
            using And.intro current.1 incremental
      | two first second => exact incremental

/-- The complete child predicate always contains its newly introduced part. Together with
`advanceFormula_holds_of_current_incremental`, this identifies the incremental formula as exactly the history-free
obligation once the current prefix is already represented. -/
theorem incrementalAdvanceFormula_holds_of_advance
    (state : Data.CCL.Encoding.Parser.State) (bit : Bool) (value : Data.Gaussian.Basic.Canonical)
    (advance : (advanceFormula state bit).Holds value) :
    (incrementalAdvanceFormula state bit).Holds value := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula,
          Formula.stateFormula,
          State.step, BoundaryFormula.Holds, if_pos (Eq.refl true), if_neg (show false ≠ true from Bool.noConfusion),
            -eq_self, -iff_self]
          using advance.2
  | highUnary count =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula,
          Formula.stateFormula,
          State.step, BoundaryFormula.Holds, if_pos (Eq.refl true), if_neg (show false ≠ true from Bool.noConfusion),
            -eq_self, -iff_self]
          using advance.2
  | lowUnary count =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula,
          Formula.stateFormula,
          State.step, BoundaryFormula.Holds, if_pos (Eq.refl true), if_neg (show false ≠ true from Bool.noConfusion),
            -eq_self, -iff_self]
          using advance.2
  | loopUnary count =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula,
          Formula.stateFormula,
          State.step, BoundaryFormula.Holds, if_pos (Eq.refl true), if_neg (show false ≠ true from Bool.noConfusion),
            -eq_self, -iff_self]
          using advance.2
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simpa only [advanceFormula, incrementalAdvanceFormula,
            Formula.stateFormula,
            State.step, BoundaryFormula.Holds, -eq_self, -iff_self] using advance.2
      | one first =>
          simpa only [advanceFormula, incrementalAdvanceFormula,
            Formula.stateFormula,
            State.step, BoundaryFormula.Holds, -eq_self, -iff_self] using advance.2
      | two first second => exact advance

/-- The compiled formula is propositionally identical to the affine next-bit predicate. -/
theorem advanceFormula_iff
    (state : Data.CCL.Encoding.Parser.State) (bit : Bool) (value : Data.Gaussian.Basic.Canonical) :
    (advanceFormula state bit).Holds value ↔
      Next.CanAdvanceAt state bit value := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      exact Formula.stateFormula_iff
        (State.step ⟨.initial, matrix, history⟩ bit) value
  | highUnary count =>
      exact Formula.stateFormula_iff
        (State.step ⟨.highUnary count, matrix, history⟩ bit) value
  | lowUnary count =>
      exact Formula.stateFormula_iff
        (State.step ⟨.lowUnary count, matrix, history⟩ bit) value
  | loopUnary count =>
      exact Formula.stateFormula_iff
        (State.step ⟨.loopUnary count, matrix, history⟩ bit) value
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          exact Formula.stateFormula_iff
            (State.step ⟨.sector kind exponent .zero, matrix, history⟩ bit) value
      | one first =>
          exact Formula.stateFormula_iff
            (State.step ⟨.sector kind exponent (.one first), matrix, history⟩ bit)
              value
      | two first second =>
          let sector := Code.sectorOfBits first second bit
          have identityDenominator := Homography.identityMatrix_denominator_ne value
          rw [advanceFormula]
          simp only [BoundaryFormula.Holds, Atom.Holds, Data.Rat.SignTest.Holds, -eq_self, -iff_self]
          have radialEquivalent := Formula.radialFormula_iff kind exponent Coordinates2.Matrix.identityMatrix value
            identityDenominator
          rewrite [Homography.homographic_identityMatrix] at radialEquivalent
          have sectorEquivalent := Formula.normalizedSectorFormula_iff kind exponent sector
            Coordinates2.Matrix.identityMatrix value identityDenominator
          rewrite [Homography.homographic_identityMatrix] at sectorEquivalent
          rewrite [Formula.eval_residualForm]
          constructor
          · rintro ⟨radial, sectorHolds, positive⟩
            refine ⟨⟨radialEquivalent.mp radial, sectorEquivalent.mp sectorHolds⟩, ?_⟩
            intro residualZero
            rw [residualZero, Data.Gaussian.Norm.Basic.normSq_zero] at positive
            exact (lt_irrefl (0 : Fraction.Rational) positive).elim
          · rintro ⟨⟨radial, sectorHolds⟩, residualNonzero⟩
            exact ⟨radialEquivalent.mpr radial, sectorEquivalent.mpr sectorHolds, Data.Gaussian.Norm.Basic.normSq_pos
              residualNonzero⟩

/-- The two compiled child formulas are mutually exclusive at every affine tail, including equality boundaries. -/
theorem advanceFormula_unique_at
    (state : Data.CCL.Encoding.Parser.State) (before : Data.Gaussian.Basic.Canonical)
    {left right : Bool}
    (leftHolds : (advanceFormula state left).Holds before)
    (rightHolds : (advanceFormula state right).Holds before) :
    left = right := by
  apply Next.canAdvanceAt_unique
  · exact (advanceFormula_iff state left before).1 leftHolds
  · exact (advanceFormula_iff state right before).1 rightHolds
end Purelib.Geometry.CCL.Parser.Formula

end
