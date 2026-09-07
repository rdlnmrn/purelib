import CCL.EncoderParserBridge
import FTA.CCLParserGeometry

/-!
# Finite Hermitian formula for one proposed raw CCL bit

The geometric branch controller in Theorem 10.2 needs the exact finite
comparison associated with a proposed parser child.  Before a completed
sector, the ordinary next-state formula is evaluated at the unchanged affine
tail.  On the third sector bit, the selected full block is checked at the old
tail and its subtraction numerator is required to be nonzero; only then is the
reciprocal coordinate change affine.

This module proves that the compiled Hermitian formula is exactly
`EncoderParserBridge.CanAdvanceAt`, the semantic predicate already proved
equivalent to `RawParserSemantics.CanStep` at a represented state.
-/

namespace FTA
namespace CCLNextBitFormula

open CCL CCL.GaussianRat
open CCL.EncoderParserBridge
open FTA.CCLGeometry
open FTA.CCLParserGeometry

abbrev QI := CCL.GaussianRat

/-- Squared numerator of the normalized homography after subtracting the
candidate sector representative.  Positivity excludes the projective
terminal value. -/
def residualForm
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector) :
    HermitianForm :=
  let M := normalizedMatrix kind exponent RawParser.identityMatrix
  affineNormForm (M.a - sector.rep * M.c) (M.b - sector.rep * M.d)

theorem eval_residualForm
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector) (z : QI) :
    (residualForm kind exponent sector).eval z =
      normSq (RawParser.normalizedValue kind exponent z - sector.rep) := by
  cases kind <;>
    simp [residualForm, normalizedMatrix, normalizationMatrix,
      RawParser.identityMatrix, Mat2.mul, Mat2.scale,
      RawParser.normalizedValue, eval_affineNormForm] <;>
    congr 1 <;> ext <;> simp only [sub_re, sub_im, mul_re, mul_im,
      add_re, add_im, neg_re, neg_im] <;> ring

/-- Exact finite formula for a proposed next raw bit at the current affine
tail. -/
def advanceFormula (state : RawParser.State) (bit : Bool) : Formula :=
  match state.phase with
  | .sector kind exponent (.two first second) =>
      let sector := RawParser.sectorOfBits first second bit
      .and
        (radialFormula kind exponent RawParser.identityMatrix)
        (.and
          (sectorFormula sector
            (normalizedMatrix kind exponent RawParser.identityMatrix))
          (.atom ⟨residualForm kind exponent sector, .positive⟩))
  | _ => stateFormula (RawParser.step state bit)

/-- The genuinely new predicate introduced by one bit.  Ordinary phases keep
the current history unchanged, so only the next active-phase formula is new;
the third sector bit retains the existing full-block and nonterminal test.
This is the formula whose boundary faces must be entered by a new owner grid. -/
def incrementalAdvanceFormula
    (state : RawParser.State) (bit : Bool) : Formula :=
  match state.phase with
  | .sector _ _ (.two _ _) => advanceFormula state bit
  | _ => activeFormula (RawParser.step state bit).phase

/-- A point satisfying the old state and the incremental predicate satisfies
the original complete next-bit formula.  Thus historical constraints need
not be presented to the next tangent-cone search. -/
theorem advanceFormula_holds_of_current_incremental
    (state : RawParser.State) (bit : Bool) (z : QI)
    (current : (stateFormula state).Holds z)
    (incremental : (incrementalAdvanceFormula state bit).Holds z) :
    (advanceFormula state bit).Holds z := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;>
        simpa [advanceFormula, incrementalAdvanceFormula, stateFormula,
          RawParser.step] using ⟨current.1, incremental⟩
  | highUnary count =>
      cases bit <;>
        simpa [advanceFormula, incrementalAdvanceFormula, stateFormula,
          RawParser.step] using ⟨current.1, incremental⟩
  | lowUnary count =>
      cases bit <;>
        simpa [advanceFormula, incrementalAdvanceFormula, stateFormula,
          RawParser.step] using ⟨current.1, incremental⟩
  | loopUnary count =>
      cases bit <;>
        simpa [advanceFormula, incrementalAdvanceFormula, stateFormula,
          RawParser.step] using ⟨current.1, incremental⟩
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simpa [advanceFormula, incrementalAdvanceFormula, stateFormula,
            RawParser.step] using ⟨current.1, incremental⟩
      | one first =>
          simpa [advanceFormula, incrementalAdvanceFormula, stateFormula,
            RawParser.step] using ⟨current.1, incremental⟩
      | two first second => exact incremental

/-- The formula consumed by the generalized-circle machinery is propositionally
identical to the affine next-bit predicate. -/
theorem advanceFormula_iff
    (state : RawParser.State) (bit : Bool) (z : QI) :
    (advanceFormula state bit).Holds z ↔ CanAdvanceAt state bit z := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      exact stateFormula_iff (RawParser.step
        ⟨.initial, matrix, history⟩ bit) z
  | highUnary count =>
      exact stateFormula_iff (RawParser.step
        ⟨.highUnary count, matrix, history⟩ bit) z
  | lowUnary count =>
      exact stateFormula_iff (RawParser.step
        ⟨.lowUnary count, matrix, history⟩ bit) z
  | loopUnary count =>
      exact stateFormula_iff (RawParser.step
        ⟨.loopUnary count, matrix, history⟩ bit) z
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          exact stateFormula_iff (RawParser.step
            ⟨.sector kind exponent .zero, matrix, history⟩ bit) z
      | one first =>
          exact stateFormula_iff (RawParser.step
            ⟨.sector kind exponent (.one first), matrix, history⟩ bit) z
      | two first second =>
          let sector := RawParser.sectorOfBits first second bit
          have identityDenominator :
              RawParser.identityMatrix.c * z + RawParser.identityMatrix.d ≠ 0 :=
            identityMatrix_denominator_ne z
          rw [advanceFormula]
          simp only [Formula.Holds, Atom.Holds, SignTest.Holds]
          rw [radialFormula_iff kind exponent RawParser.identityMatrix z
              identityDenominator,
            normalizedSectorFormula_iff kind exponent sector
              RawParser.identityMatrix z identityDenominator,
            homographic_identityMatrix, eval_residualForm]
          constructor
          · rintro ⟨radial, sectorHolds, positive⟩
            refine ⟨⟨radial, sectorHolds⟩, ?_⟩
            intro zero
            rw [zero, normSq_zero] at positive
            linarith
          · rintro ⟨⟨radial, sectorHolds⟩, residual⟩
            exact ⟨radial, sectorHolds, normSq_pos residual⟩

/-- The two compiled child formulas are mutually exclusive at every affine
tail, including every equality boundary. -/
theorem advanceFormula_unique_at
    (state : RawParser.State) (before : QI)
    {left right : Bool}
    (leftHolds : (advanceFormula state left).Holds before)
    (rightHolds : (advanceFormula state right).Holds before) :
    left = right := by
  apply canAdvanceAt_unique
  · exact (advanceFormula_iff state left before).1 leftHolds
  · exact (advanceFormula_iff state right before).1 rightHolds

/-- Semantic specialization of unconditional formula disjointness at the
unique tail of an invertible represented state. -/
theorem advanceFormula_unique
    (state : RawParser.State) (input before : QI)
    (determinant : state.matrix.det ≠ 0)
    (represented : RawParserSemantics.Represents state input before)
    {left right : Bool}
    (leftHolds : (advanceFormula state left).Holds before)
    (rightHolds : (advanceFormula state right).Holds before) :
    left = right := by
  apply RawParserSemantics.canStep_unique determinant
  · apply (canStep_iff_canAdvanceAt state input before determinant
      represented left).2
    exact (advanceFormula_iff state left before).1 leftHolds
  · apply (canStep_iff_canAdvanceAt state input before determinant
      represented right).2
    exact (advanceFormula_iff state right before).1 rightHolds

/-- Formula-facing form of the total local semantic decision. -/
inductive Decision
    (state : RawParser.State) (input before : QI) where
  | terminal
      (none : ∀ bit, ¬(advanceFormula state bit).Holds before)
  | next (bit : Bool) (holds : (advanceFormula state bit).Holds before)
      (unique : ∀ other, (advanceFormula state other).Holds before →
        other = bit)

/-- Evaluate the finite next-bit formulas and return either their unique
satisfying bit or the affine-terminal outcome. -/
def decide
    (state : RawParser.State) (input before : QI)
    (determinant : state.matrix.det ≠ 0)
    (represented : RawParserSemantics.Represents state input before) :
    Decision state input before := by
  cases decideLocal state input before determinant represented with
  | terminal none =>
      exact .terminal (by
        intro bit holds
        apply none bit
        apply (canStep_iff_canAdvanceAt state input before determinant
          represented bit).2
        exact (advanceFormula_iff state bit before).1 holds)
  | next bit possible unique =>
      refine .next bit ?_ ?_
      · apply (advanceFormula_iff state bit before).2
        exact (canStep_iff_canAdvanceAt state input before determinant
          represented bit).1 possible
      · intro other holds
        apply unique other
        apply (canStep_iff_canAdvanceAt state input before determinant
          represented other).2
        exact (advanceFormula_iff state other before).1 holds

end CCLNextBitFormula
end FTA
