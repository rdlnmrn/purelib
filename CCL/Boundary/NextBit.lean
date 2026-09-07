import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.ParserStep
import CCL.Boundary.Formula

/-!
# Finite Hermitian formulas for one raw CCL bit

Before a completed sector, the proposed child is just the next parser-state
formula at the unchanged affine tail.  On the third sector bit, the formula
checks the selected completed block and excludes its zero residual.  The
result is exactly the constructive one-bit semantic decision.
-/

namespace CCL.CCLNextBit

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Sector := CCL.Sectors.Sector
abbrev State := CCL.RawParser.State
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev Formula := CCL.CCLFormula.Formula

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Sectors
open CCL.RawParser
open CCL.RawParserSemantics
open CCL.ParserStep
open CCL.CCLGeometry
open CCL.CCLFormula

/-- Squared numerator of the normalized tail after subtraction of the
candidate sector representative. -/
def residualForm
    (kind : BlockKind) (exponent : Nat) (sector : Sector) :
    HermitianForm :=
  let matrix := normalizedMatrix kind exponent identityMatrix
  affineNormForm (matrix.a - sector.rep * matrix.c)
    (matrix.b - sector.rep * matrix.d)

theorem eval_residualForm
    (kind : BlockKind) (exponent : Nat) (sector : Sector)
    (value : Gaussian) :
    (residualForm kind exponent sector).eval value =
      normSq (normalizedValue kind exponent value - sector.rep) := by
  cases kind <;>
    simp only [residualForm, normalizedMatrix, normalizationMatrix,
      identityMatrix, CCL.Mat2.mul, CCL.Mat2.scale, normalizedValue,
      eval_affineNormForm, RFAP.ConstructiveGaussian.Gaussian.zero_mul,
      RFAP.ConstructiveGaussian.Gaussian.one_mul,
      RFAP.ConstructiveGaussian.Gaussian.zero_add,
      RFAP.ConstructiveGaussian.Gaussian.add_zero] <;>
    congr 1 <;>
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, mul_re, mul_im, add_re, add_im,
        zero_re, zero_im, one_re, one_im] <;>
      ring1

/-- Complete finite formula for a proposed next raw bit. -/
def advanceFormula (state : State) (bit : Bool) : Formula :=
  match state.phase with
  | .sector kind exponent (.two first second) =>
      let sector := sectorOfBits first second bit
      .and
        (radialFormula kind exponent identityMatrix)
        (.and
          (sectorFormula sector
            (normalizedMatrix kind exponent identityMatrix))
          (.atom ⟨residualForm kind exponent sector, .positive⟩))
  | _ => stateFormula (step state bit)

/-- Only the newly introduced part of a proposed child predicate.  Retained
history is supplied by the persistent-prefix invariant. -/
def incrementalAdvanceFormula (state : State) (bit : Bool) : Formula :=
  match state.phase with
  | .sector _ _ (.two _ _) => advanceFormula state bit
  | _ => activeFormula (step state bit).phase

/-- A current state formula plus the new child predicate entails the full
child formula. -/
theorem advanceFormula_holds_of_current_incremental
    (state : State) (bit : Bool) (value : Gaussian)
    (current : (stateFormula state).Holds value)
    (incremental : (incrementalAdvanceFormula state bit).Holds value) :
    (advanceFormula state bit).Holds value := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula, stateFormula,
          step, Formula.Holds, Bool.false_eq_true, if_false, if_true]
          using And.intro current.1 incremental
  | highUnary count =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula, stateFormula,
          step, Formula.Holds, Bool.false_eq_true, if_false, if_true]
          using And.intro current.1 incremental
  | lowUnary count =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula, stateFormula,
          step, Formula.Holds, Bool.false_eq_true, if_false, if_true]
          using And.intro current.1 incremental
  | loopUnary count =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula, stateFormula,
          step, Formula.Holds, Bool.false_eq_true, if_false, if_true]
          using And.intro current.1 incremental
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simpa only [advanceFormula, incrementalAdvanceFormula, stateFormula,
            step, Formula.Holds]
            using And.intro current.1 incremental
      | one first =>
          simpa only [advanceFormula, incrementalAdvanceFormula, stateFormula,
            step, Formula.Holds]
            using And.intro current.1 incremental
      | two first second => exact incremental

/-- The complete child predicate always contains its newly introduced part.
Together with `advanceFormula_holds_of_current_incremental`, this identifies
the incremental formula as exactly the history-free obligation once the
current prefix is already represented. -/
theorem incrementalAdvanceFormula_holds_of_advance
    (state : State) (bit : Bool) (value : Gaussian)
    (advance : (advanceFormula state bit).Holds value) :
    (incrementalAdvanceFormula state bit).Holds value := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula, stateFormula,
          step, Formula.Holds, Bool.false_eq_true, if_false, if_true]
          using advance.2
  | highUnary count =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula, stateFormula,
          step, Formula.Holds, Bool.false_eq_true, if_false, if_true]
          using advance.2
  | lowUnary count =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula, stateFormula,
          step, Formula.Holds, Bool.false_eq_true, if_false, if_true]
          using advance.2
  | loopUnary count =>
      cases bit <;>
        simpa only [advanceFormula, incrementalAdvanceFormula, stateFormula,
          step, Formula.Holds, Bool.false_eq_true, if_false, if_true]
          using advance.2
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simpa only [advanceFormula, incrementalAdvanceFormula, stateFormula,
            step, Formula.Holds] using advance.2
      | one first =>
          simpa only [advanceFormula, incrementalAdvanceFormula, stateFormula,
            step, Formula.Holds] using advance.2
      | two first second => exact advance

/-- The compiled formula is propositionally identical to the affine
next-bit predicate. -/
theorem advanceFormula_iff
    (state : State) (bit : Bool) (value : Gaussian) :
    (advanceFormula state bit).Holds value ↔
      CanAdvanceAt state bit value := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      exact stateFormula_iff
        (step ⟨.initial, matrix, history⟩ bit) value
  | highUnary count =>
      exact stateFormula_iff
        (step ⟨.highUnary count, matrix, history⟩ bit) value
  | lowUnary count =>
      exact stateFormula_iff
        (step ⟨.lowUnary count, matrix, history⟩ bit) value
  | loopUnary count =>
      exact stateFormula_iff
        (step ⟨.loopUnary count, matrix, history⟩ bit) value
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          exact stateFormula_iff
            (step ⟨.sector kind exponent .zero, matrix, history⟩ bit) value
      | one first =>
          exact stateFormula_iff
            (step ⟨.sector kind exponent (.one first), matrix, history⟩ bit)
              value
      | two first second =>
          let sector := sectorOfBits first second bit
          have identityDenominator := identityMatrix_denominator_ne value
          rw [advanceFormula]
          simp only [Formula.Holds, Atom.Holds, SignTest.Holds]
          rw [radialFormula_iff kind exponent identityMatrix value
              identityDenominator,
            normalizedSectorFormula_iff kind exponent sector identityMatrix
              value identityDenominator,
            homographic_identityMatrix, eval_residualForm]
          constructor
          · rintro ⟨radial, sectorHolds, positive⟩
            refine ⟨⟨radial, sectorHolds⟩, ?_⟩
            intro residualZero
            rw [residualZero, normSq_zero] at positive
            exact (lt_irrefl (0 : Coordinate) positive).elim
          · rintro ⟨⟨radial, sectorHolds⟩, residualNonzero⟩
            exact ⟨radial, sectorHolds, normSq_pos residualNonzero⟩

/-- The two compiled child formulas are mutually exclusive at every affine
tail, including equality boundaries. -/
theorem advanceFormula_unique_at
    (state : State) (before : Gaussian)
    {left right : Bool}
    (leftHolds : (advanceFormula state left).Holds before)
    (rightHolds : (advanceFormula state right).Holds before) :
    left = right := by
  apply canAdvanceAt_unique
  · exact (advanceFormula_iff state left before).1 leftHolds
  · exact (advanceFormula_iff state right before).1 rightHolds

/-- Proposed child formula expressed in the original input coordinate by
pulling it back through the explicit adjugate chart. -/
def inputAdvanceFormula (state : State) (bit : Bool) : Formula :=
  (advanceFormula state bit).pullback
    (CCL.CCLPullback.adjugate state.matrix)

/-- History-free child formula in the original input coordinate. -/
def inputIncrementalAdvanceFormula (state : State) (bit : Bool) : Formula :=
  (incrementalAdvanceFormula state bit).pullback
    (CCL.CCLPullback.adjugate state.matrix)

theorem inputAdvanceFormula_iff
    (state : State) (bit : Bool) (input : Gaussian)
    (inverseDenominator : denominator
      (CCL.CCLPullback.adjugate state.matrix) input ≠ 0) :
    (inputAdvanceFormula state bit).Holds input ↔
      CanAdvanceAt state bit
        (homographic (CCL.CCLPullback.adjugate state.matrix)
          input) := by
  rw [inputAdvanceFormula,
    Formula.pullback_iff
      (CCL.CCLPullback.adjugate state.matrix)
      (advanceFormula state bit) input inverseDenominator,
    advanceFormula_iff]

/-- A represented input lies in the affine domain of the inverse decoder. -/
theorem inverseDenominator_of_represents
    (state : State) (input tail : Gaussian)
    (determinantNonzero :
      CCL.CCLPullback.determinant state.matrix ≠ 0)
    (represented : Represents state input tail) :
    denominator (CCL.CCLPullback.adjugate state.matrix) input ≠
      0 := by
  have inverseDenominator :=
    CCL.CCLPullback.adjugate_denominator_homographic_ne
      state.matrix tail determinantNonzero represented.1
  rw [represented.2.1]
  exact inverseDenominator

/-- The adjugate chart recovers the unique represented affine tail. -/
theorem inverseTail_eq
    (state : State) (input tail : Gaussian)
    (determinantNonzero :
      CCL.CCLPullback.determinant state.matrix ≠ 0)
    (represented : Represents state input tail) :
    homographic (CCL.CCLPullback.adjugate state.matrix) input =
      tail := by
  calc
    homographic (CCL.CCLPullback.adjugate state.matrix) input =
        homographic (CCL.CCLPullback.adjugate state.matrix)
          (homographic state.matrix tail) := congrArg
            (homographic (CCL.CCLPullback.adjugate state.matrix))
            represented.2.1
    _ = tail :=
      CCL.CCLPullback.homographic_adjugate_forward_inverse
        state.matrix tail determinantNonzero represented.1

/-- Recover the canonical inverse-decoder representation from mere
existential representability.  The tail itself is computed from the input;
the existential is eliminated only to prove its propositional contract. -/
theorem represents_inverse_tail_of_represented
    (state : State) (input : Gaussian)
    (determinantNonzero :
      CCL.CCLPullback.determinant state.matrix ≠ 0)
    (represented : ∃ tail, Represents state input tail) :
    Represents state input
      (homographic (CCL.CCLPullback.adjugate state.matrix)
        input) := by
  rcases represented with ⟨tail, tailRepresents⟩
  have inverseDenominator := inverseDenominator_of_represents state input
    tail determinantNonzero tailRepresents
  apply CCL.CCLPullback.represents_of_inverse_tail state input
    determinantNonzero inverseDenominator
  rw [inverseTail_eq state input tail determinantNonzero tailRepresents]
  exact tailRepresents.2.2

/-- At a represented state, the original-coordinate child formula is
exactly semantic possibility of that bit. -/
theorem inputAdvanceFormula_canStep_iff
    (state : State) (input tail : Gaussian)
    (determinantNonzero :
      CCL.CCLPullback.determinant state.matrix ≠ 0)
    (represented : Represents state input tail)
    (bit : Bool) :
    (inputAdvanceFormula state bit).Holds input ↔
      CanStep state input bit := by
  have inverseDenominator := inverseDenominator_of_represents state input tail
    determinantNonzero represented
  rw [inputAdvanceFormula_iff state bit input inverseDenominator,
    inverseTail_eq state input tail determinantNonzero represented]
  exact (canStep_iff_canAdvanceAt state input tail determinantNonzero
    represented bit).symm

/-- The two input-coordinate child regions are disjoint at every represented
rational input. -/
theorem inputAdvanceFormula_unique
    (state : State) (input tail : Gaussian)
    (determinantNonzero :
      CCL.CCLPullback.determinant state.matrix ≠ 0)
    (represented : Represents state input tail)
    {left right : Bool}
    (leftHolds : (inputAdvanceFormula state left).Holds input)
    (rightHolds : (inputAdvanceFormula state right).Holds input) :
    left = right := by
  apply canStep_unique determinantNonzero
  · exact (inputAdvanceFormula_canStep_iff state input tail
      determinantNonzero represented left).1 leftHolds
  · exact (inputAdvanceFormula_canStep_iff state input tail
      determinantNonzero represented right).1 rightHolds

/-- Formula-facing result of the total local semantic decision. -/
inductive Decision (state : State) (input before : Gaussian) where
  | terminal
      (none : ∀ bit, ¬(advanceFormula state bit).Holds before)
  | next (bit : Bool) (holds : (advanceFormula state bit).Holds before)
      (unique : ∀ other, (advanceFormula state other).Holds before →
        other = bit)

/-- Evaluate the two finite formulas and return their unique bit or the
affine-terminal outcome. -/
def decide
    (state : State) (input before : Gaussian)
    (determinantNonzero :
      CCL.Chordal.Mat2.det state.matrix ≠ 0)
    (represented : Represents state input before) :
    Decision state input before := by
  cases decideLocal state input before determinantNonzero represented with
  | terminal none =>
      exact .terminal (by
        intro bit holds
        apply none bit
        apply (canStep_iff_canAdvanceAt state input before determinantNonzero
          represented bit).2
        exact (advanceFormula_iff state bit before).1 holds)
  | next bit possible unique =>
      refine .next bit ?_ ?_
      · apply (advanceFormula_iff state bit before).2
        exact (canStep_iff_canAdvanceAt state input before determinantNonzero
          represented bit).1 possible
      · intro other holds
        apply unique other
        apply (canStep_iff_canAdvanceAt state input before determinantNonzero
          represented other).2
        exact (advanceFormula_iff state other before).1 holds

end CCL.CCLNextBit
