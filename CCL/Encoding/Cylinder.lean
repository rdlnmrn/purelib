import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Encoding.BlockContraction

/-!
# Finite completed-block cylinders

A cylinder is represented by a finite list of completed raw CCL blocks and a
finite realization trace.  No collection of all compatible points is formed.
The main theorem compares any two supplied realization traces and obtains the
explicit `2⁻ⁿ` squared-chordal bound.
-/

namespace CCL.Cylinder

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Sector := CCL.Sectors.Sector
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev Word := List Bool
abbrev Tail := CCL.BlockContraction.Tail

open CCL.Chordal
open CCL.BlockContraction

/-- Whether a completed block is regular or the distinguished initial-low
form.  Allowing the low form in the finite list makes the contraction theorem
structural; well-formed syntax can separately restrict it to the first block. -/
inductive BlockKind where
  | regular
  | initialLow
deriving DecidableEq, Repr

/-- All finite data determining one completed raw CCL block. -/
structure Block where
  kind : BlockKind
  exponent : Nat
  sector : Sector
deriving DecidableEq, Repr

namespace Block

def word (block : Block) : Word :=
  match block.kind with
  | .regular => CCL.Decoder.regularWord block.exponent block.sector
  | .initialLow => CCL.Decoder.lowWord block.exponent block.sector

def matrix (block : Block) : Mat2 :=
  match block.kind with
  | .regular => CCL.Decoder.regularBlock block.exponent block.sector
  | .initialLow => CCL.Decoder.lowBlock block.exponent block.sector

theorem contraction_half (block : Block)
    (left right : Tail block.sector) :
    chordalSq (CCL.Mat2.act block.matrix left.point)
        (CCL.Mat2.act block.matrix right.point) ≤
      (1 / 2 : Coordinate) * chordalSq left.point right.point := by
  cases block with
  | mk kind exponent sector =>
      cases kind with
      | regular =>
          exact regularBlock_contraction_half exponent left right
      | initialLow =>
          exact lowBlock_contraction_half exponent left right

theorem word_length_ge_four (block : Block) : 4 ≤ block.word.length := by
  cases block with
  | mk kind exponent sector =>
      cases kind with
      | regular =>
          rw [word, CCL.Decoder.regularWord_length]
          exact Nat.le_add_left 4 exponent
      | initialLow =>
          rw [word, CCL.Decoder.lowWord_length]
          exact (by omega)

end Block

/-- Raw binary word represented by a finite completed-block prefix. -/
def rawWord : List Block → Word
  | [] => []
  | block :: remaining => block.word ++ rawWord remaining

@[simp] theorem rawWord_nil : rawWord [] = [] := rfl

@[simp] theorem rawWord_cons (block : Block) (remaining : List Block) :
    rawWord (block :: remaining) = block.word ++ rawWord remaining := rfl

/-- Finite evidence that one projective coordinate realizes all displayed
blocks.  The terminal tail remains explicit and valid; it may be affine or
the formal projective point `ω`. -/
inductive Realizes : (blocks : List Block) → Proj → Type where
  | done (point : Proj) (valid : Proj.HasNonzeroCoordinate point) :
      Realizes [] point
  | step {remaining : List Block} (block : Block)
      (tail : Tail block.sector)
      (rest : Realizes remaining tail.point) :
      Realizes (block :: remaining) (CCL.Mat2.act block.matrix tail.point)

namespace Realizes

/-- Any two finite realizations of the same completed-block prefix are within
the explicit squared-chordal width `2⁻ⁿ`. -/
theorem chordalSq_le_half_pow
    {blocks : List Block} {left right : Proj}
    (leftRealizes : Realizes blocks left)
    (rightRealizes : Realizes blocks right) :
    chordalSq left right ≤ (1 / 2 : Coordinate) ^ blocks.length := by
  induction leftRealizes generalizing right with
  | done left leftValid =>
      cases rightRealizes with
      | done right rightValid =>
          rw [List.length_nil, pow_zero]
          exact chordalSq_le_one leftValid rightValid
  | @step remaining block leftTail leftRest inductionHypothesis =>
      cases rightRealizes with
      | step _ rightTail rightRest =>
          calc
            chordalSq (CCL.Mat2.act block.matrix leftTail.point)
                (CCL.Mat2.act block.matrix rightTail.point) ≤
                (1 / 2 : Coordinate) *
                  chordalSq leftTail.point rightTail.point :=
              block.contraction_half leftTail rightTail
            _ ≤ (1 / 2 : Coordinate) *
                (1 / 2 : Coordinate) ^ remaining.length :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (inductionHypothesis rightRest) (by decide)
            _ = (1 / 2 : Coordinate) ^ (block :: remaining).length := by
              rw [List.length_cons, pow_succ]
              ring1

/-- Extending by more completed blocks can only improve the universal power
bound. -/
theorem chordalSq_le_half_pow_of_append
    {blocksPrefix blocksSuffix : List Block} {left right : Proj}
    (leftRealizes : Realizes (blocksPrefix ++ blocksSuffix) left)
    (rightRealizes : Realizes (blocksPrefix ++ blocksSuffix) right) :
    chordalSq left right ≤
      (1 / 2 : Coordinate) ^ blocksPrefix.length := by
  have fullBound := chordalSq_le_half_pow leftRealizes rightRealizes
  have halfNonnegative : (0 : Coordinate) ≤ 1 / 2 := (by decide)
  have halfPowLeOne : ∀ exponent : Nat,
      (1 / 2 : Coordinate) ^ exponent ≤ 1 := by
    intro exponent
    induction exponent with
    | zero => exact le_rfl
    | succ exponent inductionHypothesis =>
        rw [pow_succ]
        calc
          (1 / 2 : Coordinate) ^ exponent * (1 / 2) ≤
              1 * (1 / 2) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              inductionHypothesis halfNonnegative
          _ ≤ 1 := by decide
  have suffixFactorLeOne :
      (1 / 2 : Coordinate) ^ blocksSuffix.length ≤ 1 := by
    exact halfPowLeOne blocksSuffix.length
  have powerOrder :
      (1 / 2 : Coordinate) ^ (blocksPrefix ++ blocksSuffix).length ≤
        (1 / 2 : Coordinate) ^ blocksPrefix.length := by
    rw [List.length_append, pow_add]
    calc
      (1 / 2 : Coordinate) ^ blocksPrefix.length *
          (1 / 2 : Coordinate) ^ blocksSuffix.length ≤
          (1 / 2 : Coordinate) ^ blocksPrefix.length * 1 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          suffixFactorLeOne
          (RFAP.ConstructiveFraction.pow_nonneg_direct halfNonnegative _)
      _ = (1 / 2 : Coordinate) ^ blocksPrefix.length := by ring1
  exact fullBound.trans powerOrder

end Realizes

/-- Finite universal cylinder predicate in the pairwise form used by the
paper.  It quantifies over supplied finite realization certificates, not over
a named set of points. -/
def ChordBound (blocks : List Block) (bound : Coordinate) : Prop :=
  ∀ {left right : Proj}, Realizes blocks left → Realizes blocks right →
    chordalSq left right ≤ bound

/-- The explicit shrinking-cylinder theorem. -/
theorem completedPrefix_chordBound (blocks : List Block) :
    ChordBound blocks ((1 / 2 : Coordinate) ^ blocks.length) := by
  intro left right leftRealizes rightRealizes
  exact Realizes.chordalSq_le_half_pow leftRealizes rightRealizes

/-! ## Projectively rescaled finite realizations -/

namespace Block

theorem matrix_det_ne_zero (block : Block) :
    CCL.Chordal.Mat2.det block.matrix ≠ 0 := by
  cases block with
  | mk kind exponent sector =>
      cases kind with
      | regular =>
          rw [matrix, CCL.Decoder.regularBlock_det]
          exact RFAP.ConstructiveGaussian.Gaussian.neg_ne_zero_direct
            (RFAP.ConstructiveGaussian.Gaussian.natPow_ne_zero_direct
              RFAP.ConstructiveGaussian.Gaussian.gamma (by decide)
              (exponent + 1))
      | initialLow =>
          rw [matrix, CCL.Decoder.lowBlock_det]
          exact RFAP.ConstructiveGaussian.Gaussian.neg_ne_zero_direct
            (RFAP.ConstructiveGaussian.Gaussian.natPow_ne_zero_direct
              RFAP.ConstructiveGaussian.Gaussian.gamma (by decide)
              (exponent + 1))

end Block

/-- A compatible tail may be carried by any valid homogeneous pair equivalent
to the canonical affine or terminal model.  This is the form produced by an
integral decoder without choosing a projective normalization. -/
structure ProjectiveTail (sector : Sector) where
  point : Proj
  valid : CCL.Chordal.Proj.HasNonzeroCoordinate point
  model : Tail sector
  equivalent : point.Equivalent model.point

namespace ProjectiveTail

def ofTail {sector : Sector} (tail : Tail sector) : ProjectiveTail sector where
  point := tail.point
  valid := by
    cases tail with
    | omega => exact CCL.Chordal.Proj.omega_hasNonzeroCoordinate
    | affine tail value compatible =>
        exact CCL.Chordal.Proj.affine_hasNonzeroCoordinate tail
  model := tail
  equivalent := by
    cases tail <;> rfl

theorem model_valid {sector : Sector} (tail : ProjectiveTail sector) :
    CCL.Chordal.Proj.HasNonzeroCoordinate tail.model.point := by
  cases tail.model with
  | omega => exact CCL.Chordal.Proj.omega_hasNonzeroCoordinate
  | affine value source compatible =>
      exact CCL.Chordal.Proj.affine_hasNonzeroCoordinate value

end ProjectiveTail

namespace Tail

open RFAP.ConstructiveGaussian.Gaussian

/-- The canonical tail is the terminal tail exactly at the selected
representative, or an affine compatible tail for the displayed value. -/
def ModelsValue {sector : Sector} (tail : Tail sector) (value : Gaussian) : Prop :=
  match tail with
  | .omega => value = sector.rep
  | .affine _ storedValue _ => storedValue = value

theorem regularBlock_act_equivalent {sector : Sector} (exponent : Nat)
    (tail : Tail sector) (value target : Gaussian)
    (models : tail.ModelsValue value)
    (targetIdentity : natPow gamma exponent * value = target) :
    (CCL.Mat2.act (CCL.Decoder.regularBlock exponent sector)
      tail.point).Equivalent (CCL.Proj.affine target) := by
  cases tail with
  | omega =>
      rw [targetIdentity.symm, models]
      dsimp only [CCL.Proj.Equivalent,
        CCL.BlockContraction.Tail.point, CCL.Mat2.act,
        CCL.Decoder.regularBlock, CCL.Proj.omega,
        CCL.Proj.affine]
      rw [natPow_succ]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im, zero_re, zero_im,
          one_re, one_im] <;>
        ring1
  | affine tail storedValue compatible =>
      rw [models] at compatible
      rw [targetIdentity.symm]
      dsimp only [CCL.Proj.Equivalent,
        CCL.BlockContraction.Tail.point, CCL.Mat2.act,
        CCL.Decoder.regularBlock, CCL.Proj.affine]
      simp only [RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      change
        natPow gamma (exponent + 1) * sector.rep * tail +
            natPow gamma exponent =
          (natPow gamma exponent * value) * (gamma * tail)
      rw [natPow_succ]
      calc
        natPow gamma exponent * gamma * sector.rep * tail +
            natPow gamma exponent =
            natPow gamma exponent *
              (gamma * tail * sector.rep + 1) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [add_re, add_im, mul_re, mul_im, one_re, one_im] <;>
            ring1
        _ = natPow gamma exponent * (gamma * tail * value) := by
          rw [compatible.equation]
        _ = (natPow gamma exponent * value) * (gamma * tail) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [mul_re, mul_im] <;>
            ring1

theorem lowBlock_act_equivalent {sector : Sector} (exponent : Nat)
    (tail : Tail sector) (value target : Gaussian)
    (models : tail.ModelsValue value)
    (sourceIdentity : value = natPow gamma exponent * target) :
    (CCL.Mat2.act (CCL.Decoder.lowBlock exponent sector)
      tail.point).Equivalent (CCL.Proj.affine target) := by
  cases tail with
  | omega =>
      rw [models] at sourceIdentity
      dsimp only [CCL.Proj.Equivalent,
        CCL.BlockContraction.Tail.point, CCL.Mat2.act,
        CCL.Decoder.lowBlock, CCL.Proj.omega,
        CCL.Proj.affine]
      rw [sourceIdentity, natPow_succ]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [add_re, add_im, mul_re, mul_im, zero_re, zero_im,
          one_re, one_im] <;>
        ring1
  | affine tail storedValue compatible =>
      rw [models] at compatible
      dsimp only [CCL.Proj.Equivalent,
        CCL.BlockContraction.Tail.point, CCL.Mat2.act,
        CCL.Decoder.lowBlock, CCL.Proj.affine]
      simp only [RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      change gamma * sector.rep * tail + 1 =
        target * (natPow gamma (exponent + 1) * tail)
      rw [natPow_succ]
      calc
        gamma * sector.rep * tail + 1 =
            gamma * tail * sector.rep + 1 := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [add_re, add_im, mul_re, mul_im, one_re, one_im] <;>
            ring1
        _ = gamma * tail * value := compatible.equation.symm
        _ = target * (natPow gamma exponent * gamma * tail) := by
          rw [sourceIdentity]
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [mul_re, mul_im] <;>
            ring1

end Tail

namespace Block

theorem act_projectiveTail_valid (block : Block)
    (tail : ProjectiveTail block.sector) :
    CCL.Chordal.Proj.HasNonzeroCoordinate
      (CCL.Mat2.act block.matrix tail.point) :=
  CCL.Chordal.Mat2.act_hasNonzeroCoordinate
    block.matrix_det_ne_zero tail.valid

theorem act_model_valid (block : Block) (tail : ProjectiveTail block.sector) :
    CCL.Chordal.Proj.HasNonzeroCoordinate
      (CCL.Mat2.act block.matrix tail.model.point) :=
  CCL.Chordal.Mat2.act_hasNonzeroCoordinate
    block.matrix_det_ne_zero tail.model_valid

/-- Completed-block contraction is invariant under arbitrary nonzero
projective rescalings of both certified tails. -/
theorem projective_contraction_half (block : Block)
    (left right : ProjectiveTail block.sector) :
    chordalSq (CCL.Mat2.act block.matrix left.point)
        (CCL.Mat2.act block.matrix right.point) ≤
      (1 / 2 : Coordinate) * chordalSq left.point right.point := by
  have leftActEquivalent :
      (CCL.Mat2.act block.matrix left.point).Equivalent
        (CCL.Mat2.act block.matrix left.model.point) :=
    CCL.Mat2.act_respects_equivalent block.matrix left.equivalent
  have rightActEquivalent :
      (CCL.Mat2.act block.matrix right.point).Equivalent
        (CCL.Mat2.act block.matrix right.model.point) :=
    CCL.Mat2.act_respects_equivalent block.matrix right.equivalent
  have inputEquality : chordalSq left.model.point right.model.point =
      chordalSq left.point right.point := by
    calc
      chordalSq left.model.point right.model.point =
          chordalSq left.point right.model.point :=
        (CCL.Chordal.chordalSq_eq_of_equivalent_left
          left.valid left.model_valid left.equivalent
          right.model.point).symm
      _ = chordalSq left.point right.point :=
        (CCL.Chordal.chordalSq_eq_of_equivalent_right
          right.valid right.model_valid right.equivalent left.point).symm
  calc
    chordalSq (CCL.Mat2.act block.matrix left.point)
        (CCL.Mat2.act block.matrix right.point) =
        chordalSq (CCL.Mat2.act block.matrix left.model.point)
          (CCL.Mat2.act block.matrix right.point) :=
      CCL.Chordal.chordalSq_eq_of_equivalent_left
        (block.act_projectiveTail_valid left) (block.act_model_valid left)
        leftActEquivalent (CCL.Mat2.act block.matrix right.point)
    _ = chordalSq (CCL.Mat2.act block.matrix left.model.point)
        (CCL.Mat2.act block.matrix right.model.point) :=
      CCL.Chordal.chordalSq_eq_of_equivalent_right
        (block.act_projectiveTail_valid right) (block.act_model_valid right)
        rightActEquivalent (CCL.Mat2.act block.matrix left.model.point)
    _ ≤ (1 / 2 : Coordinate) *
        chordalSq left.model.point right.model.point :=
      block.contraction_half left.model right.model
    _ = (1 / 2 : Coordinate) * chordalSq left.point right.point := by
      rw [inputEquality]

end Block

/-- Finite completed-block semantics that retains the exact homogeneous
rescaling emitted by an integral decoder at every stage. -/
inductive ProjectiveRealizes : (blocks : List Block) → Proj → Type where
  | done (point : Proj)
      (valid : CCL.Chordal.Proj.HasNonzeroCoordinate point) :
      ProjectiveRealizes [] point
  | step {remaining : List Block} (block : Block)
      (tail : ProjectiveTail block.sector)
      (rest : ProjectiveRealizes remaining tail.point) :
      ProjectiveRealizes (block :: remaining)
        (CCL.Mat2.act block.matrix tail.point)

namespace ProjectiveRealizes

theorem valid {blocks : List Block} {point : Proj}
    (realizes : ProjectiveRealizes blocks point) :
    CCL.Chordal.Proj.HasNonzeroCoordinate point := by
  cases realizes with
  | done point pointValid => exact pointValid
  | step block tail rest => exact block.act_projectiveTail_valid tail

/-- The shrinking-cylinder theorem with all intermediate homogeneous
rescalings left exactly as the finite encoder computed them. -/
theorem chordalSq_le_half_pow
    {blocks : List Block} {left right : Proj}
    (leftRealizes : ProjectiveRealizes blocks left)
    (rightRealizes : ProjectiveRealizes blocks right) :
    chordalSq left right ≤ (1 / 2 : Coordinate) ^ blocks.length := by
  induction leftRealizes generalizing right with
  | done left leftValid =>
      cases rightRealizes with
      | done right rightValid =>
          rw [List.length_nil, pow_zero]
          exact chordalSq_le_one leftValid rightValid
  | @step remaining block leftTail leftRest inductionHypothesis =>
      cases rightRealizes with
      | step _ rightTail rightRest =>
          calc
            chordalSq (CCL.Mat2.act block.matrix leftTail.point)
                (CCL.Mat2.act block.matrix rightTail.point) ≤
                (1 / 2 : Coordinate) *
                  chordalSq leftTail.point rightTail.point :=
              block.projective_contraction_half leftTail rightTail
            _ ≤ (1 / 2 : Coordinate) *
                (1 / 2 : Coordinate) ^ remaining.length :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (inductionHypothesis rightRest) (by decide)
            _ = (1 / 2 : Coordinate) ^ (block :: remaining).length := by
              rw [List.length_cons, pow_succ]
              ring1

end ProjectiveRealizes

end CCL.Cylinder
