import CCL.Encoding.RawParser
import FTA.CCLGeometry

/-!
# Hermitian formulas for raw CCL parser states

This module connects Proposition 10.1(iv) to Section 10.1 of the finite
constructive FTA paper.  Every finite raw-parser predicate is compiled into a
finite Boolean formula whose atoms are signs of four-coefficient rational
Hermitian forms.  The compilation covers retained completed blocks, unfinished
unary runs, and all `8/4/2` incomplete-sector disjunctions.
-/

namespace FTA
namespace CCLParserGeometry

open CCL CCL.GaussianRat
open FTA.CCLGeometry

abbrev QI := CCL.GaussianRat

/-- The six exact sign tests used by finite parser formulas. -/
inductive SignTest where
  | negative
  | nonpositive
  | zero
  | nonzero
  | nonnegative
  | positive
deriving DecidableEq, Repr

namespace SignTest

def Holds : SignTest → ℚ → Prop
  | .negative, value => value < 0
  | .nonpositive, value => value ≤ 0
  | .zero, value => value = 0
  | .nonzero, value => value ≠ 0
  | .nonnegative, value => 0 ≤ value
  | .positive, value => 0 < value

instance (test : SignTest) (value : ℚ) : Decidable (test.Holds value) := by
  cases test <;> simp only [Holds] <;> infer_instance

end SignTest

/-- One sign test on a rational generalized circle or line. -/
structure Atom where
  form : HermitianForm
  sign : SignTest
deriving DecidableEq, Repr

namespace Atom

def Holds (atom : Atom) (z : QI) : Prop := atom.sign.Holds (atom.form.eval z)

instance (atom : Atom) (z : QI) : Decidable (atom.Holds z) := by
  unfold Holds
  infer_instance

end Atom

/-- Finite Boolean formulas over rational Hermitian sign atoms. -/
inductive Formula where
  | truth
  | falsity
  | atom (value : Atom)
  | and (left right : Formula)
  | or (left right : Formula)
deriving DecidableEq, Repr

namespace Formula

def Holds (formula : Formula) (z : QI) : Prop :=
  match formula with
  | .truth => True
  | .falsity => False
  | .atom value => value.Holds z
  | .and left right => left.Holds z ∧ right.Holds z
  | .or left right => left.Holds z ∨ right.Holds z

/-- Finite conjunction, with `True` for the empty list. -/
def all (formulas : List Formula) : Formula := formulas.foldr .and .truth

/-- Finite disjunction, with `False` for the empty list. -/
def any (formulas : List Formula) : Formula := formulas.foldr .or .falsity

@[simp] theorem holds_all (formulas : List Formula) (z : QI) :
    (all formulas).Holds z ↔ ∀ formula ∈ formulas, formula.Holds z := by
  induction formulas with
  | nil => simp [all, Holds]
  | cons formula formulas ih =>
      change (formula.Holds z ∧ (all formulas).Holds z) ↔
        ∀ item ∈ formula :: formulas, item.Holds z
      simp [ih]

@[simp] theorem holds_any (formulas : List Formula) (z : QI) :
    (any formulas).Holds z ↔ ∃ formula ∈ formulas, formula.Holds z := by
  induction formulas with
  | nil => simp [any, Holds]
  | cons formula formulas ih =>
      change (formula.Holds z ∨ (any formulas).Holds z) ↔
        ∃ item ∈ formula :: formulas, item.Holds z
      simp [ih]

/-- Fully executable Boolean evaluation of a compiled formula. -/
def evalBool : Formula → QI → Bool
  | .truth, _ => true
  | .falsity, _ => false
  | .atom value, z => decide (value.Holds z)
  | .and left right, z => left.evalBool z && right.evalBool z
  | .or left right, z => left.evalBool z || right.evalBool z

theorem evalBool_eq_true (formula : Formula) (z : QI) :
    formula.evalBool z = true ↔ formula.Holds z := by
  induction formula with
  | truth => simp [evalBool, Holds]
  | falsity => simp [evalBool, Holds]
  | atom value => simp [evalBool, Holds]
  | and left right ihLeft ihRight => simp [evalBool, Holds, ihLeft, ihRight]
  | or left right ihLeft ihRight => simp [evalBool, Holds, ihLeft, ihRight]

end Formula

/-- Constant rational Hermitian form. -/
def constantForm (value : ℚ) : HermitianForm := ⟨0, 0, 0, value⟩

@[simp] theorem eval_constantForm (value : ℚ) (z : QI) :
    (constantForm value).eval z = value := by
  simp [constantForm, HermitianForm.eval]

/-- `N(z) - threshold`, used by unfinished radial runs before any homography. -/
def affineNormComparisonForm (threshold : ℚ) : HermitianForm :=
  HermitianForm.sub (affineNormForm 1 0) (constantForm threshold)

@[simp] theorem eval_affineNormComparisonForm (threshold : ℚ) (z : QI) :
    (affineNormComparisonForm threshold).eval z = normSq z - threshold := by
  simp [affineNormComparisonForm, eval_affineNormForm]

/-- `2^count * N(z) - 1`, the unfinished initial-low unary predicate. -/
def lowUnaryForm (count : ℕ) : HermitianForm :=
  HermitianForm.sub
    (HermitianForm.scale ((2 : ℚ) ^ count) (affineNormForm 1 0))
    (constantForm 1)

@[simp] theorem eval_lowUnaryForm (count : ℕ) (z : QI) :
    (lowUnaryForm count).eval z = (2 : ℚ) ^ count * normSq z - 1 := by
  simp [lowUnaryForm, eval_affineNormForm]

def denominatorFormula (M : Mat2 QI) : Formula :=
  .atom ⟨affineNormForm M.c M.d, .positive⟩

theorem denominatorFormula_iff (M : Mat2 QI) (z : QI) :
    (denominatorFormula M).Holds z ↔ M.c * z + M.d ≠ 0 := by
  simp only [denominatorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
    eval_affineNormForm]
  constructor
  · intro h hzero
    rw [hzero, normSq_zero] at h
    linarith
  · exact normSq_pos

/-- Formula for the exact completed radial bracket through a homography. -/
def radialFormula (kind : RawParser.BlockKind) (exponent : ℕ)
    (M : Mat2 QI) : Formula :=
  match kind with
  | .initialHigh =>
      .and
        (.atom ⟨normComparisonForm M ((2 : ℚ) ^ exponent), .nonnegative⟩)
        (.atom ⟨normComparisonForm M ((2 : ℚ) ^ (exponent + 1)), .negative⟩)
  | .initialLow =>
      .and
        (.atom ⟨normComparisonForm M (1 / (2 : ℚ) ^ exponent), .nonnegative⟩)
        (.atom ⟨normComparisonForm M (2 / (2 : ℚ) ^ exponent), .negative⟩)
  | .loop =>
      .and
        (.atom ⟨normComparisonForm M ((2 : ℚ) ^ exponent), .positive⟩)
        (.atom ⟨normComparisonForm M ((2 : ℚ) ^ (exponent + 1)), .nonpositive⟩)

/-- Matrix for the scale applied before sector selection. -/
def normalizationMatrix (kind : RawParser.BlockKind) (exponent : ℕ) : Mat2 QI :=
  match kind with
  | .initialLow => Mat2.scale (natPow gamma exponent)
  | .initialHigh | .loop => Mat2.scale (inv (natPow gamma exponent))

/-- Compose sector normalization with the homography producing the current
pre-normalization value. -/
def normalizedMatrix (kind : RawParser.BlockKind) (exponent : ℕ)
    (M : Mat2 QI) : Mat2 QI :=
  Mat2.mul (normalizationMatrix kind exponent) M

theorem normalizedMatrix_lowerRow (kind : RawParser.BlockKind) (exponent : ℕ)
    (M : Mat2 QI) :
    (normalizedMatrix kind exponent M).c = M.c ∧
      (normalizedMatrix kind exponent M).d = M.d := by
  cases kind <;> simp [normalizedMatrix, normalizationMatrix, Mat2.mul, Mat2.scale]

theorem homographic_normalizedMatrix (kind : RawParser.BlockKind) (exponent : ℕ)
    (M : Mat2 QI) (z : QI) :
    RatBox.homographic (normalizedMatrix kind exponent M) z =
      RawParser.normalizedValue kind exponent (RatBox.homographic M z) := by
  cases kind <;>
    ext <;>
    simp only [normalizedMatrix, normalizationMatrix, RawParser.normalizedValue,
      Mat2.mul, Mat2.scale, RatBox.homographic, one_mul, zero_mul, zero_add,
      add_zero, mul_re, mul_im, add_re, add_im] <;>
    ring

/-- Exact finite formula for one sector row through a homography. -/
def sectorFormula (sector : Sector) (M : Mat2 QI) : Formula :=
  match sector with
  | .east =>
      .and (.atom ⟨realComparisonForm M (1 / 2), .nonnegative⟩)
        (.and (.atom ⟨imagComparisonForm M (-1 / 2), .positive⟩)
          (.atom ⟨imagComparisonForm M (1 / 2), .negative⟩))
  | .northEast =>
      .and (.atom ⟨realComparisonForm M (1 / 2), .nonnegative⟩)
        (.atom ⟨imagComparisonForm M (1 / 2), .nonnegative⟩)
  | .north =>
      .and (.atom ⟨realComparisonForm M (-1 / 2), .positive⟩)
        (.and (.atom ⟨realComparisonForm M (1 / 2), .negative⟩)
          (.atom ⟨imagComparisonForm M (1 / 2), .nonnegative⟩))
  | .northWest =>
      .and (.atom ⟨realComparisonForm M (-1 / 2), .nonpositive⟩)
        (.atom ⟨imagComparisonForm M (1 / 2), .nonnegative⟩)
  | .west =>
      .and (.atom ⟨realComparisonForm M (-1 / 2), .nonpositive⟩)
        (.and (.atom ⟨imagComparisonForm M (-1 / 2), .positive⟩)
          (.atom ⟨imagComparisonForm M (1 / 2), .negative⟩))
  | .southWest =>
      .and (.atom ⟨realComparisonForm M (-1 / 2), .nonpositive⟩)
        (.atom ⟨imagComparisonForm M (-1 / 2), .nonpositive⟩)
  | .south =>
      .and (.atom ⟨realComparisonForm M (-1 / 2), .positive⟩)
        (.and (.atom ⟨realComparisonForm M (1 / 2), .negative⟩)
          (.atom ⟨imagComparisonForm M (-1 / 2), .nonpositive⟩))
  | .southEast =>
      .and (.atom ⟨realComparisonForm M (1 / 2), .nonnegative⟩)
        (.atom ⟨imagComparisonForm M (-1 / 2), .nonpositive⟩)

private theorem normForm_nonnegative_iff (M : Mat2 QI) (z : QI)
    (threshold : ℚ) (hden : M.c * z + M.d ≠ 0) :
    0 ≤ (normComparisonForm M threshold).eval z ↔
      threshold ≤ normSq (RatBox.homographic M z) :=
  (norm_homographic_ge_iff M z threshold hden).symm

private theorem normForm_positive_iff (M : Mat2 QI) (z : QI)
    (threshold : ℚ) (hden : M.c * z + M.d ≠ 0) :
    0 < (normComparisonForm M threshold).eval z ↔
      threshold < normSq (RatBox.homographic M z) :=
  (norm_homographic_gt_iff M z threshold hden).symm

private theorem normForm_negative_iff (M : Mat2 QI) (z : QI)
    (threshold : ℚ) (hden : M.c * z + M.d ≠ 0) :
    (normComparisonForm M threshold).eval z < 0 ↔
      normSq (RatBox.homographic M z) < threshold :=
  (norm_homographic_lt_iff M z threshold hden).symm

private theorem normForm_nonpositive_iff (M : Mat2 QI) (z : QI)
    (threshold : ℚ) (hden : M.c * z + M.d ≠ 0) :
    (normComparisonForm M threshold).eval z ≤ 0 ↔
      normSq (RatBox.homographic M z) ≤ threshold :=
  (norm_homographic_le_iff M z threshold hden).symm

private theorem realForm_nonnegative_iff (M : Mat2 QI) (z : QI)
    (threshold : ℚ) (hden : M.c * z + M.d ≠ 0) :
    0 ≤ (realComparisonForm M threshold).eval z ↔
      threshold ≤ (RatBox.homographic M z).re :=
  (real_homographic_ge_iff M z threshold hden).symm

private theorem realForm_positive_iff (M : Mat2 QI) (z : QI)
    (threshold : ℚ) (hden : M.c * z + M.d ≠ 0) :
    0 < (realComparisonForm M threshold).eval z ↔
      threshold < (RatBox.homographic M z).re :=
  (real_homographic_gt_iff M z threshold hden).symm

private theorem realForm_negative_iff (M : Mat2 QI) (z : QI)
    (threshold : ℚ) (hden : M.c * z + M.d ≠ 0) :
    (realComparisonForm M threshold).eval z < 0 ↔
      (RatBox.homographic M z).re < threshold :=
  (real_homographic_lt_iff M z threshold hden).symm

private theorem realForm_nonpositive_iff (M : Mat2 QI) (z : QI)
    (threshold : ℚ) (hden : M.c * z + M.d ≠ 0) :
    (realComparisonForm M threshold).eval z ≤ 0 ↔
      (RatBox.homographic M z).re ≤ threshold :=
  (real_homographic_le_iff M z threshold hden).symm

private theorem imagForm_nonnegative_iff (M : Mat2 QI) (z : QI)
    (threshold : ℚ) (hden : M.c * z + M.d ≠ 0) :
    0 ≤ (imagComparisonForm M threshold).eval z ↔
      threshold ≤ (RatBox.homographic M z).im :=
  (imag_homographic_ge_iff M z threshold hden).symm

private theorem imagForm_positive_iff (M : Mat2 QI) (z : QI)
    (threshold : ℚ) (hden : M.c * z + M.d ≠ 0) :
    0 < (imagComparisonForm M threshold).eval z ↔
      threshold < (RatBox.homographic M z).im :=
  (imag_homographic_gt_iff M z threshold hden).symm

private theorem imagForm_negative_iff (M : Mat2 QI) (z : QI)
    (threshold : ℚ) (hden : M.c * z + M.d ≠ 0) :
    (imagComparisonForm M threshold).eval z < 0 ↔
      (RatBox.homographic M z).im < threshold :=
  (imag_homographic_lt_iff M z threshold hden).symm

private theorem imagForm_nonpositive_iff (M : Mat2 QI) (z : QI)
    (threshold : ℚ) (hden : M.c * z + M.d ≠ 0) :
    (imagComparisonForm M threshold).eval z ≤ 0 ↔
      (RatBox.homographic M z).im ≤ threshold :=
  (imag_homographic_le_iff M z threshold hden).symm

theorem radialFormula_iff (kind : RawParser.BlockKind) (exponent : ℕ)
    (M : Mat2 QI) (z : QI) (hden : M.c * z + M.d ≠ 0) :
    (radialFormula kind exponent M).Holds z ↔
      RawParser.radialBracket kind exponent (RatBox.homographic M z) := by
  cases kind with
  | initialHigh =>
      simp only [radialFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        RawParser.radialBracket]
      rw [normForm_nonnegative_iff M z ((2 : ℚ) ^ exponent) hden,
        normForm_negative_iff M z ((2 : ℚ) ^ (exponent + 1)) hden]
  | initialLow =>
      simp only [radialFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        RawParser.radialBracket]
      rw [normForm_nonnegative_iff M z (1 / (2 : ℚ) ^ exponent) hden,
        normForm_negative_iff M z (2 / (2 : ℚ) ^ exponent) hden]
      have hpow : 0 < (2 : ℚ) ^ exponent := pow_pos (by norm_num) _
      constructor
      · rintro ⟨hlower, hupper⟩
        constructor
        · have h := (div_le_iff₀ hpow).mp hlower
          simpa only [_root_.mul_comm] using h
        · have h := (lt_div_iff₀ hpow).mp hupper
          simpa only [_root_.mul_comm] using h
      · rintro ⟨hlower, hupper⟩
        constructor
        · apply (div_le_iff₀ hpow).2
          simpa only [_root_.mul_comm] using hlower
        · apply (lt_div_iff₀ hpow).2
          simpa only [_root_.mul_comm] using hupper
  | loop =>
      simp only [radialFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        RawParser.radialBracket]
      rw [normForm_positive_iff M z ((2 : ℚ) ^ exponent) hden,
        normForm_nonpositive_iff M z ((2 : ℚ) ^ (exponent + 1)) hden]

theorem sectorFormula_iff (sector : Sector) (M : Mat2 QI) (z : QI)
    (hden : M.c * z + M.d ≠ 0) :
    (sectorFormula sector M).Holds z ↔
      sector.Holds (RatBox.homographic M z) := by
  cases sector with
  | east =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [realForm_nonnegative_iff M z (1 / 2) hden,
        imagForm_positive_iff M z (-1 / 2) hden,
        imagForm_negative_iff M z (1 / 2) hden]
  | northEast =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [realForm_nonnegative_iff M z (1 / 2) hden,
        imagForm_nonnegative_iff M z (1 / 2) hden]
  | north =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [realForm_positive_iff M z (-1 / 2) hden,
        realForm_negative_iff M z (1 / 2) hden,
        imagForm_nonnegative_iff M z (1 / 2) hden]
  | northWest =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [realForm_nonpositive_iff M z (-1 / 2) hden,
        imagForm_nonnegative_iff M z (1 / 2) hden]
  | west =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [realForm_nonpositive_iff M z (-1 / 2) hden,
        imagForm_positive_iff M z (-1 / 2) hden,
        imagForm_negative_iff M z (1 / 2) hden]
  | southWest =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [realForm_nonpositive_iff M z (-1 / 2) hden,
        imagForm_nonpositive_iff M z (-1 / 2) hden]
  | south =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [realForm_positive_iff M z (-1 / 2) hden,
        realForm_negative_iff M z (1 / 2) hden,
        imagForm_nonpositive_iff M z (-1 / 2) hden]
  | southEast =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [realForm_nonnegative_iff M z (1 / 2) hden,
        imagForm_nonpositive_iff M z (-1 / 2) hden]

theorem normalizedSectorFormula_iff
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (M : Mat2 QI) (z : QI) (hden : M.c * z + M.d ≠ 0) :
    (sectorFormula sector (normalizedMatrix kind exponent M)).Holds z ↔
      sector.Holds
        (RawParser.normalizedValue kind exponent (RatBox.homographic M z)) := by
  have hrow := normalizedMatrix_lowerRow kind exponent M
  have hnormalizedDen :
      (normalizedMatrix kind exponent M).c * z +
          (normalizedMatrix kind exponent M).d ≠ 0 := by
    rw [hrow.1, hrow.2]
    exact hden
  rw [sectorFormula_iff sector (normalizedMatrix kind exponent M) z hnormalizedDen,
    homographic_normalizedMatrix]

/-- Compiled formula for one retained completed-block constraint. -/
def constraintFormula (constraint : RawParser.Constraint) : Formula :=
  .and (denominatorFormula constraint.matrix)
    (.and (radialFormula constraint.kind constraint.exponent constraint.matrix)
      (sectorFormula constraint.sector
        (normalizedMatrix constraint.kind constraint.exponent constraint.matrix)))

theorem constraintFormula_iff (constraint : RawParser.Constraint) (z : QI) :
    (constraintFormula constraint).Holds z ↔ constraint.Holds z := by
  constructor
  · rintro ⟨hdenFormula, hradialFormula, hsectorFormula⟩
    have hden : constraint.matrix.c * z + constraint.matrix.d ≠ 0 :=
      (denominatorFormula_iff constraint.matrix z).mp hdenFormula
    exact
      ⟨hden,
        (radialFormula_iff constraint.kind constraint.exponent
          constraint.matrix z hden).mp hradialFormula,
        (normalizedSectorFormula_iff constraint.kind constraint.exponent
          constraint.sector constraint.matrix z hden).mp hsectorFormula⟩
  · rintro ⟨hden, hradial, hsector⟩
    exact
      ⟨(denominatorFormula_iff constraint.matrix z).mpr hden,
        (radialFormula_iff constraint.kind constraint.exponent
          constraint.matrix z hden).mpr hradial,
        (normalizedSectorFormula_iff constraint.kind constraint.exponent
          constraint.sector constraint.matrix z hden).mpr hsector⟩

theorem homographic_identityMatrix (z : QI) :
    RatBox.homographic RawParser.identityMatrix z = z := by
  have hinv : inv (1 : QI) = 1 := by
    rw [← inv_eq]
    exact inv_one
  change (1 * z + 0) * inv (0 * z + 1) = z
  simp only [one_mul, add_zero, zero_mul, zero_add, hinv, mul_one]

theorem identityMatrix_denominator_ne (z : QI) :
    RawParser.identityMatrix.c * z + RawParser.identityMatrix.d ≠ 0 := by
  intro h
  have hre := congrArg GaussianRat.re h
  norm_num [RawParser.identityMatrix] at hre

/-- Normalized predicate for an unfinished sector prefix.  One- and two-bit
prefixes are written directly in terms of the two threshold comparisons;
this is equivalent to the corresponding union of complete sector rows but
keeps complementary child boundaries syntactically aligned. -/
def sectorBitsFormula (kind : RawParser.BlockKind) (exponent : ℕ) :
    RawParser.SectorBits → Formula
  | .zero =>
      Formula.any (RawParser.sectorCandidates .zero |>.map fun sector =>
        sectorFormula sector
          (normalizedMatrix kind exponent RawParser.identityMatrix))
  | .one false =>
      let M := normalizedMatrix kind exponent RawParser.identityMatrix
      .or
        (.and (.atom ⟨realComparisonForm M (1 / 2), .nonnegative⟩)
          (.atom ⟨imagComparisonForm M (-1 / 2), .positive⟩))
        (.and (.atom ⟨realComparisonForm M (1 / 2), .negative⟩)
          (.atom ⟨imagComparisonForm M (1 / 2), .nonnegative⟩))
  | .one true =>
      let M := normalizedMatrix kind exponent RawParser.identityMatrix
      let notFalse := .and
        (.or (.atom ⟨realComparisonForm M (1 / 2), .negative⟩)
          (.atom ⟨imagComparisonForm M (-1 / 2), .nonpositive⟩))
        (.or (.atom ⟨realComparisonForm M (1 / 2), .nonnegative⟩)
          (.atom ⟨imagComparisonForm M (1 / 2), .negative⟩))
      let covered := .or
        (.atom ⟨realComparisonForm M (1 / 2), .nonnegative⟩)
        (.or (.atom ⟨realComparisonForm M (-1 / 2), .nonpositive⟩)
          (.or (.atom ⟨imagComparisonForm M (1 / 2), .nonnegative⟩)
            (.atom ⟨imagComparisonForm M (-1 / 2), .nonpositive⟩)))
      .and notFalse covered
  | .two false false =>
      let M := normalizedMatrix kind exponent RawParser.identityMatrix
      .and (.atom ⟨realComparisonForm M (1 / 2), .nonnegative⟩)
        (.atom ⟨imagComparisonForm M (-1 / 2), .positive⟩)
  | .two false true =>
      let M := normalizedMatrix kind exponent RawParser.identityMatrix
      .and (.atom ⟨realComparisonForm M (1 / 2), .negative⟩)
        (.atom ⟨imagComparisonForm M (1 / 2), .nonnegative⟩)
  | .two true false =>
      let M := normalizedMatrix kind exponent RawParser.identityMatrix
      .and (.atom ⟨realComparisonForm M (-1 / 2), .nonpositive⟩)
        (.atom ⟨imagComparisonForm M (1 / 2), .negative⟩)
  | .two true true =>
      let M := normalizedMatrix kind exponent RawParser.identityMatrix
      .and (.atom ⟨realComparisonForm M (-1 / 2), .positive⟩)
        (.atom ⟨imagComparisonForm M (-1 / 2), .nonpositive⟩)

/-- Compiled formula for every possible active parser phase. -/
def activeFormula : RawParser.Phase → Formula
  | .initial => .truth
  | .highUnary count =>
      .atom ⟨affineNormComparisonForm ((2 : ℚ) ^ count), .nonnegative⟩
  | .lowUnary 0 =>
      .atom ⟨affineNormComparisonForm 2, .negative⟩
  | .lowUnary (count + 1) =>
      .atom ⟨affineNormComparisonForm
        (1 / (2 : ℚ) ^ count), .negative⟩
  | .loopUnary count =>
      .atom ⟨affineNormComparisonForm ((2 : ℚ) ^ count), .positive⟩
  | .sector kind exponent bits =>
      .and (radialFormula kind exponent RawParser.identityMatrix)
        (sectorBitsFormula kind exponent bits)

theorem sectorBitsFormula_iff
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (bits : RawParser.SectorBits) (z : QI) :
    (sectorBitsFormula kind exponent bits).Holds z ↔
      ∃ sector ∈ RawParser.sectorCandidates bits,
        sector.Holds (RawParser.normalizedValue kind exponent z) := by
  let M := normalizedMatrix kind exponent RawParser.identityMatrix
  have lowerRow := normalizedMatrix_lowerRow kind exponent
    RawParser.identityMatrix
  have denominator : M.c * z + M.d ≠ 0 := by
    rw [lowerRow.1, lowerRow.2]
    exact identityMatrix_denominator_ne z
  have homographic : RatBox.homographic M z =
      RawParser.normalizedValue kind exponent z := by
    simpa [M, homographic_identityMatrix] using
      homographic_normalizedMatrix kind exponent RawParser.identityMatrix z
  cases bits with
  | zero =>
      simp only [sectorBitsFormula, Formula.holds_any, List.mem_map]
      constructor
      · rintro ⟨formula, ⟨sector, member, rfl⟩, holds⟩
        exact ⟨sector, member,
          (by
            rw [sectorFormula_iff sector M z denominator, homographic] at holds
            exact holds)⟩
      · rintro ⟨sector, member, holds⟩
        refine ⟨sectorFormula sector M, ⟨sector, member, rfl⟩, ?_⟩
        rw [sectorFormula_iff sector M z denominator, homographic]
        exact holds
  | one first =>
      cases first <;>
        simp only [sectorBitsFormula, Formula.Holds, Atom.Holds,
          SignTest.Holds]
      · rw [realForm_nonnegative_iff M z (1 / 2) denominator,
          imagForm_positive_iff M z (-1 / 2) denominator,
          realForm_negative_iff M z (1 / 2) denominator,
          imagForm_nonnegative_iff M z (1 / 2) denominator,
          homographic]
        simp only [RawParser.sectorCandidates_one_false, List.mem_cons,
          Sector.Holds]
        constructor <;> rintro holds
        · rcases holds with ⟨real, imag⟩ | ⟨real, imag⟩
          · by_cases high : 1 / 2 ≤
                (RawParser.normalizedValue kind exponent z).im
            · exact ⟨Sector.northEast, by simp, real, high⟩
            · exact ⟨Sector.east, by simp, real, imag, by linarith⟩
          · by_cases left :
                (RawParser.normalizedValue kind exponent z).re ≤ -1 / 2
            · exact ⟨Sector.northWest, by simp, left, imag⟩
            · exact ⟨Sector.north, by simp, by linarith, real, imag⟩
        · rcases holds with ⟨sector, member, sectorHolds⟩
          simp only [List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl
          · exact .inl ⟨sectorHolds.1, sectorHolds.2.1⟩
          · exact .inl ⟨sectorHolds.1, by linarith [sectorHolds.2]⟩
          · exact .inr ⟨sectorHolds.2.1, sectorHolds.2.2⟩
          · exact .inr ⟨by linarith [sectorHolds.1], sectorHolds.2⟩
      · rw [realForm_negative_iff M z (1 / 2) denominator,
          imagForm_nonpositive_iff M z (-1 / 2) denominator,
          realForm_nonnegative_iff M z (1 / 2) denominator,
          imagForm_negative_iff M z (1 / 2) denominator,
          realForm_nonpositive_iff M z (-1 / 2) denominator,
          imagForm_nonnegative_iff M z (1 / 2) denominator,
          homographic]
        simp only [RawParser.sectorCandidates_one_true, List.mem_cons,
          Sector.Holds]
        constructor <;> rintro holds
        · rcases holds with ⟨⟨notFirst, notSecond⟩, covered⟩
          by_cases left : (RawParser.normalizedValue kind exponent z).re ≤
              -1 / 2
          · have imagLt : (RawParser.normalizedValue kind exponent z).im <
                1 / 2 := by
              rcases notSecond with realRight | imagLt
              · linarith
              · exact imagLt
            by_cases low : (RawParser.normalizedValue kind exponent z).im ≤
                -1 / 2
            · exact ⟨Sector.southWest, by simp, left, low⟩
            · exact ⟨Sector.west, by simp, left, by linarith, imagLt⟩
          · have realLeft : -1 / 2 <
                (RawParser.normalizedValue kind exponent z).re := by
              linarith
            have low : (RawParser.normalizedValue kind exponent z).im ≤
                -1 / 2 := by
              rcases notFirst with realLt | low
              · rcases notSecond with realRight | imagLt
                · linarith
                · rcases covered with realRight | realFarLeft | imagHigh | low
                  · linarith
                  · linarith
                  · linarith
                  · exact low
              · exact low
            by_cases right : 1 / 2 ≤
                (RawParser.normalizedValue kind exponent z).re
            · exact ⟨Sector.southEast, by simp, right, low⟩
            · exact ⟨Sector.south, by simp, realLeft, by linarith, low⟩
        · rcases holds with ⟨sector, member, sectorHolds⟩
          simp only [List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl
          · exact ⟨⟨Or.inl (by linarith [sectorHolds.1]),
                Or.inr sectorHolds.2.2⟩,
              Or.inr (Or.inl sectorHolds.1)⟩
          · exact ⟨⟨Or.inr sectorHolds.2,
                Or.inr (by linarith [sectorHolds.2])⟩,
              Or.inr (Or.inl sectorHolds.1)⟩
          · exact ⟨⟨Or.inr sectorHolds.2.2,
                Or.inr (by linarith [sectorHolds.2.2])⟩,
              Or.inr (Or.inr (Or.inr sectorHolds.2.2))⟩
          · exact ⟨⟨Or.inr sectorHolds.2,
                Or.inl sectorHolds.1⟩,
              Or.inl sectorHolds.1⟩
  | two first second =>
      cases first <;> cases second <;>
        simp only [sectorBitsFormula, Formula.Holds, Atom.Holds,
          SignTest.Holds]
      · rw [realForm_nonnegative_iff M z (1 / 2) denominator,
          imagForm_positive_iff M z (-1 / 2) denominator, homographic]
        simp only [RawParser.sectorCandidates_two_false_false, List.mem_cons,
          Sector.Holds]
        constructor <;> rintro holds
        · by_cases high : 1 / 2 ≤
              (RawParser.normalizedValue kind exponent z).im
          · exact ⟨Sector.northEast, by simp, holds.1, high⟩
          · exact ⟨Sector.east, by simp, holds.1, holds.2, by linarith⟩
        · rcases holds with ⟨sector, member, sectorHolds⟩
          simp only [List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨sectorHolds.1, sectorHolds.2.1⟩
          · exact ⟨sectorHolds.1, by linarith [sectorHolds.2]⟩
      · rw [realForm_negative_iff M z (1 / 2) denominator,
          imagForm_nonnegative_iff M z (1 / 2) denominator, homographic]
        simp only [RawParser.sectorCandidates_two_false_true, List.mem_cons,
          Sector.Holds]
        constructor <;> rintro holds
        · by_cases left : (RawParser.normalizedValue kind exponent z).re ≤
              -1 / 2
          · exact ⟨Sector.northWest, by simp, left, holds.2⟩
          · exact ⟨Sector.north, by simp, by linarith, holds.1, holds.2⟩
        · rcases holds with ⟨sector, member, sectorHolds⟩
          simp only [List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨sectorHolds.2.1, sectorHolds.2.2⟩
          · exact ⟨by linarith [sectorHolds.1], sectorHolds.2⟩
      · rw [realForm_nonpositive_iff M z (-1 / 2) denominator,
          imagForm_negative_iff M z (1 / 2) denominator, homographic]
        simp only [RawParser.sectorCandidates_two_true_false, List.mem_cons,
          Sector.Holds]
        constructor <;> rintro holds
        · by_cases low : (RawParser.normalizedValue kind exponent z).im ≤
              -1 / 2
          · exact ⟨Sector.southWest, by simp, holds.1, low⟩
          · exact ⟨Sector.west, by simp, holds.1, by linarith, holds.2⟩
        · rcases holds with ⟨sector, member, sectorHolds⟩
          simp only [List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨sectorHolds.1, sectorHolds.2.2⟩
          · exact ⟨sectorHolds.1, by linarith [sectorHolds.2]⟩
      · rw [realForm_positive_iff M z (-1 / 2) denominator,
          imagForm_nonpositive_iff M z (-1 / 2) denominator, homographic]
        simp only [RawParser.sectorCandidates_two_true_true, List.mem_cons,
          Sector.Holds]
        constructor <;> rintro holds
        · by_cases right : 1 / 2 ≤
              (RawParser.normalizedValue kind exponent z).re
          · exact ⟨Sector.southEast, by simp, right, holds.2⟩
          · exact ⟨Sector.south, by simp, holds.1, by linarith, holds.2⟩
        · rcases holds with ⟨sector, member, sectorHolds⟩
          simp only [List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨sectorHolds.1, sectorHolds.2.2⟩
          · exact ⟨by linarith [sectorHolds.1], sectorHolds.2⟩

theorem activeFormula_iff (phase : RawParser.Phase) (z : QI) :
    (activeFormula phase).Holds z ↔ RawParser.activeHolds phase z := by
  cases phase with
  | initial => simp [activeFormula, Formula.Holds, RawParser.activeHolds]
  | highUnary count =>
      simp [activeFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        RawParser.activeHolds, sub_nonneg]
  | lowUnary count =>
      cases count with
      | zero =>
          simp [activeFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
            RawParser.activeHolds, sub_neg]
      | succ count =>
          simp only [activeFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
            RawParser.activeHolds, eval_affineNormComparisonForm]
          have powerPositive : 0 < (2 : ℚ) ^ count := pow_pos (by norm_num) _
          constructor
          · intro comparison
            have divided := sub_neg.mp comparison
            have scaled := (lt_div_iff₀ powerPositive).mp divided
            calc
              (2 : ℚ) ^ count * normSq z =
                  normSq z * (2 : ℚ) ^ count := _root_.mul_comm _ _
              _ < 1 := scaled
          · intro scaled
            apply sub_neg.mpr
            apply (lt_div_iff₀ powerPositive).mpr
            calc
              normSq z * (2 : ℚ) ^ count =
                  (2 : ℚ) ^ count * normSq z := _root_.mul_comm _ _
              _ < 1 := scaled
  | loopUnary count =>
      simp [activeFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        RawParser.activeHolds, sub_pos]
  | sector kind exponent bits =>
      have hden := identityMatrix_denominator_ne z
      have hradial :
          (radialFormula kind exponent RawParser.identityMatrix).Holds z ↔
            RawParser.radialBracket kind exponent z := by
        simpa only [homographic_identityMatrix] using
          radialFormula_iff kind exponent RawParser.identityMatrix z hden
      simp only [activeFormula, Formula.Holds, RawParser.activeHolds]
      exact and_congr hradial (sectorBitsFormula_iff kind exponent bits z)

/-- Hermitian formula for a complete finite raw-parser state. -/
def stateFormula (state : RawParser.State) : Formula :=
  .and (Formula.all (state.history.map constraintFormula))
    (activeFormula state.phase)

theorem stateFormula_iff (state : RawParser.State) (z : QI) :
    (stateFormula state).Holds z ↔ state.Holds z := by
  constructor
  · rintro ⟨hhistory, hactive⟩
    constructor
    · intro constraint hconstraint
      apply (constraintFormula_iff constraint z).mp
      apply (Formula.holds_all _ z).mp hhistory
      exact List.mem_map.mpr ⟨constraint, hconstraint, rfl⟩
    · exact (activeFormula_iff state.phase z).mp hactive
  · rintro ⟨hhistory, hactive⟩
    constructor
    · apply (Formula.holds_all _ z).mpr
      intro formula hformula
      rcases List.mem_map.mp hformula with ⟨constraint, hconstraint, rfl⟩
      exact (constraintFormula_iff constraint z).mpr
        (hhistory constraint hconstraint)
    · exact (activeFormula_iff state.phase z).mpr hactive

/-- Compile any finite raw word by first running the deterministic parser. -/
def parseFormula (word : Prefix.Word) : Formula :=
  stateFormula (RawParser.parse word)

theorem parseFormula_iff (word : Prefix.Word) (z : QI) :
    (parseFormula word).Holds z ↔ (RawParser.parse word).Holds z :=
  stateFormula_iff (RawParser.parse word) z

/-- Executable Boolean form of the compiled arbitrary-prefix predicate. -/
def parseFormulaBool (word : Prefix.Word) (z : QI) : Bool :=
  (parseFormula word).evalBool z

theorem parseFormulaBool_eq_true (word : Prefix.Word) (z : QI) :
    parseFormulaBool word z = true ↔ (RawParser.parse word).Holds z := by
  rw [parseFormulaBool, Formula.evalBool_eq_true, parseFormula_iff]

end CCLParserGeometry
end FTA
