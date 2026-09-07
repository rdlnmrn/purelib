import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Pullback

/-!
# Finite Hermitian formulas for raw CCL parser states

Every predicate in an arbitrary finite raw-parser state is compiled into a
finite Boolean formula whose atoms are signs of four-coefficient rational
Hermitian forms.  Unfinished sector prefixes use the direct finite
disjunction of their `8/4/2` candidate rows.  This keeps the implementation
small while preserving the exact weak/strict boundary convention.
-/

namespace CCL.CCLFormula

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev Sector := CCL.Sectors.Sector
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev Word := List Bool

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Sectors
open CCL.RawParser
open CCL.CCLGeometry
open CCL.CCLPullback

/-- Exact sign tests used by finite parser formulas. -/
inductive SignTest where
  | negative
  | nonpositive
  | zero
  | nonzero
  | nonnegative
  | positive
deriving DecidableEq, Repr

namespace SignTest

def Holds : SignTest → Coordinate → Prop
  | .negative, value => value < 0
  | .nonpositive, value => value ≤ 0
  | .zero, value => value = 0
  | .nonzero, value => value ≠ 0
  | .nonnegative, value => 0 ≤ value
  | .positive, value => 0 < value

instance (test : SignTest) (value : Coordinate) :
    Decidable (test.Holds value) := by
  cases test <;> simp only [Holds] <;> infer_instance

/-- Multiplication by an explicitly positive rational preserves all six sign
tests, including equality and disequality. -/
theorem holds_mul_pos_iff
    (test : SignTest) (factor value : Coordinate) (positive : 0 < factor) :
    test.Holds (factor * value) ↔ test.Holds value := by
  have identity : factor * value = factor * (value - 0) := by ring1
  cases test with
  | negative =>
      exact (compare_lt_iff positive identity).symm
  | nonpositive =>
      exact (compare_le_iff positive identity).symm
  | zero =>
      exact (compare_eq_iff positive identity).symm
  | nonzero =>
      exact not_congr (compare_eq_iff positive identity).symm
  | nonnegative =>
      exact (compare_ge_iff positive identity).symm
  | positive =>
      exact (compare_gt_iff positive identity).symm

end SignTest

/-- One sign test on a generalized-circle form. -/
structure Atom where
  form : HermitianForm
  sign : SignTest
deriving DecidableEq

namespace Atom

def Holds (atom : Atom) (value : Gaussian) : Prop :=
  atom.sign.Holds (atom.form.eval value)

instance (atom : Atom) (value : Gaussian) : Decidable (atom.Holds value) := by
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
deriving DecidableEq

namespace Formula

def Holds : Formula → Gaussian → Prop
  | Formula.truth, _ => True
  | Formula.falsity, _ => False
  | Formula.atom testAtom, value => testAtom.Holds value
  | Formula.and left right, value => left.Holds value ∧ right.Holds value
  | Formula.or left right, value => left.Holds value ∨ right.Holds value

def all : List Formula → Formula
  | [] => Formula.truth
  | formula :: formulas => Formula.and formula (all formulas)

def any : List Formula → Formula
  | [] => Formula.falsity
  | formula :: formulas => Formula.or formula (any formulas)

@[simp] theorem holds_all (formulas : List Formula) (value : Gaussian) :
    (all formulas).Holds value ↔
      ∀ formula ∈ formulas, formula.Holds value := by
  induction formulas with
  | nil =>
      constructor
      · intro _ formula member
        simp only [List.not_mem_nil] at member
      · intro _
        exact True.intro
  | cons formula formulas inductionHypothesis =>
      change (formula.Holds value ∧ (all formulas).Holds value) ↔
        ∀ item ∈ formula :: formulas, item.Holds value
      constructor
      · rintro ⟨headHolds, tailHolds⟩ item member
        rcases List.mem_cons.mp member with identity | tailMember
        · subst item
          exact headHolds
        · exact (inductionHypothesis.mp tailHolds) item tailMember
      · intro everyHolds
        exact
          ⟨everyHolds formula List.mem_cons_self,
            inductionHypothesis.mpr (fun item tailMember =>
              everyHolds item (List.mem_cons_of_mem formula tailMember))⟩

@[simp] theorem holds_any (formulas : List Formula) (value : Gaussian) :
    (any formulas).Holds value ↔
      ∃ formula ∈ formulas, formula.Holds value := by
  induction formulas with
  | nil =>
      constructor
      · intro falsehood
        exact falsehood.elim
      · rintro ⟨formula, member, _⟩
        simp only [List.not_mem_nil] at member
  | cons formula formulas inductionHypothesis =>
      change (formula.Holds value ∨ (any formulas).Holds value) ↔
        ∃ item ∈ formula :: formulas, item.Holds value
      constructor
      · intro holds
        rcases holds with headHolds | tailHolds
        · exact ⟨formula, List.mem_cons_self, headHolds⟩
        · rcases inductionHypothesis.mp tailHolds with
            ⟨item, member, itemHolds⟩
          exact
            ⟨item, List.mem_cons_of_mem formula member, itemHolds⟩
      · rintro ⟨item, member, itemHolds⟩
        rcases List.mem_cons.mp member with head | tail
        · subst item
          exact Or.inl itemHolds
        · exact
            Or.inr (inductionHypothesis.mpr ⟨item, tail, itemHolds⟩)

def evalBool : Formula → Gaussian → Bool
  | Formula.truth, _ => true
  | Formula.falsity, _ => false
  | Formula.atom testAtom, value => decide (testAtom.Holds value)
  | Formula.and left right, value => left.evalBool value && right.evalBool value
  | Formula.or left right, value => left.evalBool value || right.evalBool value

theorem evalBool_eq_true (formula : Formula) (value : Gaussian) :
    formula.evalBool value = true ↔ formula.Holds value := by
  induction formula with
  | truth => simp [evalBool, Holds]
  | falsity => simp [evalBool, Holds]
  | atom atom => simp [evalBool, Holds]
  | and left right leftHypothesis rightHypothesis =>
      simp [evalBool, Holds, leftHypothesis, rightHypothesis]
  | or left right leftHypothesis rightHypothesis =>
      simp [evalBool, Holds, leftHypothesis, rightHypothesis]

end Formula

def constantForm (value : Coordinate) : HermitianForm := ⟨0, 0, 0, value⟩

@[simp] theorem eval_constantForm (constant : Coordinate) (value : Gaussian) :
    (constantForm constant).eval value = constant := by
  simp only [constantForm, HermitianForm.eval]
  ring1

/-- Form evaluating to `N(z) - threshold`. -/
def affineNormComparisonForm (threshold : Coordinate) : HermitianForm :=
  (affineNormForm 1 0).sub (constantForm threshold)

@[simp] theorem eval_affineNormComparisonForm
    (threshold : Coordinate) (value : Gaussian) :
    (affineNormComparisonForm threshold).eval value =
      normSq value - threshold := by
  rw [affineNormComparisonForm, HermitianForm.eval_sub,
    eval_affineNormForm, eval_constantForm,
    RFAP.ConstructiveGaussian.Gaussian.one_mul,
    RFAP.ConstructiveGaussian.Gaussian.add_zero]

/-- Form evaluating to `2^count * N(z) - threshold`. -/
def scaledNormComparisonForm (count : Nat) (threshold : Coordinate) :
    HermitianForm :=
  (affineNormForm 1 0).scale ((2 : Coordinate) ^ count) |>.sub
    (constantForm threshold)

@[simp] theorem eval_scaledNormComparisonForm
    (count : Nat) (threshold : Coordinate) (value : Gaussian) :
    (scaledNormComparisonForm count threshold).eval value =
      (2 : Coordinate) ^ count * normSq value - threshold := by
  rw [scaledNormComparisonForm, HermitianForm.eval_sub,
    HermitianForm.eval_scale, eval_affineNormForm, eval_constantForm,
    RFAP.ConstructiveGaussian.Gaussian.one_mul,
    RFAP.ConstructiveGaussian.Gaussian.add_zero]

theorem sub_nonnegative_iff {value threshold : Coordinate} :
    0 ≤ value - threshold ↔ threshold ≤ value := by
  constructor
  · exact sub_nonneg.mp
  · exact RFAP.ConstructiveFraction.sub_nonneg_direct

theorem sub_nonpositive_iff {value threshold : Coordinate} :
    value - threshold ≤ 0 ↔ value ≤ threshold :=
  sub_nonpos

theorem sub_negative_iff {value threshold : Coordinate} :
    value - threshold < 0 ↔ value < threshold := by
  constructor
  · exact RFAP.ConstructiveFraction.lt_of_sub_neg_direct
  · exact RFAP.ConstructiveFraction.sub_neg_direct

theorem sub_positive_iff {value threshold : Coordinate} :
    0 < value - threshold ↔ threshold < value := by
  constructor
  · exact RFAP.ConstructiveFraction.lt_of_sub_pos_direct
  · exact RFAP.ConstructiveFraction.sub_pos_direct

def denominatorFormula (matrix : Mat2) : Formula :=
  .atom ⟨affineNormForm matrix.c matrix.d, .positive⟩

theorem denominatorFormula_iff (matrix : Mat2) (value : Gaussian) :
    (denominatorFormula matrix).Holds value ↔
      denominator matrix value ≠ 0 := by
  simp only [denominatorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
    eval_affineNormForm, denominator]
  constructor
  · intro positive zero
    rw [zero, normSq_zero] at positive
    exact (lt_irrefl (0 : Coordinate) positive).elim
  · exact normSq_pos

/-- Pull a tail-coordinate formula atom back through a matrix. -/
def pullbackAtom (matrix : Mat2) (atom : Atom) : Atom :=
  ⟨pullbackForm matrix atom.form, atom.sign⟩

def Formula.pullback (matrix : Mat2) : Formula → Formula
  | Formula.truth => Formula.truth
  | Formula.falsity => Formula.falsity
  | Formula.atom testAtom => Formula.atom (pullbackAtom matrix testAtom)
  | Formula.and left right =>
      Formula.and (left.pullback matrix) (right.pullback matrix)
  | Formula.or left right =>
      Formula.or (left.pullback matrix) (right.pullback matrix)

theorem Formula.pullback_iff
    (matrix : Mat2) (formula : Formula) (value : Gaussian)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (formula.pullback matrix).Holds value ↔
      formula.Holds (homographic matrix value) := by
  induction formula with
  | truth => simp [Formula.pullback, Formula.Holds]
  | falsity => simp [Formula.pullback, Formula.Holds]
  | atom atom =>
      simp only [Formula.pullback, Formula.Holds, Atom.Holds, pullbackAtom,
        eval_pullbackForm matrix atom.form value denominatorNonzero]
      exact SignTest.holds_mul_pos_iff atom.sign
        (normSq (denominator matrix value))
        (atom.form.eval (homographic matrix value))
        (normSq_pos denominatorNonzero)
  | and left right leftHypothesis rightHypothesis =>
      simp only [Formula.pullback, Formula.Holds]
      exact and_congr leftHypothesis rightHypothesis
  | or left right leftHypothesis rightHypothesis =>
      simp only [Formula.pullback, Formula.Holds]
      exact or_congr leftHypothesis rightHypothesis

/-- Formula for one completed radial bracket through a homography. -/
def radialFormula (kind : BlockKind) (exponent : Nat) (matrix : Mat2) :
    Formula :=
  let tailFormula : Formula := match kind with
    | .initialHigh =>
        Formula.and
          (Formula.atom ⟨affineNormComparisonForm ((2 : Coordinate) ^ exponent),
            .nonnegative⟩)
          (Formula.atom ⟨affineNormComparisonForm
            ((2 : Coordinate) ^ (exponent + 1)), .negative⟩)
    | .initialLow =>
        Formula.and
          (Formula.atom ⟨scaledNormComparisonForm exponent 1, .nonnegative⟩)
          (Formula.atom ⟨scaledNormComparisonForm exponent 2, .negative⟩)
    | .loop =>
        Formula.and
          (Formula.atom ⟨affineNormComparisonForm ((2 : Coordinate) ^ exponent),
            .positive⟩)
          (Formula.atom ⟨affineNormComparisonForm
            ((2 : Coordinate) ^ (exponent + 1)), .nonpositive⟩)
  Formula.pullback matrix tailFormula

theorem radialFormula_iff
    (kind : BlockKind) (exponent : Nat) (matrix : Mat2) (value : Gaussian)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (radialFormula kind exponent matrix).Holds value ↔
      radialBracket kind exponent (homographic matrix value) := by
  unfold radialFormula
  rw [Formula.pullback_iff matrix _ value denominatorNonzero]
  cases kind with
  | initialHigh =>
      simp only [Formula.Holds, Atom.Holds, SignTest.Holds, radialBracket,
        eval_affineNormComparisonForm]
      rw [sub_nonnegative_iff, sub_negative_iff]
  | initialLow =>
      simp only [Formula.Holds, Atom.Holds, SignTest.Holds, radialBracket,
        eval_scaledNormComparisonForm]
      rw [sub_nonnegative_iff, sub_negative_iff]
  | loop =>
      simp only [Formula.Holds, Atom.Holds, SignTest.Holds, radialBracket,
        eval_affineNormComparisonForm]
      rw [sub_positive_iff, sub_nonpositive_iff]

/-- Matrix for the scale applied before sector selection. -/
def normalizationMatrix (kind : BlockKind) (exponent : Nat) : Mat2 :=
  match kind with
  | .initialLow => CCL.Mat2.scale (natPow gamma exponent)
  | .initialHigh | .loop => CCL.Mat2.scale (natPow gamma exponent)⁻¹

theorem normalizationMatrix_det_ne (kind : BlockKind) (exponent : Nat) :
    CCL.CCLPullback.determinant
      (normalizationMatrix kind exponent) ≠ 0 := by
  have gammaNonzero : gamma ≠ 0 := by decide
  have powerNonzero : natPow gamma exponent ≠ 0 :=
    natPow_ne_zero_direct gamma gammaNonzero exponent
  cases kind with
  | initialLow =>
      simpa only [normalizationMatrix, CCL.Mat2.scale,
        CCL.CCLPullback.determinant,
        CCL.Chordal.Mat2.det,
        RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.sub_zero] using powerNonzero
  | initialHigh | loop =>
      have inverseNonzero : (natPow gamma exponent)⁻¹ ≠ 0 := by
        simpa only [inv_eq] using inv_ne_zero_direct powerNonzero
      simpa only [normalizationMatrix, CCL.Mat2.scale,
        CCL.CCLPullback.determinant,
        CCL.Chordal.Mat2.det,
        RFAP.ConstructiveGaussian.Gaussian.mul_one,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.sub_zero] using inverseNonzero

def normalizedMatrix (kind : BlockKind) (exponent : Nat)
    (matrix : Mat2) : Mat2 :=
  CCL.Mat2.mul (normalizationMatrix kind exponent) matrix

theorem normalizedMatrix_lowerRow
    (kind : BlockKind) (exponent : Nat) (matrix : Mat2) :
    (normalizedMatrix kind exponent matrix).c = matrix.c ∧
      (normalizedMatrix kind exponent matrix).d = matrix.d := by
  cases kind <;> constructor <;>
    simp only [normalizedMatrix, normalizationMatrix, CCL.Mat2.mul,
      CCL.Mat2.scale, RFAP.ConstructiveGaussian.Gaussian.zero_mul,
      RFAP.ConstructiveGaussian.Gaussian.one_mul,
      RFAP.ConstructiveGaussian.Gaussian.zero_add]

theorem homographic_normalizedMatrix
    (kind : BlockKind) (exponent : Nat) (matrix : Mat2) (value : Gaussian) :
    homographic (normalizedMatrix kind exponent matrix) value =
      normalizedValue kind exponent (homographic matrix value) := by
  cases kind with
  | initialHigh =>
      unfold normalizedMatrix normalizationMatrix normalizedValue homographic
        numerator denominator
      simp only [CCL.Mat2.mul, CCL.Mat2.scale,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.one_mul,
        RFAP.ConstructiveGaussian.Gaussian.zero_add,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc
        (natPow gamma exponent)⁻¹ matrix.a value]
      calc
        ((natPow gamma exponent)⁻¹ * (matrix.a * value) +
            (natPow gamma exponent)⁻¹ * matrix.b) *
              (matrix.c * value + matrix.d)⁻¹ =
            ((natPow gamma exponent)⁻¹ *
              (matrix.a * value + matrix.b)) *
                (matrix.c * value + matrix.d)⁻¹ := by
              rw [RFAP.ConstructiveGaussian.Gaussian.left_distrib]
        _ = (natPow gamma exponent)⁻¹ *
              ((matrix.a * value + matrix.b) *
                (matrix.c * value + matrix.d)⁻¹) :=
            RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
        _ = ((matrix.a * value + matrix.b) *
                (matrix.c * value + matrix.d)⁻¹) *
              (natPow gamma exponent)⁻¹ :=
            RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
  | initialLow =>
      unfold normalizedMatrix normalizationMatrix normalizedValue homographic
        numerator denominator
      simp only [CCL.Mat2.mul, CCL.Mat2.scale,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.one_mul,
        RFAP.ConstructiveGaussian.Gaussian.zero_add,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc
        (natPow gamma exponent) matrix.a value]
      calc
        (natPow gamma exponent * (matrix.a * value) +
            natPow gamma exponent * matrix.b) *
              (matrix.c * value + matrix.d)⁻¹ =
            (natPow gamma exponent *
              (matrix.a * value + matrix.b)) *
                (matrix.c * value + matrix.d)⁻¹ := by
              rw [RFAP.ConstructiveGaussian.Gaussian.left_distrib]
        _ = natPow gamma exponent *
              ((matrix.a * value + matrix.b) *
                (matrix.c * value + matrix.d)⁻¹) :=
            RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
  | loop =>
      unfold normalizedMatrix normalizationMatrix normalizedValue homographic
        numerator denominator
      simp only [CCL.Mat2.mul, CCL.Mat2.scale,
        RFAP.ConstructiveGaussian.Gaussian.zero_mul,
        RFAP.ConstructiveGaussian.Gaussian.one_mul,
        RFAP.ConstructiveGaussian.Gaussian.zero_add,
        RFAP.ConstructiveGaussian.Gaussian.add_zero]
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc
        (natPow gamma exponent)⁻¹ matrix.a value]
      calc
        ((natPow gamma exponent)⁻¹ * (matrix.a * value) +
            (natPow gamma exponent)⁻¹ * matrix.b) *
              (matrix.c * value + matrix.d)⁻¹ =
            ((natPow gamma exponent)⁻¹ *
              (matrix.a * value + matrix.b)) *
                (matrix.c * value + matrix.d)⁻¹ := by
              rw [RFAP.ConstructiveGaussian.Gaussian.left_distrib]
        _ = (natPow gamma exponent)⁻¹ *
              ((matrix.a * value + matrix.b) *
                (matrix.c * value + matrix.d)⁻¹) :=
            RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
        _ = ((matrix.a * value + matrix.b) *
                (matrix.c * value + matrix.d)⁻¹) *
              (natPow gamma exponent)⁻¹ :=
            RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _

/-- Exact finite formula for one sector row through a homography. -/
def sectorFormula (sector : Sector) (matrix : Mat2) : Formula :=
  match sector with
  | .east =>
      .and (.atom ⟨realComparisonForm matrix (1 / 2), .nonnegative⟩)
        (.and (.atom ⟨imagComparisonForm matrix (-1 / 2), .positive⟩)
          (.atom ⟨imagComparisonForm matrix (1 / 2), .negative⟩))
  | .northEast =>
      .and (.atom ⟨realComparisonForm matrix (1 / 2), .nonnegative⟩)
        (.atom ⟨imagComparisonForm matrix (1 / 2), .nonnegative⟩)
  | .north =>
      .and (.atom ⟨realComparisonForm matrix (-1 / 2), .positive⟩)
        (.and (.atom ⟨realComparisonForm matrix (1 / 2), .negative⟩)
          (.atom ⟨imagComparisonForm matrix (1 / 2), .nonnegative⟩))
  | .northWest =>
      .and (.atom ⟨realComparisonForm matrix (-1 / 2), .nonpositive⟩)
        (.atom ⟨imagComparisonForm matrix (1 / 2), .nonnegative⟩)
  | .west =>
      .and (.atom ⟨realComparisonForm matrix (-1 / 2), .nonpositive⟩)
        (.and (.atom ⟨imagComparisonForm matrix (-1 / 2), .positive⟩)
          (.atom ⟨imagComparisonForm matrix (1 / 2), .negative⟩))
  | .southWest =>
      .and (.atom ⟨realComparisonForm matrix (-1 / 2), .nonpositive⟩)
        (.atom ⟨imagComparisonForm matrix (-1 / 2), .nonpositive⟩)
  | .south =>
      .and (.atom ⟨realComparisonForm matrix (-1 / 2), .positive⟩)
        (.and (.atom ⟨realComparisonForm matrix (1 / 2), .negative⟩)
          (.atom ⟨imagComparisonForm matrix (-1 / 2), .nonpositive⟩))
  | .southEast =>
      .and (.atom ⟨realComparisonForm matrix (1 / 2), .nonnegative⟩)
        (.atom ⟨imagComparisonForm matrix (-1 / 2), .nonpositive⟩)

theorem sectorFormula_iff
    (sector : Sector) (matrix : Mat2) (value : Gaussian)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (sectorFormula sector matrix).Holds value ↔
      sector.Holds (homographic matrix value) := by
  cases sector with
  | east =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [← real_homographic_ge_iff matrix value (1 / 2)
          denominatorNonzero,
        ← imag_homographic_gt_iff matrix value (-1 / 2)
          denominatorNonzero,
        ← imag_homographic_lt_iff matrix value (1 / 2)
          denominatorNonzero]
  | northEast =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [← real_homographic_ge_iff matrix value (1 / 2)
          denominatorNonzero,
        ← imag_homographic_ge_iff matrix value (1 / 2)
          denominatorNonzero]
  | north =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [← real_homographic_gt_iff matrix value (-1 / 2)
          denominatorNonzero,
        ← real_homographic_lt_iff matrix value (1 / 2)
          denominatorNonzero,
        ← imag_homographic_ge_iff matrix value (1 / 2)
          denominatorNonzero]
  | northWest =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [← real_homographic_le_iff matrix value (-1 / 2)
          denominatorNonzero,
        ← imag_homographic_ge_iff matrix value (1 / 2)
          denominatorNonzero]
  | west =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [← real_homographic_le_iff matrix value (-1 / 2)
          denominatorNonzero,
        ← imag_homographic_gt_iff matrix value (-1 / 2)
          denominatorNonzero,
        ← imag_homographic_lt_iff matrix value (1 / 2)
          denominatorNonzero]
  | southWest =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [← real_homographic_le_iff matrix value (-1 / 2)
          denominatorNonzero,
        ← imag_homographic_le_iff matrix value (-1 / 2)
          denominatorNonzero]
  | south =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [← real_homographic_gt_iff matrix value (-1 / 2)
          denominatorNonzero,
        ← real_homographic_lt_iff matrix value (1 / 2)
          denominatorNonzero,
        ← imag_homographic_le_iff matrix value (-1 / 2)
          denominatorNonzero]
  | southEast =>
      simp only [sectorFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        Sector.Holds]
      rw [← real_homographic_ge_iff matrix value (1 / 2)
          denominatorNonzero,
        ← imag_homographic_le_iff matrix value (-1 / 2)
          denominatorNonzero]

theorem normalizedSectorFormula_iff
    (kind : BlockKind) (exponent : Nat) (sector : Sector)
    (matrix : Mat2) (value : Gaussian)
    (denominatorNonzero : denominator matrix value ≠ 0) :
    (sectorFormula sector (normalizedMatrix kind exponent matrix)).Holds
        value ↔
      sector.Holds
        (normalizedValue kind exponent (homographic matrix value)) := by
  have lowerRow := normalizedMatrix_lowerRow kind exponent matrix
  have normalizedDenominator :
      denominator (normalizedMatrix kind exponent matrix) value ≠ 0 := by
    unfold denominator
    rw [lowerRow.1, lowerRow.2]
    exact denominatorNonzero
  rw [sectorFormula_iff sector _ value normalizedDenominator,
    homographic_normalizedMatrix]

/-- An unfinished sector prefix is the finite disjunction of its admitted
complete rows. -/
def sectorBitsFormula
    (kind : BlockKind) (exponent : Nat) (bits : SectorBits) : Formula :=
  Formula.any ((sectorCandidates bits).map fun sector =>
    sectorFormula sector
      (normalizedMatrix kind exponent identityMatrix))

theorem identityMatrix_denominator_ne (value : Gaussian) :
    denominator identityMatrix value ≠ 0 := by
  unfold denominator identityMatrix
  rw [RFAP.ConstructiveGaussian.Gaussian.zero_mul,
    RFAP.ConstructiveGaussian.Gaussian.zero_add]
  intro oneZero
  have realOneZero := congrArg
    RFAP.ConstructiveGaussian.Gaussian.re oneZero
  exact RFAP.ConstructiveFraction.zero_ne_one realOneZero.symm

theorem homographic_identityMatrix (value : Gaussian) :
    homographic identityMatrix value = value := by
  unfold homographic numerator denominator identityMatrix
  rw [RFAP.ConstructiveGaussian.Gaussian.one_mul,
    RFAP.ConstructiveGaussian.Gaussian.add_zero,
    RFAP.ConstructiveGaussian.Gaussian.zero_mul,
    RFAP.ConstructiveGaussian.Gaussian.zero_add, inv_eq,
    RFAP.ConstructiveGaussian.Gaussian.inv_one_direct,
    RFAP.ConstructiveGaussian.Gaussian.mul_one]

theorem sectorBitsFormula_iff
    (kind : BlockKind) (exponent : Nat) (bits : SectorBits)
    (value : Gaussian) :
    (sectorBitsFormula kind exponent bits).Holds value ↔
      ∃ sector ∈ sectorCandidates bits,
        sector.Holds (normalizedValue kind exponent value) := by
  unfold sectorBitsFormula
  rw [Formula.holds_any]
  constructor
  · rintro ⟨formula, formulaMember, holds⟩
    rcases QuotientFreeList.mem_map.mp formulaMember with
      ⟨sector, member, formulaEqual⟩
    subst formula
    refine ⟨sector, member, ?_⟩
    have equivalent := normalizedSectorFormula_iff kind exponent sector
      identityMatrix value (identityMatrix_denominator_ne value)
    rw [homographic_identityMatrix] at equivalent
    exact equivalent.1 holds
  · rintro ⟨sector, member, holds⟩
    refine ⟨sectorFormula sector
      (normalizedMatrix kind exponent identityMatrix),
      QuotientFreeList.mem_map.mpr ⟨sector, member, rfl⟩, ?_⟩
    have equivalent := normalizedSectorFormula_iff kind exponent sector
      identityMatrix value (identityMatrix_denominator_ne value)
    rw [homographic_identityMatrix] at equivalent
    exact equivalent.2 holds

/-- Compiled formula for one retained completed-block constraint. -/
def constraintFormula (constraint : Constraint) : Formula :=
  .and (denominatorFormula constraint.matrix)
    (.and (radialFormula constraint.kind constraint.exponent
      constraint.matrix)
      (sectorFormula constraint.sector
        (normalizedMatrix constraint.kind constraint.exponent
          constraint.matrix)))

theorem constraintFormula_iff
    (constraint : Constraint) (value : Gaussian) :
    (constraintFormula constraint).Holds value ↔
      constraint.Holds value := by
  constructor
  · rintro ⟨denominatorHolds, radialHolds, sectorHolds⟩
    have denominatorNonzero : denominator constraint.matrix value ≠ 0 :=
      (denominatorFormula_iff constraint.matrix value).1 denominatorHolds
    exact ⟨denominatorNonzero,
      (radialFormula_iff constraint.kind constraint.exponent
        constraint.matrix value denominatorNonzero).1 radialHolds,
      (normalizedSectorFormula_iff constraint.kind constraint.exponent
        constraint.sector constraint.matrix value denominatorNonzero).1
          sectorHolds⟩
  · rintro ⟨denominatorNonzero, radialHolds, sectorHolds⟩
    exact ⟨(denominatorFormula_iff constraint.matrix value).2
        denominatorNonzero,
      (radialFormula_iff constraint.kind constraint.exponent
        constraint.matrix value denominatorNonzero).2 radialHolds,
      (normalizedSectorFormula_iff constraint.kind constraint.exponent
        constraint.sector constraint.matrix value denominatorNonzero).2
          sectorHolds⟩

/-- Compiled formula for every unfinished parser phase. -/
def activeFormula : Phase → Formula
  | .initial => .truth
  | .highUnary count =>
      .atom ⟨affineNormComparisonForm ((2 : Coordinate) ^ count),
        .nonnegative⟩
  | .lowUnary 0 =>
      .atom ⟨affineNormComparisonForm 2, .negative⟩
  | .lowUnary (count + 1) =>
      .atom ⟨scaledNormComparisonForm count 1, .negative⟩
  | .loopUnary count =>
      .atom ⟨affineNormComparisonForm ((2 : Coordinate) ^ count),
        .positive⟩
  | .sector kind exponent bits =>
      .and (radialFormula kind exponent identityMatrix)
        (sectorBitsFormula kind exponent bits)

theorem activeFormula_iff (phase : Phase) (value : Gaussian) :
    (activeFormula phase).Holds value ↔ activeHolds phase value := by
  cases phase with
  | initial => simp [activeFormula, Formula.Holds, activeHolds]
  | highUnary count =>
      simp only [activeFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        activeHolds, eval_affineNormComparisonForm]
      exact sub_nonnegative_iff
  | lowUnary count =>
      cases count with
      | zero =>
          simp only [activeFormula, Formula.Holds, Atom.Holds,
            SignTest.Holds, activeHolds, eval_affineNormComparisonForm]
          exact sub_negative_iff
      | succ count =>
          simp only [activeFormula, Formula.Holds, Atom.Holds,
            SignTest.Holds, activeHolds, eval_scaledNormComparisonForm]
          exact sub_negative_iff
  | loopUnary count =>
      simp only [activeFormula, Formula.Holds, Atom.Holds, SignTest.Holds,
        activeHolds, eval_affineNormComparisonForm]
      exact sub_positive_iff
  | sector kind exponent bits =>
      have radial :
          (radialFormula kind exponent identityMatrix).Holds value ↔
            radialBracket kind exponent value := by
        simpa only [homographic_identityMatrix] using
          radialFormula_iff kind exponent identityMatrix value
            (identityMatrix_denominator_ne value)
      simp only [activeFormula, Formula.Holds, activeHolds]
      exact and_congr radial (sectorBitsFormula_iff kind exponent bits value)

/-- Hermitian formula for a complete finite parser state. -/
def stateFormula (state : State) : Formula :=
  .and (Formula.all (state.history.map constraintFormula))
    (activeFormula state.phase)

theorem stateFormula_iff (state : State) (value : Gaussian) :
    (stateFormula state).Holds value ↔ state.Holds value := by
  constructor
  · rintro ⟨historyHolds, active⟩
    constructor
    · intro constraint member
      apply (constraintFormula_iff constraint value).1
      apply (Formula.holds_all _ value).1 historyHolds
      exact QuotientFreeList.mem_map.mpr ⟨constraint, member, rfl⟩
    · exact (activeFormula_iff state.phase value).1 active
  · rintro ⟨historyHolds, active⟩
    constructor
    · apply (Formula.holds_all _ value).2
      intro formula member
      rcases QuotientFreeList.mem_map.mp member with ⟨constraint, constraintMember,
        formulaIdentity⟩
      rw [← formulaIdentity]
      exact (constraintFormula_iff constraint value).2
        (historyHolds constraint constraintMember)
    · exact (activeFormula_iff state.phase value).2 active

def parseFormula (word : Word) : Formula := stateFormula (parse word)

theorem parseFormula_iff (word : Word) (value : Gaussian) :
    (parseFormula word).Holds value ↔ (parse word).Holds value :=
  stateFormula_iff (parse word) value

def parseFormulaBool (word : Word) (value : Gaussian) : Bool :=
  (parseFormula word).evalBool value

theorem parseFormulaBool_eq_true (word : Word) (value : Gaussian) :
    parseFormulaBool word value = true ↔ (parse word).Holds value := by
  rw [parseFormulaBool, Formula.evalBool_eq_true, parseFormula_iff]

/-- Explicit finite list of all sign atoms occurring in a formula. -/
def Formula.atoms : Formula → List Atom
  | Formula.truth | Formula.falsity => []
  | Formula.atom testAtom => [testAtom]
  | Formula.and left right | Formula.or left right =>
      left.atoms ++ right.atoms

end CCL.CCLFormula
