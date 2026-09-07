import FTA.CCLSectorInteriorCone
import FTA.CCLSectorBoxGrid
import FTA.CCLStrictChildSemantics

/-!
# Closure-compatible sector selection

At an exact angular boundary, the current unfinished sector prefix may hold
only as a limit.  The phase-local equality bit still selects a successor
prefix, and one of its sector rows has the boundary point in its closure.
This finite lemma supplies the row whose strict interior cone is entered by
`CCLSectorInteriorCone`.
-/

namespace FTA
namespace CCLSectorInteriorSelection

open CCL CCL.GaussianRat
open CCL.EncoderParserBridge
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLNextBitFormula
open FTA.CCLParserGeometry
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLOwnerGrid
open FTA.CCLSectorBoxGrid
open FTA.CCLSectorInteriorCone

abbrev QI := CCL.GaussianRat

/-- Coordinatewise closure of one row of the eight-sector table. -/
def SectorClosureHolds : Sector → QI → Prop
  | .east, z => 1 / 2 ≤ z.re ∧ -1 / 2 ≤ z.im ∧ z.im ≤ 1 / 2
  | .northEast, z => 1 / 2 ≤ z.re ∧ 1 / 2 ≤ z.im
  | .north, z => -1 / 2 ≤ z.re ∧ z.re ≤ 1 / 2 ∧ 1 / 2 ≤ z.im
  | .northWest, z => z.re ≤ -1 / 2 ∧ 1 / 2 ≤ z.im
  | .west, z => z.re ≤ -1 / 2 ∧ -1 / 2 ≤ z.im ∧ z.im ≤ 1 / 2
  | .southWest, z => z.re ≤ -1 / 2 ∧ z.im ≤ -1 / 2
  | .south, z => -1 / 2 ≤ z.re ∧ z.re ≤ 1 / 2 ∧ z.im ≤ -1 / 2
  | .southEast, z => 1 / 2 ≤ z.re ∧ z.im ≤ -1 / 2

/-- Closed form of the parser annulus bracket. -/
def RadialClosureHolds
    (kind : RawParser.BlockKind) (exponent : ℕ) (value : QI) : Prop :=
  match kind with
  | .initialHigh | .loop =>
      (2 : ℚ) ^ exponent ≤ normSq value ∧
        normSq value ≤ (2 : ℚ) ^ (exponent + 1)
  | .initialLow =>
      1 / (2 : ℚ) ^ exponent ≤ normSq value ∧
        normSq value ≤ 2 / (2 : ℚ) ^ exponent

theorem radialClosureHolds_of_radialBracket
    (kind : RawParser.BlockKind) (exponent : ℕ) (value : QI)
    (radial : RawParser.radialBracket kind exponent value) :
    RadialClosureHolds kind exponent value := by
  have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
  cases kind with
  | initialHigh => exact ⟨radial.1, radial.2.le⟩
  | initialLow =>
      constructor
      · apply (div_le_iff₀ powerPositive).2
        rw [_root_.mul_comm]
        exact radial.1
      · apply (le_div_iff₀ powerPositive).2
        rw [_root_.mul_comm]
        exact radial.2.le
  | loop => exact ⟨radial.1.le, radial.2⟩

theorem radialClosure_normalized_norm_lower
    (kind : RawParser.BlockKind) (exponent : ℕ) (value : QI)
    (closure : RadialClosureHolds kind exponent value) :
    1 ≤ normSq (RawParser.normalizedValue kind exponent value) := by
  have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
  cases kind with
  | initialHigh =>
      rw [RawParser.normalizedValue, normSq_mul,
        normSq_inv _ (RawParser.natPow_gamma_ne exponent),
        normSq_natPow, normSq_gamma]
      field_simp
      exact closure.1
  | initialLow =>
      rw [RawParser.normalizedValue, normSq_mul, normSq_natPow, normSq_gamma]
      have scaled := (div_le_iff₀ powerPositive).mp closure.1
      nlinarith
  | loop =>
      rw [RawParser.normalizedValue, normSq_mul,
        normSq_inv _ (RawParser.natPow_gamma_ne exponent),
        normSq_natPow, normSq_gamma]
      field_simp
      exact closure.1

theorem sectorClosureHolds_of_holds
    (sector : Sector) (z : QI) (holds : sector.Holds z) :
    SectorClosureHolds sector z := by
  cases sector with
  | east =>
      exact ⟨holds.1, holds.2.1.le, holds.2.2.le⟩
  | northEast => exact holds
  | north => exact ⟨holds.1.le, holds.2.1.le, holds.2.2⟩
  | northWest => exact holds
  | west => exact ⟨holds.1, holds.2.1.le, holds.2.2.le⟩
  | southWest => exact holds
  | south => exact ⟨holds.1.le, holds.2.1.le, holds.2.2⟩
  | southEast => exact holds

/-- The angular Boolean used by an unfinished sector phase, written directly
on its already-normalized value. -/
def sectorLocalBit : RawParser.SectorBits → QI → Bool
  | .zero, z =>
      !decide (1 / 2 ≤ z.im) &&
        (decide (z.im ≤ -1 / 2) || decide (z.re ≤ -1 / 2))
  | .one false, z => decide (z.re < 1 / 2)
  | .one true, z => decide (-1 / 2 < z.re)
  | .two false false, z => decide (1 / 2 ≤ z.im)
  | .two false true, z => decide (z.re ≤ -1 / 2)
  | .two true false, z => decide (z.im ≤ -1 / 2)
  | .two true true, z => decide (1 / 2 ≤ z.re)

theorem localBit_sector_eq_sectorLocalBit
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (bits : RawParser.SectorBits) (value : QI) :
    CCLStrictChildSemantics.localBit (.sector kind exponent bits) value =
      sectorLocalBit bits (RawParser.normalizedValue kind exponent value) := by
  cases bits with
  | zero => rfl
  | one first => cases first <;> rfl
  | two first second => cases first <;> cases second <;> rfl

private theorem sector_mem_one_projection (sector : Sector) :
    sector ∈ RawParser.sectorCandidates
      (.one (sectorFirstBit sector)) := by
  cases sector <;> native_decide

/-- On the owned table row selected at a band point, the zero-prefix local
bit is exactly the row's first code bit. -/
theorem sectorLocalBit_zero_select
    (z : QI) (normLower : 1 ≤ normSq z) :
    sectorLocalBit .zero z = sectorFirstBit (Sector.select z) := by
  have holds := Sector.select_spec z normLower
  generalize selectedEq : Sector.select z = sector at holds ⊢
  cases sector with
  | east =>
      simp only [Sector.Holds] at holds
      have notHigh : ¬(1 / 2 : ℚ) ≤ z.im := not_le_of_gt holds.2.2
      have notLow : ¬z.im ≤ (-1 / 2 : ℚ) := not_le_of_gt holds.2.1
      have notWest : ¬z.re ≤ (-1 / 2 : ℚ) := by linarith [holds.1]
      have highDecision : decide ((1 / 2 : ℚ) ≤ z.im) = false := by
        simpa only [decide_eq_false_iff_not] using notHigh
      have lowDecision : decide (z.im ≤ (-1 / 2 : ℚ)) = false := by
        simpa only [decide_eq_false_iff_not] using notLow
      have westDecision : decide (z.re ≤ (-1 / 2 : ℚ)) = false := by
        simpa only [decide_eq_false_iff_not] using notWest
      rw [sectorLocalBit, highDecision, lowDecision, westDecision]
      rfl
  | northEast =>
      simp only [Sector.Holds] at holds
      have highDecision : decide ((1 / 2 : ℚ) ≤ z.im) = true := by
        simpa only [decide_eq_true_eq] using holds.2
      rw [sectorLocalBit, highDecision]
      rfl
  | north =>
      simp only [Sector.Holds] at holds
      have highDecision : decide ((1 / 2 : ℚ) ≤ z.im) = true := by
        simpa only [decide_eq_true_eq] using holds.2.2
      rw [sectorLocalBit, highDecision]
      rfl
  | northWest =>
      simp only [Sector.Holds] at holds
      have highDecision : decide ((1 / 2 : ℚ) ≤ z.im) = true := by
        simpa only [decide_eq_true_eq] using holds.2
      rw [sectorLocalBit, highDecision]
      rfl
  | west =>
      simp only [Sector.Holds] at holds
      have notHigh : ¬(1 / 2 : ℚ) ≤ z.im := not_le_of_gt holds.2.2
      have notLow : ¬z.im ≤ (-1 / 2 : ℚ) := not_le_of_gt holds.2.1
      have highDecision : decide ((1 / 2 : ℚ) ≤ z.im) = false := by
        simpa only [decide_eq_false_iff_not] using notHigh
      have lowDecision : decide (z.im ≤ (-1 / 2 : ℚ)) = false := by
        simpa only [decide_eq_false_iff_not] using notLow
      have westDecision : decide (z.re ≤ (-1 / 2 : ℚ)) = true := by
        simpa only [decide_eq_true_eq] using holds.1
      rw [sectorLocalBit, highDecision, lowDecision, westDecision]
      rfl
  | southWest =>
      simp only [Sector.Holds] at holds
      have notHigh : ¬(1 / 2 : ℚ) ≤ z.im := by linarith [holds.2]
      have highDecision : decide ((1 / 2 : ℚ) ≤ z.im) = false := by
        simpa only [decide_eq_false_iff_not] using notHigh
      have lowDecision : decide (z.im ≤ (-1 / 2 : ℚ)) = true := by
        simpa only [decide_eq_true_eq] using holds.2
      rw [sectorLocalBit, highDecision, lowDecision]
      rfl
  | south =>
      simp only [Sector.Holds] at holds
      have notHigh : ¬(1 / 2 : ℚ) ≤ z.im := by linarith [holds.2.2]
      have highDecision : decide ((1 / 2 : ℚ) ≤ z.im) = false := by
        simpa only [decide_eq_false_iff_not] using notHigh
      have lowDecision : decide (z.im ≤ (-1 / 2 : ℚ)) = true := by
        simpa only [decide_eq_true_eq] using holds.2.2
      rw [sectorLocalBit, highDecision, lowDecision]
      rfl
  | southEast =>
      simp only [Sector.Holds] at holds
      have notHigh : ¬(1 / 2 : ℚ) ≤ z.im := by linarith [holds.2]
      have highDecision : decide ((1 / 2 : ℚ) ≤ z.im) = false := by
        simpa only [decide_eq_false_iff_not] using notHigh
      have lowDecision : decide (z.im ≤ (-1 / 2 : ℚ)) = true := by
        simpa only [decide_eq_true_eq] using holds.2
      rw [sectorLocalBit, highDecision, lowDecision]
      rfl

/-- The equality-convention first bit always leaves at least one successor
sector row whose closure contains the exact boundary point. -/
theorem exists_sectorClosure_one_of_localBit
    (z : QI) (normLower : 1 ≤ normSq z) :
    ∃ sector ∈ RawParser.sectorCandidates
        (.one (sectorLocalBit .zero z)),
      SectorClosureHolds sector z := by
  let sector := Sector.select z
  have holds : sector.Holds z := Sector.select_spec z normLower
  have bit := sectorLocalBit_zero_select z normLower
  refine ⟨sector, ?_, sectorClosureHolds_of_holds sector z holds⟩
  rw [bit]
  exact sector_mem_one_projection sector

/-- A one-bit prefix closure and its equality-convention second bit leave a
compatible two-bit sector closure.  The four axial tie cases deliberately
move to the adjacent row selected by the new bit. -/
theorem exists_sectorClosure_two_of_localBit
    (first : Bool) (z : QI)
    (current : ∃ sector ∈ RawParser.sectorCandidates (.one first),
      SectorClosureHolds sector z) :
    ∃ sector ∈ RawParser.sectorCandidates
        (.two first (sectorLocalBit (.one first) z)),
      SectorClosureHolds sector z := by
  rcases current with ⟨sector, member, closure⟩
  cases first with
  | false =>
      simp only [RawParser.sectorCandidates_one_false, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · refine ⟨.east, ?_, closure⟩
        have notLess : ¬z.re < 1 / 2 := not_lt_of_ge closure.1
        have bit : sectorLocalBit (.one false) z = false := by
          rw [sectorLocalBit]
          simpa only [decide_eq_false_iff_not] using notLess
        rw [bit]
        native_decide
      · refine ⟨.northEast, ?_, closure⟩
        have notLess : ¬z.re < 1 / 2 := not_lt_of_ge closure.1
        have bit : sectorLocalBit (.one false) z = false := by
          rw [sectorLocalBit]
          simpa only [decide_eq_false_iff_not] using notLess
        rw [bit]
        native_decide
      · by_cases less : z.re < 1 / 2
        · refine ⟨.north, ?_, closure⟩
          have bit : sectorLocalBit (.one false) z = true := by
            rw [sectorLocalBit]
            simpa only [decide_eq_true_eq] using less
          rw [bit]
          native_decide
        · refine ⟨.northEast, ?_, ?_⟩
          · have bit : sectorLocalBit (.one false) z = false := by
              rw [sectorLocalBit]
              simpa only [decide_eq_false_iff_not] using less
            rw [bit]
            native_decide
          · exact ⟨by linarith [closure.2.1], closure.2.2⟩
      · refine ⟨.northWest, ?_, closure⟩
        have less : z.re < 1 / 2 := by linarith [closure.1]
        have bit : sectorLocalBit (.one false) z = true := by
          rw [sectorLocalBit]
          simpa only [decide_eq_true_eq] using less
        rw [bit]
        native_decide
  | true =>
      simp only [RawParser.sectorCandidates_one_true, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · refine ⟨.west, ?_, closure⟩
        have notLess : ¬(-1 / 2 : ℚ) < z.re := not_lt_of_ge closure.1
        have bit : sectorLocalBit (.one true) z = false := by
          rw [sectorLocalBit]
          simpa only [decide_eq_false_iff_not] using notLess
        rw [bit]
        native_decide
      · refine ⟨.southWest, ?_, closure⟩
        have notLess : ¬(-1 / 2 : ℚ) < z.re := not_lt_of_ge closure.1
        have bit : sectorLocalBit (.one true) z = false := by
          rw [sectorLocalBit]
          simpa only [decide_eq_false_iff_not] using notLess
        rw [bit]
        native_decide
      · by_cases less : (-1 / 2 : ℚ) < z.re
        · refine ⟨.south, ?_, closure⟩
          have bit : sectorLocalBit (.one true) z = true := by
            rw [sectorLocalBit]
            simpa only [decide_eq_true_eq] using less
          rw [bit]
          native_decide
        · refine ⟨.southWest, ?_, ?_⟩
          · have bit : sectorLocalBit (.one true) z = false := by
              rw [sectorLocalBit]
              simpa only [decide_eq_false_iff_not] using less
            rw [bit]
            native_decide
          · exact ⟨by linarith [closure.1], closure.2.2⟩
      · refine ⟨.southEast, ?_, closure⟩
        have less : (-1 / 2 : ℚ) < z.re := by linarith [closure.1]
        have bit : sectorLocalBit (.one true) z = true := by
          rw [sectorLocalBit]
          simpa only [decide_eq_true_eq] using less
        rw [bit]
        native_decide

theorem orientedRealForm_eval_nonneg_iff
    (increasing : Bool) (matrix : Mat2 QI) (threshold : ℚ) (point : QI)
    (denominator : matrix.c * point + matrix.d ≠ 0) :
    0 ≤ (orientedRealForm increasing matrix threshold).eval point ↔
      if increasing then
        threshold ≤ (CCL.RatBox.homographic matrix point).re
      else
        (CCL.RatBox.homographic matrix point).re ≤ threshold := by
  cases increasing with
  | false =>
      simp only [orientedRealForm_false, HermitianForm.eval_neg]
      have comparison := real_homographic_le_iff matrix point threshold
        denominator
      constructor
      · intro negNonnegative
        apply comparison.mpr
        linarith
      · intro coordinateLe
        have baseLe := comparison.mp coordinateLe
        linarith
  | true =>
      simp only [orientedRealForm_true, if_true]
      exact (real_homographic_ge_iff matrix point threshold denominator).symm

theorem orientedImagForm_eval_nonneg_iff
    (increasing : Bool) (matrix : Mat2 QI) (threshold : ℚ) (point : QI)
    (denominator : matrix.c * point + matrix.d ≠ 0) :
    0 ≤ (orientedImagForm increasing matrix threshold).eval point ↔
      if increasing then
        threshold ≤ (CCL.RatBox.homographic matrix point).im
      else
        (CCL.RatBox.homographic matrix point).im ≤ threshold := by
  cases increasing with
  | false =>
      simp only [orientedImagForm_false, HermitianForm.eval_neg]
      have comparison := imag_homographic_le_iff matrix point threshold
        denominator
      constructor
      · intro negNonnegative
        apply comparison.mpr
        linarith
      · intro coordinateLe
        have baseLe := comparison.mp coordinateLe
        linarith
  | true =>
      simp only [orientedImagForm_true, if_true]
      exact (imag_homographic_ge_iff matrix point threshold denominator).symm

theorem orientedNormForm_eval_nonneg_iff
    (increasing : Bool) (matrix : Mat2 QI) (radiusSq : ℚ) (point : QI)
    (denominator : matrix.c * point + matrix.d ≠ 0) :
    0 ≤ (orientedNormForm increasing matrix radiusSq).eval point ↔
      if increasing then
        radiusSq ≤ normSq (CCL.RatBox.homographic matrix point)
      else
        normSq (CCL.RatBox.homographic matrix point) ≤ radiusSq := by
  cases increasing with
  | false =>
      simp only [orientedNormForm_false, HermitianForm.eval_neg]
      have comparison := norm_homographic_le_iff matrix point radiusSq
        denominator
      constructor
      · intro negNonnegative
        apply comparison.mpr
        linarith
      · intro normLe
        have baseLe := comparison.mp normLe
        linarith
  | true =>
      simp only [orientedNormForm_true, if_true]
      exact (norm_homographic_ge_iff matrix point radiusSq denominator).symm

/-- A closed parser annulus orients both strict-interior radial faces
nonnegatively before perturbation. -/
theorem radialInteriorForms_nonneg_of_closure
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (point : QI) (denominator : matrix.c * point + matrix.d ≠ 0)
    (closure : RadialClosureHolds kind exponent
      (CCL.RatBox.homographic matrix point)) :
    ∀ form ∈ radialInteriorForms kind exponent matrix,
      0 ≤ form.eval point := by
  intro form member
  cases kind with
  | initialHigh =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact (orientedNormForm_eval_nonneg_iff true matrix
          ((2 : ℚ) ^ exponent) point denominator).2 closure.1
      · exact (orientedNormForm_eval_nonneg_iff false matrix
          ((2 : ℚ) ^ (exponent + 1)) point denominator).2 closure.2
  | initialLow =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact (orientedNormForm_eval_nonneg_iff true matrix
          (1 / (2 : ℚ) ^ exponent) point denominator).2 closure.1
      · exact (orientedNormForm_eval_nonneg_iff false matrix
          (2 / (2 : ℚ) ^ exponent) point denominator).2 closure.2
  | loop =>
      simp only [radialInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact (orientedNormForm_eval_nonneg_iff true matrix
          ((2 : ℚ) ^ exponent) point denominator).2 closure.1
      · exact (orientedNormForm_eval_nonneg_iff false matrix
          ((2 : ℚ) ^ (exponent + 1)) point denominator).2 closure.2

/-- A row closure is exactly enough to orient every strict-interior face
nonnegatively before the common tangent perturbation. -/
theorem sectorInteriorForms_nonneg_of_closure
    (sector : Sector) (matrix : Mat2 QI) (point : QI)
    (denominator : matrix.c * point + matrix.d ≠ 0)
    (closure : SectorClosureHolds sector
      (CCL.RatBox.homographic matrix point)) :
    ∀ form ∈ sectorInteriorForms sector matrix,
      0 ≤ form.eval point := by
  intro form member
  cases sector with
  | east =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl
      · exact (orientedRealForm_eval_nonneg_iff true matrix (1 / 2) point
          denominator).2 closure.1
      · exact (orientedImagForm_eval_nonneg_iff true matrix (-1 / 2) point
          denominator).2 closure.2.1
      · exact (orientedImagForm_eval_nonneg_iff false matrix (1 / 2) point
          denominator).2 closure.2.2
  | northEast =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact (orientedRealForm_eval_nonneg_iff true matrix (1 / 2) point
          denominator).2 closure.1
      · exact (orientedImagForm_eval_nonneg_iff true matrix (1 / 2) point
          denominator).2 closure.2
  | north =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl
      · exact (orientedImagForm_eval_nonneg_iff true matrix (1 / 2) point
          denominator).2 closure.2.2
      · exact (orientedRealForm_eval_nonneg_iff true matrix (-1 / 2) point
          denominator).2 closure.1
      · exact (orientedRealForm_eval_nonneg_iff false matrix (1 / 2) point
          denominator).2 closure.2.1
  | northWest =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact (orientedRealForm_eval_nonneg_iff false matrix (-1 / 2) point
          denominator).2 closure.1
      · exact (orientedImagForm_eval_nonneg_iff true matrix (1 / 2) point
          denominator).2 closure.2
  | west =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl
      · exact (orientedRealForm_eval_nonneg_iff false matrix (-1 / 2) point
          denominator).2 closure.1
      · exact (orientedImagForm_eval_nonneg_iff true matrix (-1 / 2) point
          denominator).2 closure.2.1
      · exact (orientedImagForm_eval_nonneg_iff false matrix (1 / 2) point
          denominator).2 closure.2.2
  | southWest =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact (orientedRealForm_eval_nonneg_iff false matrix (-1 / 2) point
          denominator).2 closure.1
      · exact (orientedImagForm_eval_nonneg_iff false matrix (-1 / 2) point
          denominator).2 closure.2
  | south =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl
      · exact (orientedImagForm_eval_nonneg_iff false matrix (-1 / 2) point
          denominator).2 closure.2.2
      · exact (orientedRealForm_eval_nonneg_iff true matrix (-1 / 2) point
          denominator).2 closure.1
      · exact (orientedRealForm_eval_nonneg_iff false matrix (1 / 2) point
          denominator).2 closure.2.1
  | southEast =>
      simp only [sectorInteriorForms, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact (orientedRealForm_eval_nonneg_iff true matrix (1 / 2) point
          denominator).2 closure.1
      · exact (orientedImagForm_eval_nonneg_iff false matrix (-1 / 2) point
          denominator).2 closure.2

/-- At a zero-bit sector boundary, the fixed equality bit selects a row whose
entire radial/sector interior cone is nonnegative at the anchor. -/
theorem exists_activeBlockSectorInteriorForms_nonneg_zero
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (point : QI) (denominator : matrix.c * point + matrix.d ≠ 0)
    (radialClosure : RadialClosureHolds kind exponent
      (CCL.RatBox.homographic matrix point)) :
    ∃ sector ∈ RawParser.sectorCandidates
        (.one (CCLStrictChildSemantics.localBit
          (.sector kind exponent .zero)
            (CCL.RatBox.homographic matrix point))),
      ∀ form ∈ blockSectorInteriorForms kind exponent sector matrix,
        0 ≤ form.eval point := by
  let value := CCL.RatBox.homographic matrix point
  let normalized := normalizedMatrix kind exponent matrix
  have normLower := radialClosure_normalized_norm_lower kind exponent value
    radialClosure
  rcases exists_sectorClosure_one_of_localBit
      (RawParser.normalizedValue kind exponent value) normLower with
    ⟨sector, sectorMember, sectorClosure⟩
  refine ⟨sector, ?_, ?_⟩
  · simpa only [value, localBit_sector_eq_sectorLocalBit] using sectorMember
  · intro form member
    rcases List.mem_append.mp member with radialMember | sectorFormMember
    · exact radialInteriorForms_nonneg_of_closure kind exponent matrix point
        denominator radialClosure form radialMember
    · have normalizedDenominator : normalized.c * point + normalized.d ≠ 0 := by
        have lowerRow := normalizedMatrix_lowerRow kind exponent matrix
        simpa only [normalized, lowerRow.1, lowerRow.2] using denominator
      have closureAt : SectorClosureHolds sector
          (CCL.RatBox.homographic normalized point) := by
        simpa only [normalized, value, homographic_normalizedMatrix] using
          sectorClosure
      exact sectorInteriorForms_nonneg_of_closure sector normalized point
        normalizedDenominator closureAt form sectorFormMember

/-- One-bit version of
`exists_activeBlockSectorInteriorForms_nonneg_zero`; the current prefix is
needed only through a closed compatible sector row. -/
theorem exists_activeBlockSectorInteriorForms_nonneg_one
    (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool)
    (matrix : Mat2 QI) (point : QI)
    (denominator : matrix.c * point + matrix.d ≠ 0)
    (radialClosure : RadialClosureHolds kind exponent
      (CCL.RatBox.homographic matrix point))
    (currentSectorClosure : ∃ sector ∈
      RawParser.sectorCandidates (.one first),
      SectorClosureHolds sector
        (RawParser.normalizedValue kind exponent
          (CCL.RatBox.homographic matrix point))) :
    ∃ sector ∈ RawParser.sectorCandidates
        (.two first (CCLStrictChildSemantics.localBit
          (.sector kind exponent (.one first))
            (CCL.RatBox.homographic matrix point))),
      ∀ form ∈ blockSectorInteriorForms kind exponent sector matrix,
        0 ≤ form.eval point := by
  let value := CCL.RatBox.homographic matrix point
  let normalized := normalizedMatrix kind exponent matrix
  rcases exists_sectorClosure_two_of_localBit first
      (RawParser.normalizedValue kind exponent value) (by
        simpa only [value] using currentSectorClosure) with
    ⟨sector, sectorMember, sectorClosure⟩
  refine ⟨sector, ?_, ?_⟩
  · simpa only [value, localBit_sector_eq_sectorLocalBit] using sectorMember
  · intro form member
    rcases List.mem_append.mp member with radialMember | sectorFormMember
    · exact radialInteriorForms_nonneg_of_closure kind exponent matrix point
        denominator radialClosure form radialMember
    · have normalizedDenominator : normalized.c * point + normalized.d ≠ 0 := by
        have lowerRow := normalizedMatrix_lowerRow kind exponent matrix
        simpa only [normalized, lowerRow.1, lowerRow.2] using denominator
      have closureAt : SectorClosureHolds sector
          (CCL.RatBox.homographic normalized point) := by
        simpa only [normalized, value, homographic_normalizedMatrix] using
          sectorClosure
      exact sectorInteriorForms_nonneg_of_closure sector normalized point
        normalizedDenominator closureAt form sectorFormMember

/-! ## Box-compatible strict entry -/

def inactiveBlockSectorInteriorForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (point : QI) : List HermitianForm :=
  (blockSectorInteriorForms kind exponent sector matrix).filter fun form =>
    decide (form.eval point ≠ 0)

theorem activeBlockSectorInteriorForms_eval_zero
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {matrix : Mat2 QI} {point : QI} {form : HermitianForm}
    (member : form ∈ activeBlockSectorInteriorForms kind exponent sector
      matrix point) :
    form.eval point = 0 :=
  of_decide_eq_true (List.mem_filter.mp member).2

theorem inactiveBlockSectorInteriorForms_eval_ne_zero
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {matrix : Mat2 QI} {point : QI} {form : HermitianForm}
    (member : form ∈ inactiveBlockSectorInteriorForms kind exponent sector
      matrix point) :
    form.eval point ≠ 0 :=
  of_decide_eq_true (List.mem_filter.mp member).2

theorem blockSectorInteriorForms_active_or_inactive
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {matrix : Mat2 QI} {point : QI} {form : HermitianForm}
    (member : form ∈ blockSectorInteriorForms kind exponent sector matrix) :
    form ∈ activeBlockSectorInteriorForms kind exponent sector matrix point ∨
      form ∈ inactiveBlockSectorInteriorForms kind exponent sector matrix
        point := by
  by_cases zero : form.eval point = 0
  · left
    exact List.mem_filter.mpr ⟨member, by simp [zero]⟩
  · right
    exact List.mem_filter.mpr ⟨member, by simp [zero]⟩

def blockSectorBoxPriors
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (point : QI) (box : RatBox) :
    List HermitianForm :=
  inactiveBlockSectorInteriorForms kind exponent sector matrix point ++
    boxForms box

theorem blockSectorBoxPriors_pos
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {matrix : Mat2 QI} {point : QI} {box : RatBox}
    (nonnegative : ∀ form ∈
      blockSectorInteriorForms kind exponent sector matrix,
      0 ≤ form.eval point)
    (strictBox : StrictContains box point) :
    ∀ form ∈ blockSectorBoxPriors kind exponent sector matrix point box,
      0 < form.eval point := by
  intro form member
  rcases List.mem_append.mp member with inactive | boxForm
  · have source := (List.mem_filter.mp inactive).1
    have nonzero := inactiveBlockSectorInteriorForms_eval_ne_zero inactive
    exact lt_of_le_of_ne (nonnegative form source) (Ne.symm nonzero)
  · exact all_boxForms_pos_of_strictContains strictBox form boxForm

/-- Rational point produced by the combined annulus/sector/box cone. -/
def blockSectorBoxPoint
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    (denominator : matrix.c * point + matrix.d ≠ 0)
    (box : RatBox) : QI :=
  let direction := blockSectorInteriorTangentDirection kind exponent sector
    matrix point determinantNonzero denominator
  let priors := blockSectorBoxPriors kind exponent sector matrix point box
  step point (multiOwnerEpsilon direction priors) direction.vector

structure BlockSectorBoxSample
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (box : RatBox) where
  point : QI
  blockStrict : ∀ form ∈
    blockSectorInteriorForms kind exponent sector matrix,
    0 < form.eval point
  boxStrict : StrictContains box point

theorem BlockSectorBoxSample.radialFormula_holds
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {matrix : Mat2 QI} {box : RatBox}
    (sample : BlockSectorBoxSample kind exponent sector matrix box) :
    (radialFormula kind exponent matrix).Holds sample.point := by
  apply radialFormula_holds_of_interiorForms_pos
  intro form member
  apply sample.blockStrict form
  exact List.mem_append_left _ member

theorem BlockSectorBoxSample.sectorFormula_holds
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {matrix : Mat2 QI} {box : RatBox}
    (sample : BlockSectorBoxSample kind exponent sector matrix box) :
    (sectorFormula sector (normalizedMatrix kind exponent matrix)).Holds
      sample.point := by
  apply sectorFormula_holds_of_interiorForms_pos
  intro form member
  apply sample.blockStrict form
  exact List.mem_append_right _ member

/-- Total box-compatible entry once a closure-compatible row has been
selected.  All arithmetic is rational and the direction search is finite. -/
def computeBlockSectorBoxSample
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (point : QI)
    (determinantNonzero : determinant matrix ≠ 0)
    (denominator : matrix.c * point + matrix.d ≠ 0)
    (box : RatBox)
    (nonnegative : ∀ form ∈
      blockSectorInteriorForms kind exponent sector matrix,
      0 ≤ form.eval point)
    (strictBox : StrictContains box point) :
    BlockSectorBoxSample kind exponent sector matrix box := by
  let active := activeBlockSectorInteriorForms kind exponent sector matrix point
  let direction := blockSectorInteriorTangentDirection kind exponent sector
    matrix point determinantNonzero denominator
  let priors := blockSectorBoxPriors kind exponent sector matrix point box
  let epsilon := multiOwnerEpsilon direction priors
  let stepped := step point epsilon direction.vector
  have priorsPositive : ∀ form ∈ priors, 0 < form.eval point := by
    simpa only [priors] using blockSectorBoxPriors_pos nonnegative strictBox
  have priorsNonzero : ∀ form ∈ priors, form.eval point ≠ 0 := by
    intro form member
    exact (priorsPositive form member).ne'
  have onActive : ∀ form ∈ active, form.eval point = 0 := by
    intro form member
    exact activeBlockSectorInteriorForms_eval_zero member
  have entered : ∀ form ∈ active, 0 < form.eval stepped := by
    simpa only [active, direction, priors, epsilon, stepped] using
      enters_all_boundaries direction priors onActive priorsNonzero
  have preserved : ∀ form ∈ priors,
      0 < form.eval point * form.eval stepped := by
    simpa only [direction, priors, epsilon, stepped] using
      preserves_all_priors direction priors priorsNonzero
  have priorsAfter : ∀ form ∈ priors, 0 < form.eval stepped := by
    intro form member
    rcases mul_pos_iff.mp (preserved form member) with signs | signs
    · exact signs.2
    · exact (not_lt_of_ge (priorsPositive form member).le signs.1).elim
  refine
    { point := stepped
      blockStrict := ?_
      boxStrict := ?_ }
  · intro form member
    rcases blockSectorInteriorForms_active_or_inactive (point := point) member
        with activeMember | inactiveMember
    · exact entered form activeMember
    · apply priorsAfter form
      simp [priors, blockSectorBoxPriors, inactiveMember]
  · apply strictContains_of_all_boxForms_pos
    intro form member
    apply priorsAfter form
    simp [priors, blockSectorBoxPriors, member]

/-- A strict combined sample realizes the zero-prefix incremental child
selected by its sector membership. -/
theorem BlockSectorBoxSample.inputIncrementalAdvanceFormula_holds_zero
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {parserMatrix : Mat2 QI} {history : List RawParser.Constraint}
    {box : RatBox}
    (sample : BlockSectorBoxSample kind exponent sector
      (adjugate parserMatrix) box)
    (bit : Bool)
    (sectorMember : sector ∈ RawParser.sectorCandidates (.one bit))
    (denominator : (adjugate parserMatrix).c * sample.point +
      (adjugate parserMatrix).d ≠ 0) :
    (inputIncrementalAdvanceFormula
      ⟨.sector kind exponent .zero, parserMatrix, history⟩ bit).Holds
        sample.point := by
  let matrix := adjugate parserMatrix
  let tail := CCL.RatBox.homographic matrix sample.point
  have radial : RawParser.radialBracket kind exponent tail :=
    (radialFormula_iff kind exponent matrix sample.point denominator).1
      sample.radialFormula_holds
  have sectorHolds : sector.Holds
      (RawParser.normalizedValue kind exponent tail) :=
    (normalizedSectorFormula_iff kind exponent sector matrix sample.point
      denominator).1 sample.sectorFormula_holds
  apply (inputIncrementalAdvanceFormula_iff
    ⟨.sector kind exponent .zero, parserMatrix, history⟩ bit sample.point
      denominator).2
  simp only [incrementalAdvanceFormula, RawParser.step]
  apply (activeFormula_iff (.sector kind exponent (.one bit)) tail).2
  exact ⟨radial, sector, sectorMember, sectorHolds⟩

/-- One-prefix counterpart of
`BlockSectorBoxSample.inputIncrementalAdvanceFormula_holds_zero`. -/
theorem BlockSectorBoxSample.inputIncrementalAdvanceFormula_holds_one
    {kind : RawParser.BlockKind} {exponent : ℕ} {first : Bool}
    {sector : Sector} {parserMatrix : Mat2 QI}
    {history : List RawParser.Constraint} {box : RatBox}
    (sample : BlockSectorBoxSample kind exponent sector
      (adjugate parserMatrix) box)
    (bit : Bool)
    (sectorMember : sector ∈
      RawParser.sectorCandidates (.two first bit))
    (denominator : (adjugate parserMatrix).c * sample.point +
      (adjugate parserMatrix).d ≠ 0) :
    (inputIncrementalAdvanceFormula
      ⟨.sector kind exponent (.one first), parserMatrix, history⟩ bit).Holds
        sample.point := by
  let matrix := adjugate parserMatrix
  let tail := CCL.RatBox.homographic matrix sample.point
  have radial : RawParser.radialBracket kind exponent tail :=
    (radialFormula_iff kind exponent matrix sample.point denominator).1
      sample.radialFormula_holds
  have sectorHolds : sector.Holds
      (RawParser.normalizedValue kind exponent tail) :=
    (normalizedSectorFormula_iff kind exponent sector matrix sample.point
      denominator).1 sample.sectorFormula_holds
  apply (inputIncrementalAdvanceFormula_iff
    ⟨.sector kind exponent (.one first), parserMatrix, history⟩ bit sample.point
      denominator).2
  simp only [incrementalAdvanceFormula, RawParser.step]
  apply (activeFormula_iff (.sector kind exponent (.two first bit)) tail).2
  exact ⟨radial, sector, sectorMember, sectorHolds⟩

/-! ## Residual-tolerant box-compatible entry -/

/-- A point strictly inside a finite list of inward faces and a requested
rational box. -/
structure OrientedBoxSample (forms : List HermitianForm) (box : RatBox) where
  point : QI
  formsStrict : ∀ form ∈ forms, 0 < form.eval point
  boxStrict : StrictContains box point

def approximateOrientedBoxPriors
    (active forms : List HermitianForm) (box : RatBox) :
    List HermitianForm :=
  (forms.filter fun form => decide (form ∉ active)) ++ boxForms box

/-- Residual-tolerant entry data for an arbitrary finite conjunction of
oriented Hermitian faces. -/
structure ApproximateOrientedBoxData
    (forms : List HermitianForm) (box : RatBox)
    (active : List HermitianForm) where
  base : QI
  baseStrict : box.StrictContains base
  direction : TangentDirection active base
  inactiveStrict : ∀ form ∈ forms, form ∉ active → 0 < form.eval base
  activeResidual : ∀ form ∈ active,
    |form.eval base| < approximateBoundaryBudget direction
      (approximateOrientedBoxPriors active forms box)

namespace ApproximateOrientedBoxData

def point
    {forms : List HermitianForm} {box : RatBox}
    {active : List HermitianForm}
    (data : ApproximateOrientedBoxData forms box active) : QI :=
  step data.base
    (multiOwnerEpsilon data.direction
      (approximateOrientedBoxPriors active forms box))
    data.direction.vector

theorem priors_nonzero
    {forms : List HermitianForm} {box : RatBox}
    {active : List HermitianForm}
    (data : ApproximateOrientedBoxData forms box active) :
    ∀ form ∈ approximateOrientedBoxPriors active forms box,
      form.eval data.base ≠ 0 := by
  intro form member
  rcases List.mem_append.mp member with inactive | boxForm
  · have filtered := List.mem_filter.mp inactive
    exact (data.inactiveStrict form filtered.1
      (of_decide_eq_true filtered.2)).ne'
  · exact (all_boxForms_pos_of_strictContains data.baseStrict form boxForm).ne'

theorem entered
    {forms : List HermitianForm} {box : RatBox}
    {active : List HermitianForm}
    (data : ApproximateOrientedBoxData forms box active) :
    ∀ form ∈ active, 0 < form.eval (point data) := by
  simpa only [point] using
    enters_all_boundaries_of_residual data.direction
      (approximateOrientedBoxPriors active forms box)
      (priors_nonzero data) data.activeResidual

theorem preserved
    {forms : List HermitianForm} {box : RatBox}
    {active : List HermitianForm}
    (data : ApproximateOrientedBoxData forms box active) :
    ∀ form ∈ approximateOrientedBoxPriors active forms box,
      0 < form.eval data.base * form.eval (point data) := by
  simpa only [point] using
    preserves_all_priors data.direction
      (approximateOrientedBoxPriors active forms box) (priors_nonzero data)

private theorem prior_pos_after
    {forms : List HermitianForm} {box : RatBox}
    {active : List HermitianForm}
    (data : ApproximateOrientedBoxData forms box active)
    (form : HermitianForm)
    (member : form ∈ approximateOrientedBoxPriors active forms box)
    (positive : 0 < form.eval data.base) :
    0 < form.eval (point data) := by
  rcases mul_pos_iff.mp (preserved data form member) with signs | signs
  · exact signs.2
  · exact (not_lt_of_ge positive.le signs.1).elim

def sample
    {forms : List HermitianForm} {box : RatBox}
    {active : List HermitianForm}
    (data : ApproximateOrientedBoxData forms box active) :
    OrientedBoxSample forms box where
  point := point data
  formsStrict := by
    intro form member
    by_cases activeMember : form ∈ active
    · exact entered data form activeMember
    · apply prior_pos_after data form
      · apply List.mem_append_left
        exact List.mem_filter.mpr ⟨member, by simp [activeMember]⟩
      · exact data.inactiveStrict form member activeMember
  boxStrict := by
    apply strictContains_of_all_boxForms_pos
    intro form member
    apply prior_pos_after data form
    · exact List.mem_append_right _ member
    · exact all_boxForms_pos_of_strictContains data.baseStrict form member

end ApproximateOrientedBoxData

/-- Priors for an approximate sector-boundary entry.  The caller supplies
the finite list of faces whose values may merely be small at the rational
anchor; every other block face and every side of the requested box is
preserved as a strict prior. -/
def approximateBlockSectorBoxPriors
    (active : List HermitianForm)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (box : RatBox) : List HermitianForm :=
  ((blockSectorInteriorForms kind exponent sector matrix).filter fun form =>
      decide (form ∉ active)) ++
    boxForms box

/-- Finite rational data sufficient to enter a completed annulus/sector cone
from a nearby, rather than exact, algebraic boundary point.  This is the
sector analogue of `CCLActiveEventGrid.Data`: active faces need only have
residual below the proved entry budget, while all complementary faces are
strict priors. -/
structure ApproximateBlockSectorBoxData
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (box : RatBox) (active : List HermitianForm) where
  base : QI
  baseStrict : box.StrictContains base
  direction : TangentDirection active base
  inactiveStrict : ∀ form ∈
    blockSectorInteriorForms kind exponent sector matrix,
      form ∉ active → 0 < form.eval base
  activeResidual : ∀ form ∈ active,
    |form.eval base| < approximateBoundaryBudget direction
      (approximateBlockSectorBoxPriors active kind exponent sector matrix box)

namespace ApproximateBlockSectorBoxData

/-- Take the common rational inward step certified by the approximate
boundary data. -/
def point
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {matrix : Mat2 QI} {box : RatBox} {active : List HermitianForm}
    (data : ApproximateBlockSectorBoxData kind exponent sector matrix box
      active) : QI :=
  step data.base
    (multiOwnerEpsilon data.direction
      (approximateBlockSectorBoxPriors active kind exponent sector matrix box))
    data.direction.vector

theorem priors_nonzero
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {matrix : Mat2 QI} {box : RatBox} {active : List HermitianForm}
    (data : ApproximateBlockSectorBoxData kind exponent sector matrix box
      active) :
    ∀ form ∈ approximateBlockSectorBoxPriors active kind exponent sector
        matrix box,
      form.eval data.base ≠ 0 := by
  intro form member
  rcases List.mem_append.mp member with inactive | boxForm
  · have filtered := List.mem_filter.mp inactive
    exact (data.inactiveStrict form filtered.1
      (of_decide_eq_true filtered.2)).ne'
  · exact (all_boxForms_pos_of_strictContains data.baseStrict form boxForm).ne'

theorem entered
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {matrix : Mat2 QI} {box : RatBox} {active : List HermitianForm}
    (data : ApproximateBlockSectorBoxData kind exponent sector matrix box
      active) :
    ∀ form ∈ active, 0 < form.eval (point data) := by
  simpa only [point] using
    enters_all_boundaries_of_residual data.direction
      (approximateBlockSectorBoxPriors active kind exponent sector matrix box)
      (priors_nonzero data) data.activeResidual

theorem preserved
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {matrix : Mat2 QI} {box : RatBox} {active : List HermitianForm}
    (data : ApproximateBlockSectorBoxData kind exponent sector matrix box
      active) :
    ∀ form ∈ approximateBlockSectorBoxPriors active kind exponent sector
        matrix box,
      0 < form.eval data.base * form.eval (point data) := by
  simpa only [point] using
    preserves_all_priors data.direction
      (approximateBlockSectorBoxPriors active kind exponent sector matrix box)
      (priors_nonzero data)

private theorem prior_pos_after
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {matrix : Mat2 QI} {box : RatBox} {active : List HermitianForm}
    (data : ApproximateBlockSectorBoxData kind exponent sector matrix box
      active) (form : HermitianForm)
    (member : form ∈ approximateBlockSectorBoxPriors active kind exponent
      sector matrix box)
    (positive : 0 < form.eval data.base) :
    0 < form.eval (point data) := by
  rcases mul_pos_iff.mp (preserved data form member) with signs | signs
  · exact signs.2
  · exact (not_lt_of_ge positive.le signs.1).elim

/-- Residual-tolerant entry produces the same strict block-and-box sample as
the exact-zero constructor. -/
def sample
    {kind : RawParser.BlockKind} {exponent : ℕ} {sector : Sector}
    {matrix : Mat2 QI} {box : RatBox} {active : List HermitianForm}
    (data : ApproximateBlockSectorBoxData kind exponent sector matrix box
      active) :
    BlockSectorBoxSample kind exponent sector matrix box where
  point := point data
  blockStrict := by
    intro form member
    by_cases activeMember : form ∈ active
    · exact entered data form activeMember
    · apply prior_pos_after data form
      · apply List.mem_append_left
        exact List.mem_filter.mpr ⟨member, by simp [activeMember]⟩
      · exact data.inactiveStrict form member activeMember
  boxStrict := by
    apply strictContains_of_all_boxForms_pos
    intro form member
    apply prior_pos_after data form
    · exact List.mem_append_right _ member
    · exact all_boxForms_pos_of_strictContains data.baseStrict form member

end ApproximateBlockSectorBoxData

end CCLSectorInteriorSelection
end FTA
