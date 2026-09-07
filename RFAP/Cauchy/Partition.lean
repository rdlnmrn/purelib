import mathlib.Tactic.QuotientFreeRing
import RFAP.Cauchy.Resolution
import RFAP.Isolation.SafeCandidates

/-!
# Choice-free finite partitions for the Cauchy product formula

Six nonzero coordinate polynomials have only finitely many displayed zeros.
A bounded central-third scan therefore supplies every recursive cut without
forming a root set.  Coefficient-computed local radii resolve the two outer
endpoint cells and every interior cell after an explicit finite depth.
-/

namespace RFAP.CauchyPartition

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Interval := RFAP.PathClearance.Interval
abbrev ClearanceCertificate := RFAP.PathClearance.Certificate

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.PathClearance
open RFAP.IntervalSign
open RFAP.CauchyProduct
open RFAP.CauchyResolution
open RFAP.SafeCandidates

/-- Product of the six coordinate polynomials whose displayed nonzero values
are the safe interior partition endpoints. -/
def productEventGuard
    (A B C D E H : Polynomial) : Polynomial :=
  ((((A * B) * C) * D) * E) * H

theorem productEventGuard_isZero_false
    {A B C D E H : Polynomial}
    (A_nonzero : A.isZero = false) (B_nonzero : B.isZero = false)
    (C_nonzero : C.isZero = false) (D_nonzero : D.isZero = false)
    (E_nonzero : E.isZero = false) (H_nonzero : H.isZero = false) :
    (productEventGuard A B C D E H).isZero = false := by
  unfold productEventGuard
  exact isZero_mul_eq_false
    (isZero_mul_eq_false
      (isZero_mul_eq_false
        (isZero_mul_eq_false
          (isZero_mul_eq_false A_nonzero B_nonzero) C_nonzero)
        D_nonzero)
      E_nonzero)
    H_nonzero

theorem productEventGuard_eval_ne_zero_components
    (A B C D E H : Polynomial) (x : Coordinate)
    (guardNonzero : (productEventGuard A B C D E H).eval x ≠ 0) :
    A.eval x ≠ 0 ∧ B.eval x ≠ 0 ∧
      C.eval x ≠ 0 ∧ D.eval x ≠ 0 ∧
      E.eval x ≠ 0 ∧ H.eval x ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro zero <;>
    apply guardNonzero <;>
    simp [productEventGuard, eval_mul, zero]

/-- A single positive squared-radius threshold covers every kind of leaf:
ordinary interior, left outer endpoint, and right outer endpoint. -/
def completeProductResolutionRadiusSq
    {A B C D E H : Polynomial} {root : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) : Coordinate :=
  min (localProductResolutionRadiusSq left right realIdentity imagIdentity)
    (min
      (endpointProductResolutionRadiusSq left right realIdentity imagIdentity
        root.lower)
      (endpointProductResolutionRadiusSq left right realIdentity imagIdentity
        root.upper))

theorem completeProductResolutionRadiusSq_pos
    {A B C D E H : Polynomial} {root : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    0 < completeProductResolutionRadiusSq left right
      realIdentity imagIdentity := by
  unfold completeProductResolutionRadiusSq
  exact lt_min
    (localProductResolutionRadiusSq_pos left right realIdentity imagIdentity)
    (lt_min
      (endpointProductResolutionRadiusSq_pos left right
        realIdentity imagIdentity root.lower)
      (endpointProductResolutionRadiusSq_pos left right
        realIdentity imagIdentity root.upper))

/-- Width threshold below both one and the complete squared-radius threshold.
The extra bound by one converts a strict width inequality to a strict square
inequality without square roots. -/
def completeProductLeafWidth
    {A B C D E H : Polynomial} {root : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) : Coordinate :=
  min 1 (completeProductResolutionRadiusSq left right
    realIdentity imagIdentity)

theorem completeProductLeafWidth_pos
    {A B C D E H : Polynomial} {root : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    0 < completeProductLeafWidth left right realIdentity imagIdentity :=
  lt_min (by decide)
    (completeProductResolutionRadiusSq_pos left right
      realIdentity imagIdentity)

theorem radius_lt_of_width_lt
    {interval : Interval} (proper : interval.lower < interval.upper)
    {radiusBound : Coordinate}
    (widthSmall : interval.upper - interval.lower < min 1 radiusBound) :
    sampleRadiusSq interval interval.lower < radiusBound := by
  let width := interval.upper - interval.lower
  have widthPositive : 0 < width :=
    RFAP.ConstructiveFraction.sub_pos_direct proper
  have widthBelowOne : width < 1 :=
    widthSmall.trans_le (min_le_left _ _)
  have widthBelowRadius : width < radiusBound :=
    widthSmall.trans_le (min_le_right _ _)
  have squareBelowWidth : width ^ 2 < width := by
    have multiplied :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
        widthBelowOne widthPositive
    simpa only [pow_two, one_mul] using multiplied
  rw [sampleRadiusSq_lower_eq_widthSq]
  exact squareBelowWidth.trans widthBelowRadius

/-- Every sufficiently narrow guarded subinterval is one of the three
constructively resolved leaf forms.  The two ambient endpoints are allowed
to lie on coordinate axes, but no leaf may contain both of them. -/
theorem auxiliaryProductFormula_of_guarded_leaf
    {A B C D E H : Polynomial} {root interval : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (widthSmall : interval.upper - interval.lower <
      completeProductLeafWidth left right realIdentity imagIdentity)
    (lowerGuard : interval.lower = root.lower ∨
      (productEventGuard A B C D E H).eval interval.lower ≠ 0)
    (upperGuard : interval.upper = root.upper ∨
      (productEventGuard A B C D E H).eval interval.upper ≠ 0)
    (separated : ¬(interval.lower = root.lower ∧
      interval.upper = root.upper))
    (leftRootStart : A.eval root.lower ≠ 0 ∨ B.eval root.lower ≠ 0)
    (rightRootStart : C.eval root.lower ≠ 0 ∨ D.eval root.lower ≠ 0)
    (leftRootStop : A.eval root.upper ≠ 0 ∨ B.eval root.upper ≠ 0)
    (rightRootStop : C.eval root.upper ≠ 0 ∨ D.eval root.upper ≠ 0) :
    AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  have radius : sampleRadiusSq interval interval.lower <
      completeProductResolutionRadiusSq left right
        realIdentity imagIdentity :=
    radius_lt_of_width_lt proper widthSmall
  by_cases lowerAtRoot : interval.lower = root.lower
  · have upperNotRoot : interval.upper ≠ root.upper := by
      intro upperAtRoot
      exact separated ⟨lowerAtRoot, upperAtRoot⟩
    have upperClear := upperGuard.resolve_left upperNotRoot
    rcases productEventGuard_eval_ne_zero_components
        A B C D E H interval.upper upperClear with
      ⟨_AUpper, BUpper, _CUpper, DUpper, _EUpper, HUpper⟩
    apply auxiliaryProductFormula_of_leftEndpoint_refined_radiusSq
      left right realIdentity imagIdentity refines
    · simpa only [lowerAtRoot] using
        radius.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    · simpa only [lowerAtRoot] using leftRootStart
    · simpa only [lowerAtRoot] using rightRootStart
    · exact BUpper
    · exact DUpper
    · exact HUpper
  · have lowerClear := lowerGuard.resolve_left lowerAtRoot
    rcases productEventGuard_eval_ne_zero_components
        A B C D E H interval.lower lowerClear with
      ⟨ALower, BLower, CLower, DLower, ELower, HLower⟩
    by_cases upperAtRoot : interval.upper = root.upper
    · apply auxiliaryProductFormula_of_rightEndpoint_refined_radiusSq
        left right realIdentity imagIdentity refines
      · simpa only [upperAtRoot] using
          radius.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      · simpa only [upperAtRoot] using leftRootStop
      · simpa only [upperAtRoot] using rightRootStop
      · exact BLower
      · exact DLower
      · exact HLower
    · have upperClear := upperGuard.resolve_left upperAtRoot
      rcases productEventGuard_eval_ne_zero_components
          A B C D E H interval.upper upperClear with
        ⟨AUpper, BUpper, CUpper, DUpper, EUpper, HUpper⟩
      apply auxiliaryProductFormula_of_refined_radiusSq
        left right realIdentity imagIdentity refines
      · exact radius.trans_le (min_le_left _ _)
      · exact ALower
      · exact BLower
      · exact CLower
      · exact DLower
      · exact ELower
      · exact HLower
      · exact AUpper
      · exact BUpper
      · exact CUpper
      · exact DUpper
      · exact EUpper
      · exact HUpper

/-- Fixed-depth central-third subdivision.  Every emitted cut is selected by
the bounded finite guard scan, and the recursive formulas telescope exactly. -/
theorem auxiliaryProductFormulaAtDepth
    {A B C D E H : Polynomial}
    (A_nonzero : A.isZero = false) (B_nonzero : B.isZero = false)
    (C_nonzero : C.isZero = false) (D_nonzero : D.isZero = false)
    (E_nonzero : E.isZero = false) (H_nonzero : H.isZero = false)
    {root : Interval}
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (leftRootStart : A.eval root.lower ≠ 0 ∨ B.eval root.lower ≠ 0)
    (rightRootStart : C.eval root.lower ≠ 0 ∨ D.eval root.lower ≠ 0)
    (leftRootStop : A.eval root.upper ≠ 0 ∨ B.eval root.upper ≠ 0)
    (rightRootStop : C.eval root.upper ≠ 0 ∨ D.eval root.upper ≠ 0)
    (fuel : Nat) (interval : Interval)
    (refines : interval.Refines root)
    (proper : interval.lower < interval.upper)
    (lowerGuard : interval.lower = root.lower ∨
      (productEventGuard A B C D E H).eval interval.lower ≠ 0)
    (upperGuard : interval.upper = root.upper ∨
      (productEventGuard A B C D E H).eval interval.upper ≠ 0)
    (separated : fuel ≠ 0 ∨
      ¬(interval.lower = root.lower ∧ interval.upper = root.upper))
    (sufficient : (2 / 3 : Coordinate) ^ fuel *
      (interval.upper - interval.lower) <
        completeProductLeafWidth left right realIdentity imagIdentity) :
    AuxiliaryProductFormula A B C D E H
      interval.lower interval.upper := by
  induction fuel generalizing interval with
  | zero =>
      rcases separated with fuelNonzero | separated
      · exact (fuelNonzero rfl).elim
      · apply auxiliaryProductFormula_of_guarded_leaf
          left right realIdentity imagIdentity refines proper
        · simpa only [pow_zero, one_mul] using sufficient
        · exact lowerGuard
        · exact upperGuard
        · exact separated
        · exact leftRootStart
        · exact rightRootStart
        · exact leftRootStop
        · exact rightRootStop
  | succ fuel inductionHypothesis =>
      let guard := productEventGuard A B C D E H
      have guardNonzero : guard.isZero = false :=
        productEventGuard_isZero_false A_nonzero B_nonzero
          C_nonzero D_nonzero E_nonzero H_nonzero
      let cut := centralSearchValue guard guard.natDegree proper
        guardNonzero le_rfl
      have cutSpec : guard.eval cut ≠ 0 ∧
          interval.lower < cut ∧ cut < interval.upper := by
        simpa only [guard, cut] using centralSearchValue_spec
          guard guard.natDegree proper guardNonzero le_rfl
      have contraction : cut - interval.lower <
            (2 / 3 : Coordinate) *
              (interval.upper - interval.lower) ∧
          interval.upper - cut <
            (2 / 3 : Coordinate) *
              (interval.upper - interval.lower) := by
        simpa only [guard, cut] using centralSearchValue_contraction
          guard guard.natDegree proper guardNonzero le_rfl
      let leftInterval : Interval :=
        { lower := interval.lower
          upper := cut
          valid := cutSpec.2.1.le }
      let rightInterval : Interval :=
        { lower := cut
          upper := interval.upper
          valid := cutSpec.2.2.le }
      have leftRefines : leftInterval.Refines root := by
        exact ⟨refines.1, cutSpec.2.2.le.trans refines.2⟩
      have rightRefines : rightInterval.Refines root := by
        exact ⟨refines.1.trans cutSpec.2.1.le, refines.2⟩
      have leftSeparated :
          ¬(leftInterval.lower = root.lower ∧
            leftInterval.upper = root.upper) := by
        intro both
        have cutAtUpper : cut = root.upper := by
          simpa only [leftInterval] using both.2
        have upperBound : interval.upper ≤ cut := by
          rw [cutAtUpper]
          exact refines.2
        exact (not_lt_of_ge upperBound) cutSpec.2.2
      have rightSeparated :
          ¬(rightInterval.lower = root.lower ∧
            rightInterval.upper = root.upper) := by
        intro both
        have cutAtLower : cut = root.lower := by
          simpa only [rightInterval] using both.1
        have lowerBound : cut ≤ interval.lower := by
          rw [cutAtLower]
          exact refines.1
        exact (not_lt_of_ge lowerBound) cutSpec.2.1
      have powerPositive : 0 < (2 / 3 : Coordinate) ^ fuel :=
        RFAP.ConstructiveFraction.pow_pos_direct (by decide) fuel
      have leftSufficient : (2 / 3 : Coordinate) ^ fuel *
          (leftInterval.upper - leftInterval.lower) <
            completeProductLeafWidth left right realIdentity imagIdentity := by
        calc
          (2 / 3 : Coordinate) ^ fuel *
              (leftInterval.upper - leftInterval.lower) <
              (2 / 3 : Coordinate) ^ fuel *
                ((2 / 3 : Coordinate) *
                  (interval.upper - interval.lower)) :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              powerPositive
              (by simpa only [leftInterval] using contraction.1)
          _ = (2 / 3 : Coordinate) ^ Nat.succ fuel *
              (interval.upper - interval.lower) := by
            rw [pow_succ]
            ring1
          _ < completeProductLeafWidth left right
              realIdentity imagIdentity := sufficient
      have rightSufficient : (2 / 3 : Coordinate) ^ fuel *
          (rightInterval.upper - rightInterval.lower) <
            completeProductLeafWidth left right realIdentity imagIdentity := by
        calc
          (2 / 3 : Coordinate) ^ fuel *
              (rightInterval.upper - rightInterval.lower) <
              (2 / 3 : Coordinate) ^ fuel *
                ((2 / 3 : Coordinate) *
                  (interval.upper - interval.lower)) :=
            RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
              powerPositive
              (by simpa only [rightInterval] using contraction.2)
          _ = (2 / 3 : Coordinate) ^ Nat.succ fuel *
              (interval.upper - interval.lower) := by
            rw [pow_succ]
            ring1
          _ < completeProductLeafWidth left right
              realIdentity imagIdentity := sufficient
      have leftFormula := inductionHypothesis leftInterval leftRefines
        (by simpa only [leftInterval] using cutSpec.2.1)
        (by simpa only [leftInterval] using lowerGuard)
        (Or.inr (by simpa only [leftInterval, guard] using cutSpec.1))
        (Or.inr leftSeparated) leftSufficient
      have rightFormula := inductionHypothesis rightInterval rightRefines
        (by simpa only [rightInterval] using cutSpec.2.2)
        (Or.inr (by simpa only [rightInterval, guard] using cutSpec.1))
        (by simpa only [rightInterval] using upperGuard)
        (Or.inr rightSeparated) rightSufficient
      exact leftFormula.add rightFormula

/-- Complete nondegenerate auxiliary product formula.  The construction uses
one finite safe-cut tree at a coefficient-computed natural depth. -/
theorem auxiliaryProductFormula_of_nondegenerate_coordinates
    {A B C D E H : Polynomial}
    (A_nonzero : A.isZero = false) (B_nonzero : B.isZero = false)
    (C_nonzero : C.isZero = false) (D_nonzero : D.isZero = false)
    (E_nonzero : E.isZero = false) (H_nonzero : H.isZero = false)
    {root : Interval} (proper : root.lower < root.upper)
    (left : ClearanceCertificate A B root)
    (right : ClearanceCertificate C D root)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x)
    (leftRootStart : A.eval root.lower ≠ 0 ∨ B.eval root.lower ≠ 0)
    (rightRootStart : C.eval root.lower ≠ 0 ∨ D.eval root.lower ≠ 0)
    (leftRootStop : A.eval root.upper ≠ 0 ∨ B.eval root.upper ≠ 0)
    (rightRootStop : C.eval root.upper ≠ 0 ∨ D.eval root.upper ≠ 0) :
    AuxiliaryProductFormula A B C D E H root.lower root.upper := by
  let leafWidth := completeProductLeafWidth
    left right realIdentity imagIdentity
  have leafWidthPositive : 0 < leafWidth := by
    simpa only [leafWidth] using
      completeProductLeafWidth_pos left right realIdentity imagIdentity
  let depth := geometricDepth (root.upper - root.lower) (leafWidth / 2)
  have geometric : (2 / 3 : Coordinate) ^ depth *
      (root.upper - root.lower) ≤ leafWidth / 2 := by
    simpa only [depth] using
      (geometricDepth_sufficient
        (width := root.upper - root.lower) (epsilon := leafWidth / 2)
        (show 0 ≤ root.upper - root.lower from
          (RFAP.ConstructiveFraction.sub_pos_direct proper).le)
        (RFAP.ConstructiveFraction.div_pos_direct leafWidthPositive
          (show (0 : Coordinate) < 2 by decide)))
  have halfBelow : leafWidth / 2 < leafWidth := by
    have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Coordinate) < 1 by decide) leafWidthPositive
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    have halfInverse : (2 : Coordinate)⁻¹ = 1 / 2 := by
      rw [RFAP.ExplicitField.div_eq_mul_inv]
      exact (RFAP.ConstructiveFraction.one_mul _).symm
    rw [halfInverse]
    simpa only [RFAP.ConstructiveFraction.mul_comm, one_mul] using scaled
  have baseSufficient : (2 / 3 : Coordinate) ^ depth *
      (root.upper - root.lower) < leafWidth :=
    geometric.trans_lt halfBelow
  have widthNonnegative : 0 ≤ root.upper - root.lower :=
    (RFAP.ConstructiveFraction.sub_pos_direct proper).le
  have contractionLeOne : (2 / 3 : Coordinate) ≤ 1 := by decide
  have contractionWidthLe : (2 / 3 : Coordinate) *
      (root.upper - root.lower) ≤ root.upper - root.lower := by
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      contractionLeOne widthNonnegative
    simpa only [one_mul] using scaled
  have depthPowerNonnegative : 0 ≤ (2 / 3 : Coordinate) ^ depth :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) depth
  have sufficient : (2 / 3 : Coordinate) ^ Nat.succ depth *
      (root.upper - root.lower) < leafWidth := by
    calc
      (2 / 3 : Coordinate) ^ Nat.succ depth *
          (root.upper - root.lower) =
          (2 / 3 : Coordinate) ^ depth *
            ((2 / 3 : Coordinate) *
              (root.upper - root.lower)) := by
        rw [pow_succ]
        ring1
      _ ≤ (2 / 3 : Coordinate) ^ depth *
          (root.upper - root.lower) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          contractionWidthLe depthPowerNonnegative
      _ < leafWidth := baseSufficient
  exact auxiliaryProductFormulaAtDepth
    A_nonzero B_nonzero C_nonzero D_nonzero E_nonzero H_nonzero
    left right realIdentity imagIdentity
    leftRootStart rightRootStart leftRootStop rightRootStop
    (Nat.succ depth) root ⟨le_rfl, le_rfl⟩ proper
    (Or.inl rfl) (Or.inl rfl) (Or.inl (Nat.succ_ne_zero depth))
    (by simpa only [leafWidth] using sufficient)

end RFAP.CauchyPartition
