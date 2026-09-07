import mathlib.Tactic.QuotientFreeOmega
import mathlib.RFAP.ConstructivePolynomial

/-!
# Finite leading-term bookkeeping for dense polynomials

These predicates record only normalized finite coefficient counts and the
displayed leading coefficient.  Their closure lemmas are the algebraic input
for the fraction-free Schur recursion; no roots or evaluation-extensionality
principle is involved.
-/

namespace RFAP.ConstructivePolynomialLeading

abbrev Polynomial (K : Type*) :=
  RFAP.ComputablePolynomial.DensePolynomial K

open RFAP.ComputablePolynomial.DensePolynomial

variable {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]

structure LeadingTerm (p : Polynomial K) (degree : Nat)
    (coefficient : K) : Prop where
  normalized : p.normalize = p
  nonzero : p.isZero = false
  degree_eq : p.natDegree = degree
  coefficient_eq : p.leadingCoeff = coefficient

structure DegreeAtMost (p : Polynomial K) (degree : Nat) : Prop where
  normalized : p.normalize = p
  count_le : p.degreeCount ≤ degree + 1

structure DegreeBelow (p : Polynomial K) (degree : Nat) : Prop where
  normalized : p.normalize = p
  count_le : p.degreeCount ≤ degree

namespace LeadingTerm

/-- Transport a displayed leading-term certificate across three ordinary
equalities without using generated congruence for the predicate family. -/
theorem of_equal {p q : Polynomial K} {degree otherDegree : Nat}
    {coefficient otherCoefficient : K}
    (polynomialEqual : p = q) (degreeEqual : degree = otherDegree)
    (coefficientEqual : coefficient = otherCoefficient)
    (leading : LeadingTerm q otherDegree otherCoefficient) :
    LeadingTerm p degree coefficient := by
  cases polynomialEqual
  cases degreeEqual
  cases coefficientEqual
  exact leading

/-- The normalized representative of any displayed nonzero polynomial carries
its own finite leading term. -/
theorem normalizeSelf {p : Polynomial K} (nonzero : p.isZero = false) :
    LeadingTerm p.normalize p.natDegree p.leadingCoeff where
  normalized := normalize_normalize p
  nonzero := by simpa only [isZero_normalize] using nonzero
  degree_eq := natDegree_normalize p
  coefficient_eq := by
    change p.normalize.normalize.coeffs.headD 0 =
      p.normalize.coeffs.headD 0
    rw [normalize_normalize]

/-- A normalized nonzero polynomial carries its displayed leading term. -/
theorem ofNormalized {p : Polynomial K} (nonzero : p.isZero = false)
    (normalized : p.normalize = p) :
    LeadingTerm p p.natDegree p.leadingCoeff where
  normalized := normalized
  nonzero := nonzero
  degree_eq := rfl
  coefficient_eq := rfl

theorem count_eq {p : Polynomial K} {degree : Nat} {coefficient : K}
    (leading : LeadingTerm p degree coefficient) :
    p.degreeCount = degree + 1 := by
  rw [← leading.degree_eq]
  exact (natDegree_add_one_eq_degreeCount leading.nonzero).symm

theorem coefficient_ne_zero
    {p : Polynomial K} {degree : Nat} {coefficient : K}
    (leading : LeadingTerm p degree coefficient) : coefficient ≠ 0 := by
  rw [← leading.coefficient_eq]
  exact leadingCoeff_ne_zero leading.nonzero

theorem atMost {p : Polynomial K} {degree : Nat} {coefficient : K}
    (leading : LeadingTerm p degree coefficient) : DegreeAtMost p degree :=
  { normalized := leading.normalized
    count_le := leading.count_eq.le }

theorem mul {p q : Polynomial K} {pDegree qDegree : Nat}
    {pCoefficient qCoefficient : K}
    (left : LeadingTerm p pDegree pCoefficient)
    (right : LeadingTerm q qDegree qCoefficient) :
    LeadingTerm (p * q) (pDegree + qDegree)
      (pCoefficient * qCoefficient) where
  normalized := normalize_mul p q
  nonzero := isZero_mul_eq_false left.nonzero right.nonzero
  degree_eq := by
    rw [natDegree_mul left.nonzero right.nonzero,
      left.degree_eq, right.degree_eq]
  coefficient_eq := by
    rw [leadingCoeff_mul left.nonzero right.nonzero,
      left.coefficient_eq, right.coefficient_eq]

theorem constant {a : K} (nonzero : a ≠ 0) :
    LeadingTerm (constant a) 0 a where
  normalized := by
    apply ext
    change [a].dropWhile (· = 0) = [a]
    rw [List.dropWhile_cons_of_neg (by simp [nonzero])]
  nonzero := by
    change ([a].dropWhile (· = 0)).isEmpty = false
    rw [List.dropWhile_cons_of_neg (by simp [nonzero])]
    rfl
  degree_eq := by
    change ([a].dropWhile (· = 0)).length - 1 = 0
    rw [List.dropWhile_cons_of_neg (by simp [nonzero])]
    rfl
  coefficient_eq := by
    change ([a].dropWhile (· = 0)).headD 0 = a
    rw [List.dropWhile_cons_of_neg (by simp [nonzero])]
    rfl

/-- Negation preserves degree and negates the displayed leading coefficient. -/
theorem neg {p : Polynomial K} {degree : Nat} {coefficient : K}
    (leading : LeadingTerm p degree coefficient) :
    LeadingTerm (-p) degree (-coefficient) where
  normalized := normalize_neg p
  nonzero := by simpa only [isZero_neg] using leading.nonzero
  degree_eq := by simpa only [natDegree_neg] using leading.degree_eq
  coefficient_eq := by
    rw [leadingCoeff_neg, leading.coefficient_eq]

theorem scale {p : Polynomial K} {degree : Nat} {coefficient scalar : K}
    (scalarNonzero : scalar ≠ 0)
    (leading : LeadingTerm p degree coefficient) :
    LeadingTerm (RFAP.ComputablePolynomial.DensePolynomial.scale scalar p)
      degree (scalar * coefficient) := by
  have coefficientsNonempty : p.normalize.coeffs.isEmpty = false :=
    leading.nonzero
  have scaledCoefficients := scale_coeffs_of_ne_zero scalarNonzero p
  refine
    { normalized := normalize_scale scalar p
      nonzero := ?_
      degree_eq := ?_
      coefficient_eq := ?_ }
  · rw [isZero, normalize_scale, scaledCoefficients]
    cases coefficients : p.normalize.coeffs with
    | nil =>
        rw [coefficients] at coefficientsNonempty
        exact Bool.noConfusion coefficientsNonempty
    | cons head tail => rfl
  · rw [natDegree, degreeCount, normalize_scale, scaledCoefficients,
      List.length_map]
    have count := leading.count_eq
    rw [degreeCount] at count
    omega
  · rw [leadingCoeff, normalize_scale, scaledCoefficients]
    cases coefficients : p.normalize.coeffs with
    | nil =>
        rw [coefficients] at coefficientsNonempty
        exact Bool.noConfusion coefficientsNonempty
    | cons head tail =>
        simp only [List.map_cons, List.headD_cons]
        have coefficientIdentity := leading.coefficient_eq
        rw [leadingCoeff, coefficients, List.headD_cons] at coefficientIdentity
        rw [coefficientIdentity]

theorem shift {p : Polynomial K} {degree : Nat} {coefficient : K}
    (amount : Nat) (leading : LeadingTerm p degree coefficient) :
    LeadingTerm (RFAP.ComputablePolynomial.DensePolynomial.shift amount p)
      (degree + amount) coefficient := by
  have leadingNonzero := leading.coefficient_ne_zero
  have coefficientsIdentity :
      (RFAP.ComputablePolynomial.DensePolynomial.shift amount p).coeffs =
        p.normalize.coeffs ++ List.replicate amount 0 := by
    rw [RFAP.ComputablePolynomial.DensePolynomial.shift,
      if_neg (by simpa using leading.nonzero)]
  cases coefficients : p.normalize.coeffs with
  | nil =>
      have contradiction := leading.nonzero
      change p.normalize.coeffs.isEmpty = false at contradiction
      rw [coefficients] at contradiction
      exact Bool.noConfusion contradiction
  | cons head tail =>
      have headIdentity : head = coefficient := by
        have coefficientIdentity := leading.coefficient_eq
        rw [leadingCoeff, coefficients, List.headD_cons] at coefficientIdentity
        exact coefficientIdentity
      have headNonzero : head ≠ 0 := by simpa only [headIdentity]
      refine
        { normalized := ?_
          nonzero := ?_
          degree_eq := ?_
          coefficient_eq := ?_ }
      · apply ext
        rw [normalize_coeffs, coefficientsIdentity, coefficients]
        simp only [List.cons_append]
        rw [List.dropWhile_cons_of_neg (by simp [headNonzero])]
      · rw [isZero]
        have normalized :
            (RFAP.ComputablePolynomial.DensePolynomial.shift amount p).normalize =
              RFAP.ComputablePolynomial.DensePolynomial.shift amount p := by
          apply ext
          rw [normalize_coeffs, coefficientsIdentity, coefficients]
          simp only [List.cons_append]
          rw [List.dropWhile_cons_of_neg (by simp [headNonzero])]
        rw [normalized, coefficientsIdentity, coefficients]
        rfl
      · rw [natDegree, degreeCount]
        have normalized :
            (RFAP.ComputablePolynomial.DensePolynomial.shift amount p).normalize =
              RFAP.ComputablePolynomial.DensePolynomial.shift amount p := by
          apply ext
          rw [normalize_coeffs, coefficientsIdentity, coefficients]
          simp only [List.cons_append]
          rw [List.dropWhile_cons_of_neg (by simp [headNonzero])]
        rw [normalized, coefficientsIdentity, List.length_append,
          List.length_replicate]
        have count := leading.count_eq
        rw [degreeCount] at count
        rw [count]
        omega
      · rw [leadingCoeff]
        have normalized :
            (RFAP.ComputablePolynomial.DensePolynomial.shift amount p).normalize =
              RFAP.ComputablePolynomial.DensePolynomial.shift amount p := by
          apply ext
          rw [normalize_coeffs, coefficientsIdentity, coefficients]
          simp only [List.cons_append]
          rw [List.dropWhile_cons_of_neg (by simp [headNonzero])]
        rw [normalized, coefficientsIdentity, coefficients]
        simp only [List.cons_append, List.headD_cons, headIdentity]

theorem subBelow {p q : Polynomial K} {degree : Nat} {coefficient : K}
    (left : LeadingTerm p degree coefficient)
    (right : DegreeBelow q degree) :
    LeadingTerm (p - q) degree coefficient := by
  have shorter : q.degreeCount < p.degreeCount := by
    rw [left.count_eq]
    exact Nat.lt_succ_of_le right.count_le
  obtain ⟨out, hcoeffs, hout⟩ :=
    sub_coeffs_shape_of_degreeCount_lt left.nonzero left.normalized shorter
  have outputNonzero : (p - q).isZero = false := by
    rw [isZero, normalize_sub, hcoeffs]
    simp
  refine
    { normalized := normalize_sub p q
      nonzero := outputNonzero
      degree_eq := ?_
      coefficient_eq := ?_ }
  · have outputCount := natDegree_add_one_eq_degreeCount outputNonzero
    have leftCount := left.count_eq
    have exactOutputCount : (p - q).degreeCount = p.degreeCount := by
      rw [degreeCount, normalize_sub, hcoeffs]
      simp [hout]
    exact Nat.succ.inj
      (outputCount.trans (exactOutputCount.trans leftCount))
  · change (p - q).normalize.coeffs.headD 0 = coefficient
    rw [normalize_sub, hcoeffs]
    simpa only [List.headD_cons] using left.coefficient_eq

end LeadingTerm

namespace DegreeAtMost

/-- Transport a finite degree bound across displayed polynomial and degree
equalities without generated predicate congruence. -/
theorem of_equal {p q : Polynomial K} {degree otherDegree : Nat}
    (polynomialEqual : p = q) (degreeEqual : degree = otherDegree)
    (bounded : DegreeAtMost q otherDegree) : DegreeAtMost p degree := by
  cases polynomialEqual
  cases degreeEqual
  exact bounded

theorem zero (degree : Nat) : DegreeAtMost (0 : Polynomial K) degree where
  normalized := rfl
  count_le := Nat.zero_le _

theorem mono {p : Polynomial K} {smaller larger : Nat}
    (bounded : DegreeAtMost p smaller) (less : smaller ≤ larger) :
    DegreeAtMost p larger where
  normalized := bounded.normalized
  count_le := bounded.count_le.trans (Nat.succ_le_succ less)

theorem mul {p q : Polynomial K} {pDegree qDegree : Nat}
    (left : DegreeAtMost p pDegree)
    (right : DegreeAtMost q qDegree) :
    DegreeAtMost (p * q) (pDegree + qDegree) where
  normalized := normalize_mul p q
  count_le := by
    by_cases hp : p.isZero = true
    · rw [mul_eq_zero_of_isZero_left hp]
      exact Nat.zero_le _
    · have hpFalse : p.isZero = false := Bool.eq_false_of_not_eq_true hp
      by_cases hq : q.isZero = true
      · rw [mul_eq_zero_of_isZero_right hq]
        exact Nat.zero_le _
      · have hqFalse : q.isZero = false := Bool.eq_false_of_not_eq_true hq
        have hpPositive := degreeCount_pos_of_isZero_false hpFalse
        have hqPositive := degreeCount_pos_of_isZero_false hqFalse
        have bound := degreeCount_mul_le p q
        have hpBound := left.count_le
        have hqBound := right.count_le
        omega

theorem sub {p q : Polynomial K} {degree : Nat}
    (left : DegreeAtMost p degree) (right : DegreeAtMost q degree) :
    DegreeAtMost (p - q) degree where
  normalized := normalize_sub p q
  count_le := by
    exact (degreeCount_sub_le_of_normalized left.normalized).trans
      (max_le left.count_le right.count_le)

theorem toBelowSucc {p : Polynomial K} {degree : Nat}
    (bounded : DegreeAtMost p degree) : DegreeBelow p (degree + 1) where
  normalized := bounded.normalized
  count_le := bounded.count_le

end DegreeAtMost

namespace DegreeBelow

/-- Transport a strict finite degree bound across displayed polynomial and
degree equalities without generated predicate congruence. -/
theorem of_equal {p q : Polynomial K} {degree otherDegree : Nat}
    (polynomialEqual : p = q) (degreeEqual : degree = otherDegree)
    (bounded : DegreeBelow q otherDegree) : DegreeBelow p degree := by
  cases polynomialEqual
  cases degreeEqual
  exact bounded

/-- A normalized nonzero polynomial of strictly smaller natural degree is
strictly below the displayed target degree in coefficient count. -/
theorem ofNatDegreeLt {p : Polynomial K} {degree : Nat}
    (nonzero : p.isZero = false) (normalized : p.normalize = p)
    (smaller : p.natDegree < degree) : DegreeBelow p degree where
  normalized := normalized
  count_le := by
    have count := natDegree_add_one_eq_degreeCount nonzero
    omega

theorem zero (degree : Nat) : DegreeBelow (0 : Polynomial K) degree where
  normalized := rfl
  count_le := Nat.zero_le _

theorem mono {p : Polynomial K} {smaller larger : Nat}
    (below : DegreeBelow p smaller) (less : smaller ≤ larger) :
    DegreeBelow p larger where
  normalized := below.normalized
  count_le := below.count_le.trans less

theorem toAtMost {p : Polynomial K} {degree : Nat}
    (below : DegreeBelow p degree) : DegreeAtMost p degree where
  normalized := below.normalized
  count_le := below.count_le.trans (Nat.le_succ _)

theorem neg {p : Polynomial K} {degree : Nat}
    (below : DegreeBelow p degree) : DegreeBelow (-p) degree where
  normalized := normalize_neg p
  count_le := by simpa only [degreeCount_neg] using below.count_le

theorem mulAtMost {p q : Polynomial K} {pDegree qDegree : Nat}
    (left : DegreeBelow p pDegree)
    (right : DegreeAtMost q qDegree) :
    DegreeBelow (p * q) (pDegree + qDegree) where
  normalized := normalize_mul p q
  count_le := by
    by_cases hp : p.isZero = true
    · rw [mul_eq_zero_of_isZero_left hp]
      exact Nat.zero_le _
    · have hpFalse : p.isZero = false := Bool.eq_false_of_not_eq_true hp
      by_cases hq : q.isZero = true
      · rw [mul_eq_zero_of_isZero_right hq]
        exact Nat.zero_le _
      · have hqFalse : q.isZero = false := Bool.eq_false_of_not_eq_true hq
        have hpPositive := degreeCount_pos_of_isZero_false hpFalse
        have hqPositive := degreeCount_pos_of_isZero_false hqFalse
        have bound := degreeCount_mul_le p q
        have hpBound := left.count_le
        have hqBound := right.count_le
        omega

theorem atMostMul {p q : Polynomial K} {pDegree qDegree : Nat}
    (left : DegreeAtMost p pDegree)
    (right : DegreeBelow q qDegree) :
    DegreeBelow (p * q) (pDegree + qDegree) where
  normalized := normalize_mul p q
  count_le := by
    by_cases hp : p.isZero = true
    · rw [mul_eq_zero_of_isZero_left hp]
      exact Nat.zero_le _
    · have hpFalse : p.isZero = false := Bool.eq_false_of_not_eq_true hp
      by_cases hq : q.isZero = true
      · rw [mul_eq_zero_of_isZero_right hq]
        exact Nat.zero_le _
      · have hqFalse : q.isZero = false := Bool.eq_false_of_not_eq_true hq
        have hpPositive := degreeCount_pos_of_isZero_false hpFalse
        have hqPositive := degreeCount_pos_of_isZero_false hqFalse
        have bound := degreeCount_mul_le p q
        have hpBound := left.count_le
        have hqBound := right.count_le
        omega

theorem sub {p q : Polynomial K} {degree : Nat}
    (left : DegreeBelow p degree) (right : DegreeBelow q degree) :
    DegreeBelow (p - q) degree where
  normalized := normalize_sub p q
  count_le := by
    exact (degreeCount_sub_le_of_normalized left.normalized).trans
      (max_le left.count_le right.count_le)

end DegreeBelow

namespace LeadingTerm

/-- Equal-degree leading terms add without cancellation when their displayed
leading coefficients have nonzero sum. -/
theorem add {p q : Polynomial K} {degree : Nat} {leftCoefficient rightCoefficient : K}
    (left : LeadingTerm p degree leftCoefficient)
    (right : LeadingTerm q degree rightCoefficient)
    (sumNonzero : leftCoefficient + rightCoefficient ≠ 0) :
    LeadingTerm (p + q) degree (leftCoefficient + rightCoefficient) := by
  obtain ⟨leftTail, leftCoefficients, leftLength⟩ :=
    normalized_coeffs_shape left.nonzero
  obtain ⟨rightTail, rightCoefficients, rightLength⟩ :=
    normalized_coeffs_shape right.nonzero
  rw [left.normalized, left.coefficient_eq] at leftCoefficients
  rw [right.normalized, right.coefficient_eq] at rightCoefficients
  have leftCount := left.count_eq
  have rightCount := right.count_eq
  have outputCoefficients :
      (p + q).coeffs =
        (leftCoefficient + rightCoefficient) ::
          List.zipWith (· + ·) leftTail rightTail := by
    change (RFAP.ComputablePolynomial.DensePolynomial.add p q).coeffs = _
    simp only [RFAP.ComputablePolynomial.DensePolynomial.add,
      leftCoefficients, rightCoefficients, List.length_cons]
    rw [leftLength, rightLength, left.degree_eq, right.degree_eq,
      max_self, Nat.sub_self]
    simp only [RFAP.ComputablePolynomial.DensePolynomial.padLeft,
      List.replicate_zero, List.nil_append, List.zipWith_cons_cons]
    change ((leftCoefficient + rightCoefficient) ::
      List.zipWith (· + ·) leftTail rightTail).dropWhile (· = 0) = _
    rw [List.dropWhile_cons_of_neg (by simpa using sumNonzero)]
  have outputNonzero : (p + q).isZero = false := by
    rw [isZero, normalize_add, outputCoefficients]
    rfl
  refine
    { normalized := normalize_add p q
      nonzero := outputNonzero
      degree_eq := ?_
      coefficient_eq := ?_ }
  · have outputCount := natDegree_add_one_eq_degreeCount outputNonzero
    have outputLength :
        (List.zipWith (· + ·) leftTail rightTail).length = degree := by
      rw [List.length_zipWith, leftLength, rightLength, left.degree_eq,
        right.degree_eq, min_self]
    rw [degreeCount, normalize_add, outputCoefficients,
      List.length_cons, outputLength] at outputCount
    exact Nat.add_right_cancel outputCount
  · rw [leadingCoeff, normalize_add, outputCoefficients]
    rfl

theorem addBelow {p q : Polynomial K} {degree : Nat} {coefficient : K}
    (left : LeadingTerm p degree coefficient)
    (right : DegreeBelow q degree) :
    LeadingTerm (p + q) degree coefficient := by
  have result := left.subBelow (DegreeBelow.neg right)
  change LeadingTerm (p + - -q) degree coefficient at result
  rw [RFAP.ComputablePolynomial.DensePolynomial.neg_neg,
    right.normalized] at result
  exact result

/-- Addition with the higher-degree term on the right preserves that term. -/
theorem belowAdd {p q : Polynomial K} {degree : Nat} {coefficient : K}
    (left : DegreeBelow p degree)
    (right : LeadingTerm q degree coefficient) :
    LeadingTerm (p + q) degree coefficient := by
  rw [add_comm_direct]
  exact right.addBelow left

/-- Subtracting a higher-degree right term exposes its negated leading term. -/
theorem belowSub {p q : Polynomial K} {degree : Nat} {coefficient : K}
    (left : DegreeBelow p degree)
    (right : LeadingTerm q degree coefficient) :
    LeadingTerm (p - q) degree (-coefficient) := by
  change LeadingTerm (p + -q) degree (-coefficient)
  exact (right.neg).belowAdd left

/-- A zero finite coefficient difference between normalized nonzero
polynomials forces equality of their natural degrees. -/
theorem natDegree_eq_of_sub_isZero
    {p q : Polynomial K} (pNonzero : p.isZero = false)
    (qNonzero : q.isZero = false) (pNormalized : p.normalize = p)
    (qNormalized : q.normalize = q) (differenceZero : (p - q).isZero = true) :
    p.natDegree = q.natDegree := by
  by_cases leftSmaller : p.natDegree < q.natDegree
  · have leftBelow := DegreeBelow.ofNatDegreeLt pNonzero pNormalized
      leftSmaller
    have rightLeading := LeadingTerm.ofNormalized qNonzero qNormalized
    have differenceNonzero := (rightLeading.belowSub leftBelow).nonzero
    rw [differenceZero] at differenceNonzero
    exact Bool.noConfusion differenceNonzero
  · by_cases rightSmaller : q.natDegree < p.natDegree
    · have rightBelow := DegreeBelow.ofNatDegreeLt qNonzero qNormalized
        rightSmaller
      have leftLeading := LeadingTerm.ofNormalized pNonzero pNormalized
      have differenceNonzero := (leftLeading.subBelow rightBelow).nonzero
      rw [differenceZero] at differenceNonzero
      exact Bool.noConfusion differenceNonzero
    · exact Nat.le_antisymm (Nat.le_of_not_gt rightSmaller)
        (Nat.le_of_not_gt leftSmaller)

end LeadingTerm

end RFAP.ConstructivePolynomialLeading
