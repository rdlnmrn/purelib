import mathlib.Tactic.QuotientFreeRing
import RFAP.Winding

/-!
# Finite clearance certificates over constructive coordinates

Two displayed dense Bézout cofactors give a pointwise identity for a pair of
coordinate polynomials.  Finite Horner bounds then turn that identity into a
positive, uniform sum-of-squares bound on a closed constructive interval.
Four such bounds combine into a quantitative box-boundary certificate.

All bounds are rational finite data.  The proofs use neither a root set nor
an infinite-field extensionality argument.
-/

namespace RFAP.PathClearance

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Box := RFAP.Boxes.Box

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.Winding

/-- A closed interval over constructive coordinates. -/
structure Interval where
  lower : Coordinate
  upper : Coordinate
  valid : lower ≤ upper
deriving DecidableEq

namespace Interval

def Contains (interval : Interval) (x : Coordinate) : Prop :=
  interval.lower ≤ x ∧ x ≤ interval.upper

/-- Inclusion of one displayed rational interval in another. -/
def Refines (interval root : Interval) : Prop :=
  root.lower ≤ interval.lower ∧ interval.upper ≤ root.upper

instance containsDecidable (interval : Interval) (x : Coordinate) :
    Decidable (interval.Contains x) := by
  unfold Contains
  infer_instance

instance refinesDecidable (interval root : Interval) :
    Decidable (interval.Refines root) := by
  unfold Refines
  infer_instance

/-- Uniform bound for the square of every member of the interval. -/
def squareBound (interval : Interval) : Coordinate :=
  max (interval.lower ^ 2) (interval.upper ^ 2)

theorem squareBound_nonneg (interval : Interval) : 0 ≤ interval.squareBound :=
  (RFAP.ConstructiveFraction.sq_nonneg_direct interval.lower).trans
    (le_max_left _ _)

theorem sq_le_squareBound {interval : Interval} {x : Coordinate}
    (inside : interval.Contains x) : x ^ 2 ≤ interval.squareBound :=
  RFAP.Boxes.Box.sq_le_endpoint_max inside.1 inside.2

theorem squareBound_le_of_refines {interval root : Interval}
    (refines : interval.Refines root) :
    interval.squareBound ≤ root.squareBound := by
  apply max_le
  · exact root.sq_le_squareBound ⟨refines.1, interval.valid.trans refines.2⟩
  · exact root.sq_le_squareBound ⟨refines.1.trans interval.valid, refines.2⟩

end Interval

private theorem twice_nonneg {a : Coordinate} (nonnegative : 0 ≤ a) :
    0 ≤ 2 * a := by
  calc
    0 = 0 + 0 := by ring1
    _ ≤ a + a := add_le_add nonnegative nonnegative
    _ = 2 * a := by ring1

private theorem twice_le_twice {a b : Coordinate} (less : a ≤ b) :
    2 * a ≤ 2 * b := by
  calc
    2 * a = a + a := by ring1
    _ ≤ b + b := add_le_add less less
    _ = 2 * b := by ring1

private theorem add_sq_le_two (a b : Coordinate) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  apply sub_nonneg.mp
  calc
    0 ≤ (a - b) ^ 2 := RFAP.ConstructiveFraction.sq_nonneg_direct _
    _ = 2 * (a ^ 2 + b ^ 2) - (a + b) ^ 2 := by ring1

/-- One Horner step for a squared evaluation majorant. -/
def evalSqBoundStep (radiusSq bound coefficient : Coordinate) : Coordinate :=
  2 * (bound * radiusSq + coefficient ^ 2)

/-- Finite Horner majorant for `p(t)^2` throughout an interval. -/
def evalSqBound (p : Polynomial) (interval : Interval) : Coordinate :=
  p.coeffs.foldl (evalSqBoundStep interval.squareBound) 0

/-- Monotonicity of one squared Horner-majorant step against separately
displayed radius, accumulator, and coefficient-square ceilings. -/
theorem evalSqBoundStep_le
    {radius bound coefficient radiusCeiling boundCeiling
      coefficientSqCeiling : Coordinate}
    (radiusNonnegative : 0 ≤ radius)
    (radiusLe : radius ≤ radiusCeiling)
    (boundLe : bound ≤ boundCeiling)
    (coefficientSqLe : coefficient ^ 2 ≤ coefficientSqCeiling)
    (boundCeilingNonnegative : 0 ≤ boundCeiling) :
    evalSqBoundStep radius bound coefficient ≤
      2 * (boundCeiling * radiusCeiling + coefficientSqCeiling) := by
  unfold evalSqBoundStep
  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
  · exact add_le_add
      (RFAP.ConstructiveFraction.mul_le_mul_direct boundLe radiusLe
        radiusNonnegative boundCeilingNonnegative)
      coefficientSqLe
  · decide

/-- A three-coefficient polynomial needs exactly three displayed Horner
steps.  This compact bound lets explicit finite calculations compare simple
coefficient-square ceilings without normalizing a large rational fold. -/
theorem evalSqBound_three_le
    (polynomial : Polynomial) (a b c : Coordinate)
    (coefficients : polynomial.coeffs = [a, b, c])
    (interval : Interval)
    (radiusCeiling aSqCeiling bSqCeiling cSqCeiling : Coordinate)
    (radiusCeilingNonnegative : 0 ≤ radiusCeiling)
    (aSqCeilingNonnegative : 0 ≤ aSqCeiling)
    (bSqCeilingNonnegative : 0 ≤ bSqCeiling)
    (radiusLe : interval.squareBound ≤ radiusCeiling)
    (aSqLe : a ^ 2 ≤ aSqCeiling)
    (bSqLe : b ^ 2 ≤ bSqCeiling)
    (cSqLe : c ^ 2 ≤ cSqCeiling) :
    evalSqBound polynomial interval ≤
      2 *
        ((2 * ((2 * aSqCeiling) * radiusCeiling + bSqCeiling)) *
            radiusCeiling +
          cSqCeiling) := by
  unfold evalSqBound
  rw [coefficients]
  simp only [List.foldl_cons, List.foldl_nil]
  have firstLe : evalSqBoundStep interval.squareBound 0 a ≤
      2 * aSqCeiling := by
    convert evalSqBoundStep_le interval.squareBound_nonneg radiusLe le_rfl
      aSqLe (show (0 : Coordinate) ≤ 0 by exact le_rfl) using 1
    all_goals ring1
  have firstCeilingNonnegative : 0 ≤ 2 * aSqCeiling :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      aSqCeilingNonnegative
  have secondLe : evalSqBoundStep interval.squareBound
      (evalSqBoundStep interval.squareBound 0 a) b ≤
        2 * ((2 * aSqCeiling) * radiusCeiling + bSqCeiling) :=
    evalSqBoundStep_le interval.squareBound_nonneg radiusLe firstLe bSqLe
      firstCeilingNonnegative
  have secondCeilingNonnegative :
      0 ≤ 2 * ((2 * aSqCeiling) * radiusCeiling + bSqCeiling) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          firstCeilingNonnegative radiusCeilingNonnegative)
        bSqCeilingNonnegative)
  exact evalSqBoundStep_le interval.squareBound_nonneg radiusLe secondLe
    cSqLe secondCeilingNonnegative

private theorem evalSqBoundCoeffs_monotone
    (coefficients : List Coordinate) {smallRadius largeRadius : Coordinate}
    {smallBound largeBound : Coordinate}
    (smallRadiusNonnegative : 0 ≤ smallRadius)
    (largeRadiusNonnegative : 0 ≤ largeRadius)
    (smallBoundNonnegative : 0 ≤ smallBound)
    (largeBoundNonnegative : 0 ≤ largeBound)
    (radiusLe : smallRadius ≤ largeRadius)
    (boundLe : smallBound ≤ largeBound) :
    coefficients.foldl (evalSqBoundStep smallRadius) smallBound ≤
      coefficients.foldl (evalSqBoundStep largeRadius) largeBound := by
  induction coefficients generalizing smallBound largeBound with
  | nil => exact boundLe
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      have productLe : smallBound * smallRadius ≤
          largeBound * largeRadius :=
        RFAP.ConstructiveFraction.mul_le_mul_direct boundLe radiusLe
          smallRadiusNonnegative largeBoundNonnegative
      have nextLe : evalSqBoundStep smallRadius smallBound coefficient ≤
          evalSqBoundStep largeRadius largeBound coefficient := by
        exact twice_le_twice (add_le_add productLe (le_refl _))
      apply inductionHypothesis
      · apply twice_nonneg
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            smallBoundNonnegative smallRadiusNonnegative)
          (RFAP.ConstructiveFraction.sq_nonneg_direct coefficient)
      · apply twice_nonneg
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct
            largeBoundNonnegative largeRadiusNonnegative)
          (RFAP.ConstructiveFraction.sq_nonneg_direct coefficient)
      · exact nextLe

theorem evalSqBound_le_of_refines (p : Polynomial) {interval root : Interval}
    (refines : interval.Refines root) :
    evalSqBound p interval ≤ evalSqBound p root := by
  unfold evalSqBound
  exact evalSqBoundCoeffs_monotone p.coeffs
    interval.squareBound_nonneg root.squareBound_nonneg
    (le_refl 0) (le_refl 0) (interval.squareBound_le_of_refines refines)
    (le_refl 0)

private theorem evalSqBoundCoeffs_spec (coefficients : List Coordinate)
    (interval : Interval) {x accumulator bound : Coordinate}
    (inside : interval.Contains x) (boundNonnegative : 0 ≤ bound)
    (accumulatorBound : accumulator ^ 2 ≤ bound) :
    let finalValue := coefficients.foldl
      (fun value coefficient => value * x + coefficient) accumulator
    let finalBound := coefficients.foldl
      (evalSqBoundStep interval.squareBound) bound
    0 ≤ finalBound ∧ finalValue ^ 2 ≤ finalBound := by
  induction coefficients generalizing accumulator bound with
  | nil => exact ⟨boundNonnegative, accumulatorBound⟩
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · apply twice_nonneg
        exact add_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct boundNonnegative
            interval.squareBound_nonneg)
          (RFAP.ConstructiveFraction.sq_nonneg_direct coefficient)
      · have productBound : (accumulator * x) ^ 2 ≤
            bound * interval.squareBound := by
          rw [mul_pow]
          exact RFAP.ConstructiveFraction.mul_le_mul_direct accumulatorBound
            (interval.sq_le_squareBound inside)
            (RFAP.ConstructiveFraction.sq_nonneg_direct x) boundNonnegative
        exact (add_sq_le_two (accumulator * x) coefficient).trans
          (twice_le_twice
            (add_le_add productBound (le_refl (coefficient ^ 2))))

theorem evalSqBound_nonneg (p : Polynomial) (interval : Interval) :
    0 ≤ evalSqBound p interval := by
  have specification := evalSqBoundCoeffs_spec p.coeffs interval
    (x := interval.lower) (accumulator := 0) (bound := 0)
    ⟨le_rfl, interval.valid⟩ (le_refl 0) (by
      change (0 : Coordinate) ≤ 0
      exact le_rfl)
  exact specification.1

theorem eval_sq_le_evalSqBound (p : Polynomial) (interval : Interval)
    {x : Coordinate} (inside : interval.Contains x) :
    p.eval x ^ 2 ≤ evalSqBound p interval := by
  have specification := evalSqBoundCoeffs_spec p.coeffs interval
    (x := x) (accumulator := 0) (bound := 0) inside (le_refl 0) (by
      change (0 : Coordinate) ≤ 0
      exact le_rfl)
  simpa only [eval, evalCoeffs, evalSqBound] using specification.2

/-- Explicit finite Bézout data.  Keeping the two cofactors in the certificate
lets determinant and Euclidean constructions share the same clearance path. -/
structure CoprimeCertificate (p q : Polynomial) where
  left : Polynomial
  right : Polynomial
  identity : ∀ x : Coordinate,
    1 = left.eval x * p.eval x + right.eval x * q.eval x

namespace CoprimeCertificate

def swap {p q : Polynomial}
    (certificate : CoprimeCertificate p q) : CoprimeCertificate q p where
  left := certificate.right
  right := certificate.left
  identity := by
    intro x
    rw [certificate.identity]
    ring1

/-- Bézout data transported through one signed Euclidean step. -/
def signedStep {p q : Polynomial}
    (certificate : CoprimeCertificate p q) :
    CoprimeCertificate q (-((divMod p q).remainder)) where
  left := certificate.left * (divMod p q).quotient + certificate.right
  right := -certificate.left
  identity := by
    intro x
    have step := RFAP.Sturm.signedStep_eval_identity p q x
    rw [certificate.identity, step]
    simp only [eval_add, eval_mul, eval_neg]
    ring1

theorem eval_ne_zero {p q : Polynomial}
    (certificate : CoprimeCertificate p q) (x : Coordinate) :
    p.eval x ≠ 0 ∨ q.eval x ≠ 0 := by
  by_cases hp : p.eval x = 0
  · right
    intro hq
    have contradiction := certificate.identity x
    rw [hp, hq, RFAP.ConstructiveFraction.mul_zero_direct,
      RFAP.ConstructiveFraction.mul_zero_direct,
      RFAP.ConstructiveFraction.zero_add] at contradiction
    exact RFAP.ConstructiveFraction.zero_ne_one contradiction.symm
  · exact Or.inl hp

theorem noCommonZero {p q : Polynomial}
    (certificate : CoprimeCertificate p q) :
    RFAP.Sturm.NoCommonZero p q :=
  certificate.eval_ne_zero

end CoprimeCertificate

/-- Positive uniform sum-of-squares clearance on a finite interval. -/
structure Certificate (p q : Polynomial) (interval : Interval) where
  bound : Coordinate
  positive : 0 < bound
  lower : ∀ x : Coordinate, interval.Contains x →
    bound ≤ p.eval x ^ 2 + q.eval x ^ 2

namespace Certificate

/-- A positive sum-of-squares lower bound makes the displayed coordinate
pair pointwise nonzero throughout the certified interval. -/
theorem eval_ne_zero {p q : Polynomial} {interval : Interval}
    (certificate : Certificate p q interval) {x : Coordinate}
    (inside : interval.Contains x) : p.eval x ≠ 0 ∨ q.eval x ≠ 0 := by
  by_cases pZero : p.eval x = 0
  · right
    intro qZero
    have lower := certificate.lower x inside
    rw [pZero, qZero] at lower
    have boundLeZero : certificate.bound ≤ 0 :=
      lower.trans_eq (by ring1)
    exact (not_lt_of_ge boundLeZero) certificate.positive
  · exact Or.inl pZero

def swap {p q : Polynomial} {interval : Interval}
    (certificate : Certificate p q interval) : Certificate q p interval where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro x inside
    calc
      certificate.bound ≤ p.eval x ^ 2 + q.eval x ^ 2 :=
        certificate.lower x inside
      _ = q.eval x ^ 2 + p.eval x ^ 2 :=
        RFAP.ConstructiveFraction.add_comm _ _

/-- Negating the second coordinate preserves a sum-of-squares clearance. -/
def negSecond {p q : Polynomial} {interval : Interval}
    (certificate : Certificate p q interval) :
    Certificate p (-q) interval where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro x inside
    simpa only [eval_neg, neg_sq] using certificate.lower x inside

/-- Reuse a uniform clearance certificate on a displayed subinterval. -/
def restrict {p q : Polynomial} {root interval : Interval}
    (certificate : Certificate p q root) (refines : interval.Refines root) :
    Certificate p q interval where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro x inside
    exact certificate.lower x
      ⟨refines.1.trans inside.1, inside.2.trans refines.2⟩

/-- Finite quotient majorant used when transporting clearance through one
signed Euclidean step. -/
def signedStepMajorant (p q : Polynomial) (interval : Interval) : Coordinate :=
  2 * (evalSqBound (divMod p q).quotient interval + 1)

theorem signedStepMajorant_pos (p q : Polynomial) (interval : Interval) :
    0 < signedStepMajorant p q interval := by
  have innerPositive : 0 < evalSqBound (divMod p q).quotient interval + 1 := by
    calc
      0 < 1 := by decide
      _ ≤ evalSqBound (divMod p q).quotient interval + 1 :=
        add_le_add (evalSqBound_nonneg _ _) (le_refl 1)
  exact RFAP.ConstructiveFraction.mul_pos_direct (by decide) innerPositive

/-- A pointwise sum-of-squares clearance transports constructively through
one signed Euclidean step.  No polynomial gcd or root enumeration is used. -/
def signedStep {p q : Polynomial} {interval : Interval}
    (certificate : Certificate p q interval) :
    Certificate q (-((divMod p q).remainder)) interval where
  bound := certificate.bound / signedStepMajorant p q interval
  positive := RFAP.ConstructiveFraction.div_pos_direct certificate.positive
    (signedStepMajorant_pos p q interval)
  lower := by
    intro x inside
    let next := -((divMod p q).remainder)
    let quotientBound := evalSqBound (divMod p q).quotient interval
    let qValue := q.eval x
    let nextValue := next.eval x
    have quotientBoundNonnegative : 0 ≤ quotientBound :=
      evalSqBound_nonneg _ _
    have quotientSqBound : (divMod p q).quotient.eval x ^ 2 ≤
        quotientBound := eval_sq_le_evalSqBound _ interval inside
    have productSqBound :
        (qValue * (divMod p q).quotient.eval x) ^ 2 ≤
          qValue ^ 2 * quotientBound := by
      rw [mul_pow]
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        quotientSqBound
        (RFAP.ConstructiveFraction.sq_nonneg_direct qValue)
    have pSqBound : p.eval x ^ 2 ≤
        2 * (qValue ^ 2 * quotientBound + nextValue ^ 2) := by
      have step := RFAP.Sturm.signedStep_eval_identity p q x
      change p.eval x =
        qValue * (divMod p q).quotient.eval x - nextValue at step
      rw [step]
      calc
        (qValue * (divMod p q).quotient.eval x - nextValue) ^ 2 =
            (qValue * (divMod p q).quotient.eval x + -nextValue) ^ 2 := by
          ring1
        _ ≤ 2 * ((qValue * (divMod p q).quotient.eval x) ^ 2 +
              (-nextValue) ^ 2) := add_sq_le_two _ _
        _ ≤ 2 * (qValue ^ 2 * quotientBound + nextValue ^ 2) :=
          twice_le_twice (by
            simpa only [neg_sq] using
              add_le_add productSqBound (le_refl (nextValue ^ 2)))
    have sumBound : p.eval x ^ 2 + qValue ^ 2 ≤
        (qValue ^ 2 + nextValue ^ 2) *
          signedStepMajorant p q interval := by
      calc
        p.eval x ^ 2 + qValue ^ 2 ≤
            2 * (qValue ^ 2 * quotientBound + nextValue ^ 2) +
              qValue ^ 2 := add_le_add pSqBound (le_refl _)
        _ ≤ (qValue ^ 2 + nextValue ^ 2) *
              signedStepMajorant p q interval := by
          apply sub_nonneg.mp
          calc
            0 ≤ qValue ^ 2 + 2 * quotientBound * nextValue ^ 2 :=
              add_nonneg (RFAP.ConstructiveFraction.sq_nonneg_direct qValue)
                (RFAP.ConstructiveFraction.mul_nonneg_direct
                  (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
                    quotientBoundNonnegative)
                  (RFAP.ConstructiveFraction.sq_nonneg_direct nextValue))
            _ = (qValue ^ 2 + nextValue ^ 2) *
                  signedStepMajorant p q interval -
                (2 * (qValue ^ 2 * quotientBound + nextValue ^ 2) +
                  qValue ^ 2) := by
              dsimp only [signedStepMajorant]
              ring1
    apply (RFAP.ConstructiveFraction.div_le_iff_pos
      (signedStepMajorant_pos p q interval)).2
    exact (certificate.lower x inside).trans sumBound

/-- Multiply two complex-coordinate clearances using the exact finite
sum-of-two-squares identity. -/
def complexProduct
    {A B C D E H : Polynomial} {interval : Interval}
    (left : Certificate A B interval)
    (right : Certificate C D interval)
    (realIdentity : ∀ x : Coordinate,
      E.eval x = A.eval x * C.eval x - B.eval x * D.eval x)
    (imagIdentity : ∀ x : Coordinate,
      H.eval x = A.eval x * D.eval x + B.eval x * C.eval x) :
    Certificate E H interval where
  bound := left.bound * right.bound
  positive := RFAP.ConstructiveFraction.mul_pos_direct
    left.positive right.positive
  lower := by
    intro x inside
    have leftLower := left.lower x inside
    have rightLower := right.lower x inside
    have productLower : left.bound * right.bound ≤
        (A.eval x ^ 2 + B.eval x ^ 2) *
          (C.eval x ^ 2 + D.eval x ^ 2) :=
      RFAP.ConstructiveFraction.mul_le_mul_direct leftLower rightLower
        right.positive.le
        (add_nonneg (RFAP.ConstructiveFraction.sq_nonneg_direct _)
          (RFAP.ConstructiveFraction.sq_nonneg_direct _))
    calc
      left.bound * right.bound ≤
          (A.eval x ^ 2 + B.eval x ^ 2) *
            (C.eval x ^ 2 + D.eval x ^ 2) := productLower
      _ = E.eval x ^ 2 + H.eval x ^ 2 := by
        rw [realIdentity x, imagIdentity x]
        ring1

end Certificate

/-- Finite upper bound for the squared Bézout coefficients on an interval. -/
def bezoutSqMajorant {p q : Polynomial}
    (certificate : CoprimeCertificate p q) (interval : Interval) : Coordinate :=
  max 1 (evalSqBound certificate.left interval +
    evalSqBound certificate.right interval)

theorem bezoutSqMajorant_le_of_refines {p q : Polynomial}
    (certificate : CoprimeCertificate p q) {interval root : Interval}
    (refines : interval.Refines root) :
    bezoutSqMajorant certificate interval ≤
      bezoutSqMajorant certificate root := by
  apply max_le
  · exact le_max_left _ _
  · exact (add_le_add
      (evalSqBound_le_of_refines certificate.left refines)
      (evalSqBound_le_of_refines certificate.right refines)).trans
      (le_max_right _ _)

theorem bezoutSqMajorant_pos {p q : Polynomial}
    (certificate : CoprimeCertificate p q) (interval : Interval) :
    0 < bezoutSqMajorant certificate interval :=
  (show (0 : Coordinate) < 1 by decide).trans_le (le_max_left _ _)

theorem bezout_eval_sq_add_le_majorant {p q : Polynomial}
    (certificate : CoprimeCertificate p q) (interval : Interval)
    {x : Coordinate} (inside : interval.Contains x) :
    certificate.left.eval x ^ 2 + certificate.right.eval x ^ 2 ≤
      bezoutSqMajorant certificate interval := by
  exact (add_le_add
    (eval_sq_le_evalSqBound certificate.left interval inside)
    (eval_sq_le_evalSqBound certificate.right interval inside)).trans
    (le_max_right _ _)

private theorem sum_product_sq_le_product_sums
    (a b p q : Coordinate) :
    (a * p + b * q) ^ 2 ≤ (a ^ 2 + b ^ 2) * (p ^ 2 + q ^ 2) := by
  apply sub_nonneg.mp
  calc
    0 ≤ (a * q - b * p) ^ 2 :=
      RFAP.ConstructiveFraction.sq_nonneg_direct _
    _ = (a ^ 2 + b ^ 2) * (p ^ 2 + q ^ 2) -
        (a * p + b * q) ^ 2 := by ring1

/-- A finite Bézout certificate yields quantitative path clearance. -/
def certificateOfCoprime {p q : Polynomial}
    (coprime : CoprimeCertificate p q) (interval : Interval) :
    Certificate p q interval where
  bound := 1 / bezoutSqMajorant coprime interval
  positive := by
    exact RFAP.ConstructiveFraction.div_pos_direct (by decide)
      (bezoutSqMajorant_pos coprime interval)
  lower := by
    intro x inside
    let coefficientSq :=
      coprime.left.eval x ^ 2 + coprime.right.eval x ^ 2
    let valueSq := p.eval x ^ 2 + q.eval x ^ 2
    have coefficientNonnegative : 0 ≤ coefficientSq :=
      add_nonneg
        (RFAP.ConstructiveFraction.sq_nonneg_direct _)
        (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    have valueNonnegative : 0 ≤ valueSq :=
      add_nonneg
        (RFAP.ConstructiveFraction.sq_nonneg_direct _)
        (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    have coefficientBound : coefficientSq ≤
        bezoutSqMajorant coprime interval :=
      bezout_eval_sq_add_le_majorant coprime interval inside
    have identity := coprime.identity x
    have cauchy : 1 ≤ coefficientSq * valueSq := by
      calc
        1 = (coprime.left.eval x * p.eval x +
            coprime.right.eval x * q.eval x) ^ 2 := by rw [← identity]; ring1
        _ ≤ coefficientSq * valueSq := by
          exact sum_product_sq_le_product_sums _ _ _ _
    have scaled : 1 ≤ bezoutSqMajorant coprime interval * valueSq :=
      cauchy.trans
        (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          coefficientBound valueNonnegative)
    apply (RFAP.ConstructiveFraction.div_le_iff_pos
      (bezoutSqMajorant_pos coprime interval)).mpr
    dsimp only [valueSq] at scaled ⊢
    rw [RFAP.ConstructiveFraction.mul_comm]
    exact scaled

theorem certificateOfCoprime_bound_le_of_refines {p q : Polynomial}
    (coprime : CoprimeCertificate p q) {interval root : Interval}
    (refines : interval.Refines root) :
    (certificateOfCoprime coprime root).bound ≤
      (certificateOfCoprime coprime interval).bound := by
  have rootPositive := bezoutSqMajorant_pos coprime root
  have intervalPositive := bezoutSqMajorant_pos coprime interval
  have majorantLe := bezoutSqMajorant_le_of_refines coprime refines
  apply (RFAP.ConstructiveFraction.le_div_iff_pos intervalPositive).2
  dsimp only [certificateOfCoprime]
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
    RFAP.ConstructiveFraction.one_mul, RFAP.ConstructiveFraction.mul_comm]
  change bezoutSqMajorant coprime interval /
      bezoutSqMajorant coprime root ≤ 1
  exact (RFAP.ConstructiveFraction.div_le_iff_pos rootPositive).2 (by
    rw [RFAP.ConstructiveFraction.one_mul]
    exact majorantLe)

end RFAP.PathClearance
