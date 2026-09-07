import FTA.GaussianDerivative
import FTA.LocalExtraction

/-!
# Executable Gaussian-rational squarefree certificates

This module runs extended Euclid directly on finite dense coefficient lists
over `ℚ(i)`.  The sparse polynomial library is used only to verify the returned
finite Bézout data.  In particular, no proposition-valued witness is extracted
into computational data.
-/

namespace FTA.GaussianDenseSquarefree

open Polynomial
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.GaussianDerivative
open FTA.LocalExtraction

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI

/-- Sparse specification of one executable leading-term cancellation. -/
theorem toPolynomial_cancelLead (p q : GaussianPolynomial) :
    (cancelLead p q).toPolynomial = p.toPolynomial -
      (C (p.leadingCoeff / q.leadingCoeff) * q.toPolynomial) *
        X ^ (p.natDegree - q.natDegree) := by
  exact DensePolynomial.toPolynomial_cancelLead p q

/-- One nonterminal dense cancellation strictly lowers sparse degree. -/
theorem degree_toPolynomial_cancelLead_lt {p q : GaussianPolynomial}
    (hp : p.isZero = false) (hq : q.isZero = false)
    (hdegree : q.natDegree ≤ p.natDegree) :
    (cancelLead p q).toPolynomial.degree < p.toPolynomial.degree := by
  let c := p.leadingCoeff / q.leadingCoeff
  let e := p.natDegree - q.natDegree
  let term := (C c * q.toPolynomial) * X ^ e
  have hpPolynomial : p.toPolynomial ≠ 0 :=
    toPolynomial_ne_zero_of_isZero_false hp
  have hqPolynomial : q.toPolynomial ≠ 0 :=
    toPolynomial_ne_zero_of_isZero_false hq
  have hc : c ≠ 0 :=
    div_ne_zero (leadingCoeff_ne_zero hp) (leadingCoeff_ne_zero hq)
  have hbase : C c * q.toPolynomial ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hqPolynomial
  have hterm : term ≠ 0 :=
    mul_ne_zero hbase (pow_ne_zero _ Polynomial.X_ne_zero)
  have htermDegree : term.natDegree = p.natDegree := by
    dsimp only [term, e]
    rw [Polynomial.natDegree_mul_X_pow _ hbase,
      Polynomial.natDegree_C_mul hc, natDegree_toPolynomial hq]
    omega
  have hdegreeEqual : p.toPolynomial.degree = term.degree := by
    rw [Polynomial.degree_eq_natDegree hpPolynomial,
      Polynomial.degree_eq_natDegree hterm,
      natDegree_toPolynomial hp, htermDegree]
  have hleadingEqual :
      p.toPolynomial.leadingCoeff = term.leadingCoeff := by
    dsimp only [term, c]
    rw [Polynomial.leadingCoeff_mul_X_pow, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_C, leadingCoeff_toPolynomial hq,
      leadingCoeff_toPolynomial hp]
    field_simp [leadingCoeff_ne_zero hq]
  rw [toPolynomial_cancelLead]
  exact Polynomial.degree_sub_lt hdegreeEqual hpPolynomial hleadingEqual

/-- Every continuing long-division step lowers the normalized coefficient
count, independently of any order on the coefficient field. -/
theorem degreeCount_cancelLead_lt {p q : GaussianPolynomial}
    (hp : p.isZero = false) (hq : q.isZero = false)
    (hdegree : q.natDegree ≤ p.natDegree) :
    (cancelLead p q).degreeCount < p.degreeCount := by
  by_cases nextZero : (cancelLead p q).isZero = true
  · rw [degreeCount_eq_zero_of_isZero nextZero]
    exact degreeCount_pos_of_isZero_false hp
  · have nextNonzero : (cancelLead p q).isZero = false := by
      simpa using nextZero
    have degreeDrop := degree_toPolynomial_cancelLead_lt hp hq hdegree
    have hpPolynomial : p.toPolynomial ≠ 0 :=
      toPolynomial_ne_zero_of_isZero_false hp
    have nextPolynomial : (cancelLead p q).toPolynomial ≠ 0 :=
      toPolynomial_ne_zero_of_isZero_false nextNonzero
    rw [Polynomial.degree_eq_natDegree nextPolynomial,
      Polynomial.degree_eq_natDegree hpPolynomial,
      natDegree_toPolynomial nextNonzero,
      natDegree_toPolynomial hp] at degreeDrop
    have degreeDropNat :
        (cancelLead p q).natDegree < p.natDegree := by
      exact_mod_cast degreeDrop
    have nextCount := natDegree_add_one_eq_degreeCount nextNonzero
    have currentCount := natDegree_add_one_eq_degreeCount hp
    omega

/-- Sufficient finite fuel carries strict degree descent through dense long
division over `ℚ(i)`. -/
theorem divLoop_remainder_small
    (fuel : ℕ) (p q quotient : GaussianPolynomial)
    (hq : q.isZero = false) (fuelEnough : p.degreeCount < fuel) :
    (divLoop fuel p q quotient).remainder.isZero = true ∨
      (divLoop fuel p q quotient).remainder.natDegree < q.natDegree := by
  induction fuel generalizing p quotient with
  | zero => omega
  | succ fuel inductionHypothesis =>
      rw [divLoop]
      split
      · rename_i stopped
        dsimp only
        simp [hq] at stopped
        rcases stopped with pZero | degreeSmall
        · exact Or.inl pZero
        · exact Or.inr degreeSmall
      · rename_i continuing
        dsimp only
        have conditions :
            p.isZero = false ∧ q.natDegree ≤ p.natDegree := by
          simpa [hq] using continuing
        apply inductionHypothesis
          (p := cancelLead p q)
          (quotient := quotient + leadQuotient p q)
        have drop := degreeCount_cancelLead_lt conditions.1 hq conditions.2
        omega

theorem divMod_remainder_degreeCount_lt
    (p q : GaussianPolynomial) (hq : q.isZero = false) :
    (divMod p q).remainder.degreeCount < q.degreeCount := by
  have small := divLoop_remainder_small
    (p.degreeCount + 1) p.normalize q.normalize 0
    (by simpa using hq) (by simp)
  have remainderSmall :
      (divMod p q).remainder.isZero = true ∨
        (divMod p q).remainder.natDegree < q.natDegree := by
    simpa [divMod] using small
  rcases remainderSmall with remainderZero | degreeSmall
  · rw [degreeCount_eq_zero_of_isZero remainderZero]
    exact degreeCount_pos_of_isZero_false hq
  · by_cases remainderZero : (divMod p q).remainder.isZero = true
    · rw [degreeCount_eq_zero_of_isZero remainderZero]
      exact degreeCount_pos_of_isZero_false hq
    · have remainderNonzero :
          (divMod p q).remainder.isZero = false := by
        simpa using remainderZero
      have remainderCount :=
        natDegree_add_one_eq_degreeCount remainderNonzero
      have divisorCount := natDegree_add_one_eq_degreeCount hq
      omega

/-- Output of executable extended Euclid over Gaussian-rational coefficient
lists, including the factors needed to verify common divisibility. -/
structure BezoutResult (p q : GaussianPolynomial) where
  gcd : GaussianPolynomial
  left : GaussianPolynomial
  right : GaussianPolynomial
  identity : gcd.toPolynomial =
    left.toPolynomial * p.toPolynomial + right.toPolynomial * q.toPolynomial
  pFactor : GaussianPolynomial
  qFactor : GaussianPolynomial
  pIdentity : p.toPolynomial = gcd.toPolynomial * pFactor.toPolynomial
  qIdentity : q.toPolynomial = gcd.toPolynomial * qFactor.toPolynomial
  nonzero : p.isZero = false ∨ q.isZero = false → gcd.isZero = false

/-- Finite extended Euclid; termination is the proved remainder coefficient
count descent above. -/
def extendedGCD (p q : GaussianPolynomial) : BezoutResult p q :=
  if qZero : q.isZero then
    { gcd := p.normalize
      left := constant 1
      right := 0
      identity := by
        rw [toPolynomial_normalize, toPolynomial_constant,
          toPolynomial_zero]
        simp
      pFactor := constant 1
      qFactor := 0
      pIdentity := by
        rw [toPolynomial_normalize, toPolynomial_constant]
        simp
      qIdentity := by
        have qZeroTrue : q.isZero = true := by simpa using qZero
        rw [(toPolynomial_eq_zero_iff_isZero q).2 qZeroTrue,
          toPolynomial_zero, mul_zero]
      nonzero := by
        intro someNonzero
        have pNonzero : p.isZero = false := by
          rcases someNonzero with pNonzero | qNonzero
          · exact pNonzero
          · have qZeroTrue : q.isZero = true := by simpa using qZero
            simp [qZeroTrue] at qNonzero
        simpa using pNonzero }
  else
    let division := divMod p q
    let recursive := extendedGCD q division.remainder
    { gcd := recursive.gcd
      left := recursive.right
      right := recursive.left - recursive.right * division.quotient
      identity := by
        rw [toPolynomial_sub, toPolynomial_mul]
        calc
          recursive.gcd.toPolynomial =
              recursive.left.toPolynomial * q.toPolynomial +
                recursive.right.toPolynomial * division.remainder.toPolynomial :=
            recursive.identity
          _ = recursive.right.toPolynomial * p.toPolynomial +
              (recursive.left.toPolynomial -
                recursive.right.toPolynomial * division.quotient.toPolynomial) *
                  q.toPolynomial := by
            have divisionIdentity := divMod_toPolynomial_equation p q
            rw [divisionIdentity]
            ring
      pFactor := recursive.qFactor +
        recursive.pFactor * division.quotient
      qFactor := recursive.pFactor
      pIdentity := by
        rw [toPolynomial_add, toPolynomial_mul]
        calc
          p.toPolynomial = q.toPolynomial * division.quotient.toPolynomial +
              division.remainder.toPolynomial :=
            divMod_toPolynomial_equation p q
          _ = recursive.gcd.toPolynomial *
              (recursive.qFactor.toPolynomial +
                recursive.pFactor.toPolynomial * division.quotient.toPolynomial) := by
            rw [recursive.pIdentity, recursive.qIdentity]
            ring
      qIdentity := recursive.pIdentity
      nonzero := by
        intro _
        apply recursive.nonzero
        left
        simpa using qZero }
termination_by q.degreeCount
decreasing_by
  have qNonzero : q.isZero = false := by simpa using qZero
  exact divMod_remainder_degreeCount_lt p q qNonzero

/-- Finite dense Bézout data displaying coprimality over `ℚ(i)`. -/
structure CoprimeCertificate (p q : GaussianPolynomial) where
  left : GaussianPolynomial
  right : GaussianPolynomial
  identity : left.toPolynomial * p.toPolynomial +
    right.toPolynomial * q.toPolynomial = 1

theorem toPolynomial_eq_C_leadingCoeff_of_natDegree_eq_zero
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (degreeZero : p.natDegree = 0) :
    p.toPolynomial = C p.leadingCoeff := by
  have sparseDegree : p.toPolynomial.natDegree = 0 := by
    rw [natDegree_toPolynomial nonzero]
    exact degreeZero
  have hconstant := Polynomial.eq_C_of_natDegree_eq_zero sparseDegree
  have hcoefficient : p.toPolynomial.coeff 0 = p.leadingCoeff := by
    calc
      p.toPolynomial.coeff 0 = p.toPolynomial.leadingCoeff := by
        rw [Polynomial.leadingCoeff, sparseDegree]
      _ = p.leadingCoeff := leadingCoeff_toPolynomial nonzero
  exact hconstant.trans (congrArg C hcoefficient)

/-- A nonzero represented constant evaluates to its normalized leading
coefficient at every Gaussian-rational point. -/
theorem eval_eq_leadingCoeff_of_natDegree_eq_zero
    {p : GaussianPolynomial} (nonzero : p.isZero = false)
    (degreeZero : p.natDegree = 0) (x : QI) :
    p.eval x = p.leadingCoeff := by
  have sparseDegree : p.toPolynomial.natDegree = 0 := by
    rw [natDegree_toPolynomial nonzero]
    exact degreeZero
  let coefficient := p.toPolynomial.coeff 0
  have constantPolynomial : p.toPolynomial = C coefficient :=
    Polynomial.eq_C_of_natDegree_eq_zero sparseDegree
  calc
    p.eval x = Polynomial.eval x p.toPolynomial :=
      (eval_toPolynomial p x).symm
    _ = Polynomial.eval x (C coefficient) :=
      congrArg (Polynomial.eval x) constantPolynomial
    _ = coefficient := by simp
    _ = p.toPolynomial.coeff 0 := rfl
    _ = p.toPolynomial.leadingCoeff := by
      rw [Polynomial.leadingCoeff, sparseDegree]
    _ = p.leadingCoeff := leadingCoeff_toPolynomial nonzero

/-- Normalize a nonzero constant Euclidean result to a Bézout identity for
one. -/
def certificateOfConstantGCD
    {p q : GaussianPolynomial} (result : BezoutResult p q)
    (gcdNonzero : result.gcd.isZero = false)
    (degreeZero : result.gcd.natDegree = 0) :
    CoprimeCertificate p q where
  left := scale result.gcd.leadingCoeff⁻¹ result.left
  right := scale result.gcd.leadingCoeff⁻¹ result.right
  identity := by
    rw [toPolynomial_scale, toPolynomial_scale]
    have constantGCD :=
      toPolynomial_eq_C_leadingCoeff_of_natDegree_eq_zero gcdNonzero degreeZero
    have leadingNonzero := leadingCoeff_ne_zero gcdNonzero
    calc
      C result.gcd.leadingCoeff⁻¹ * result.left.toPolynomial * p.toPolynomial +
          C result.gcd.leadingCoeff⁻¹ * result.right.toPolynomial * q.toPolynomial =
          C result.gcd.leadingCoeff⁻¹ * result.gcd.toPolynomial := by
        rw [result.identity]
        ring
      _ = C result.gcd.leadingCoeff⁻¹ * C result.gcd.leadingCoeff := by
        rw [constantGCD]
      _ = 1 := by
        rw [← map_mul, inv_mul_cancel₀ leadingNonzero, map_one]

theorem BezoutResult.gcd_toPolynomial_dvd_left
    {p q : GaussianPolynomial} (result : BezoutResult p q) :
    result.gcd.toPolynomial ∣ p.toPolynomial := by
  refine ⟨result.pFactor.toPolynomial, ?_⟩
  exact result.pIdentity

theorem BezoutResult.gcd_toPolynomial_dvd_right
    {p q : GaussianPolynomial} (result : BezoutResult p q) :
    result.gcd.toPolynomial ∣ q.toPolynomial := by
  refine ⟨result.qFactor.toPolynomial, ?_⟩
  exact result.qIdentity

/-- Recover executable dense Bézout coefficients from an already verified
sparse coprimality proposition by inspecting the finite Euclidean output.
The proposition is used only to eliminate the checked nonconstant-gcd case. -/
def certificateOfIsCoprime
    (p q : GaussianPolynomial)
    (someNonzero : p.isZero = false ∨ q.isZero = false)
    (coprime : IsCoprime p.toPolynomial q.toPolynomial) :
    CoprimeCertificate p q := by
  let result := extendedGCD p q
  have gcdNonzero : result.gcd.isZero = false :=
    result.nonzero someNonzero
  if degreeZero : result.gcd.natDegree = 0 then
    exact certificateOfConstantGCD result gcdNonzero degreeZero
  else
    have gcdUnit : IsUnit result.gcd.toPolynomial :=
      coprime.isUnit_of_dvd' result.gcd_toPolynomial_dvd_left
        result.gcd_toPolynomial_dvd_right
    have sparseDegreeZero : result.gcd.toPolynomial.natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit gcdUnit
    have denseDegreeZero : result.gcd.natDegree = 0 := by
      rw [← natDegree_toPolynomial gcdNonzero]
      exact sparseDegreeZero
    exact (degreeZero denseDegreeZero).elim

/-- Extended Euclid computes the paper's dense Gaussian squarefree
certificate for every primitive positive-degree input. -/
def primitiveSquarefreeCertificate
    {p : GaussianPolynomial} (primitive : FTA.Primitive p.toPolynomial)
    (degreePositive : 0 < p.natDegree) :
    GaussianSquarefreeCertificate p := by
  have nonzero : p.isZero = false :=
    FTA.GlobalWinding.isZero_false_of_natDegree_pos degreePositive
  let result := extendedGCD p (derivative p)
  have gcdNonzero : result.gcd.isZero = false :=
    result.nonzero (Or.inl nonzero)
  have degreeZero : result.gcd.natDegree = 0 := by
    rcases primitive.2.isUnit_or_isUnit result.pIdentity with gcdUnit | factorUnit
    · have sparseDegreeZero : result.gcd.toPolynomial.natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_isUnit gcdUnit
      rwa [natDegree_toPolynomial gcdNonzero] at sparseDegreeZero
    · have sparseDegreePositive : 0 < p.toPolynomial.natDegree := by
        rw [natDegree_toPolynomial nonzero]
        exact degreePositive
      have derivativeNonzero : p.toPolynomial.derivative ≠ 0 :=
        Polynomial.derivative_ne_zero.mpr (Nat.ne_of_gt sparseDegreePositive)
      have pNotDividesDerivative : ¬p.toPolynomial ∣ p.toPolynomial.derivative :=
        Polynomial.not_dvd_of_degree_lt derivativeNonzero
          (Polynomial.degree_derivative_lt primitive.2.ne_zero)
      have pAssociatedGCD : Associated p.toPolynomial result.gcd.toPolynomial := by
        rw [result.pIdentity]
        exact associated_mul_unit_left result.gcd.toPolynomial
          result.pFactor.toPolynomial factorUnit
      have pDividesDerivative : p.toPolynomial ∣ p.toPolynomial.derivative := by
        rw [← toPolynomial_derivative]
        exact pAssociatedGCD.dvd.trans result.gcd_toPolynomial_dvd_right
      exact (pNotDividesDerivative pDividesDerivative).elim
  let certificate := certificateOfConstantGCD result gcdNonzero degreeZero
  exact
    { left := certificate.left
      right := certificate.right
      identity := certificate.identity }

/-! ## Native computation regression -/

private def quadraticExample : GaussianPolynomial :=
  ⟨[(1 : QI), 0, -2]⟩

/-- The Gaussian extended-Euclidean program actually evaluates on finite
coefficient lists; this check is not merely a specification-level existence
proof. -/
theorem extendedGCD_quadratic_derivative_degree_zero :
    (extendedGCD quadraticExample
      (derivative quadraticExample)).gcd.natDegree = 0 := by
  native_decide

end FTA.GaussianDenseSquarefree
