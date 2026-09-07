import FTA.SturmTransducer

/-!
# Finite squarefree-factor descent

Every nonzero nonconstant dense rational polynomial is split into its computed
squarefree part and the strictly lower-degree complementary gcd factor.  The
descent terminates by the proved degree drop and returns only proof-bearing
squarefree Sturm inputs, together with one nonzero rational scalar and an
exact evaluation identity for their product.
-/

namespace FTA.SquarefreeFactorization

open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.DenseSquarefree
open FTA.Sturm
open FTA.SturmTransducer

abbrev RatPolynomial := DensePolynomial ℚ

/-- One nonconstant squarefree factor and all finite data needed by the Sturm
program. -/
structure Factor where
  polynomial : RatPolynomial
  input : SquarefreeInput polynomial

/-- Dense product of a certified factor list. -/
def factorProduct : List Factor → RatPolynomial
  | [] => constant 1
  | factor :: factors => factor.polynomial * factorProduct factors

@[simp] theorem factorProduct_nil : factorProduct [] = constant 1 := rfl

@[simp] theorem factorProduct_cons (factor : Factor) (factors : List Factor) :
    factorProduct (factor :: factors) = factor.polynomial * factorProduct factors :=
  rfl

@[simp] theorem factorProduct_eval (factors : List Factor) (x : ℚ) :
    (factorProduct factors).eval x =
      (factors.map fun factor => factor.polynomial.eval x).prod := by
  induction factors with
  | nil => simp [factorProduct]
  | cons factor factors ih => simp [factorProduct, ih]

/-- A finite squarefree decomposition retains the terminal nonzero constant
as a scalar rather than pretending it is a nonconstant Sturm input. -/
structure Decomposition (p : RatPolynomial) where
  scalar : ℚ
  scalar_ne_zero : scalar ≠ 0
  factors : List Factor
  factors_nonempty : factors ≠ []
  eval_identity : ∀ x, p.eval x = scalar * (factorProduct factors).eval x

/-- The current squarefree quotient packaged for the transducer layer. -/
def currentFactor (p : RatPolynomial) (hp : p.isZero = false)
    (hdegree : p.natDegree ≠ 0) : Factor where
  polynomial := squarefreePart p
  input := squarefreePartInput p hp hdegree

/-- Degree-recursive finite squarefree decomposition.  Each recursive call is
on the complementary gcd factor, whose degree is strictly smaller. -/
def decompose (p : RatPolynomial) (hp : p.isZero = false)
    (hdegree : p.natDegree ≠ 0) : Decomposition p := by
  let factor := currentFactor p hp hdegree
  let repeated := repeatedPart p
  have hrepeated : repeated.isZero = false := repeatedPart_isZero_false hp
  if hconstant : repeated.natDegree = 0 then
    exact
      { scalar := repeated.leadingCoeff
        scalar_ne_zero := leadingCoeff_ne_zero hrepeated
        factors := [factor]
        factors_nonempty := by simp
        eval_identity := by
          intro x
          rw [repeatedPart_mul_squarefreePart_eval]
          have hrepeatedEval :=
            FTA.DenseSquarefree.eval_eq_leadingCoeff_of_natDegree_eq_zero
              hrepeated hconstant x
          simp only [factorProduct, eval_mul, eval_constant, mul_one, factor,
            currentFactor]
          rw [hrepeatedEval] }
  else
    let tail := decompose repeated hrepeated hconstant
    exact
      { scalar := tail.scalar
        scalar_ne_zero := tail.scalar_ne_zero
        factors := factor :: tail.factors
        factors_nonempty := by simp
        eval_identity := by
          intro x
          rw [repeatedPart_mul_squarefreePart_eval, tail.eval_identity]
          simp only [factorProduct, eval_mul, factor, currentFactor]
          ring }
termination_by p.natDegree
decreasing_by
  exact repeatedPart_natDegree_lt hp hdegree

theorem factorProduct_eval_ne_zero_of_decomposition_eval_ne_zero
    {p : RatPolynomial} (decomposition : Decomposition p) {x : ℚ}
    (hp : p.eval x ≠ 0) : (factorProduct decomposition.factors).eval x ≠ 0 := by
  intro hproduct
  apply hp
  rw [decomposition.eval_identity, hproduct, mul_zero]

theorem Factor.eval_ne_zero_of_mem_of_factorProduct_eval_ne_zero
    {factors : List Factor} {factor : Factor} {x : ℚ}
    (hmem : factor ∈ factors) (hproduct : (factorProduct factors).eval x ≠ 0) :
    factor.polynomial.eval x ≠ 0 := by
  induction factors with
  | nil => simp at hmem
  | cons head tail ih =>
      have hhead : head.polynomial.eval x ≠ 0 := by
        intro hzero
        apply hproduct
        simp [factorProduct, hzero]
      have htail : (factorProduct tail).eval x ≠ 0 := by
        intro hzero
        apply hproduct
        simp [factorProduct, hzero]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hhead
      · exact ih hmem htail

/-- A zero of the finite factor product is a zero of at least one displayed
squarefree factor. -/
theorem exists_factor_eval_eq_zero_of_factorProduct_eval_eq_zero
    {factors : List Factor} {x : ℚ}
    (productZero : (factorProduct factors).eval x = 0) :
    ∃ factor ∈ factors, factor.polynomial.eval x = 0 := by
  induction factors with
  | nil => simp [factorProduct, eval_constant] at productZero
  | cons head tail inductionHypothesis =>
      rw [factorProduct_cons, eval_mul] at productZero
      rcases mul_eq_zero.mp productZero with headZero | tailZero
      · exact ⟨head, by simp, headZero⟩
      · rcases inductionHypothesis tailZero with ⟨factor, member, factorZero⟩
        exact ⟨factor, by simp [member], factorZero⟩

/-- The evaluation identity of a squarefree decomposition therefore exposes a
displayed factor at every exact zero of the original polynomial. -/
theorem Decomposition.exists_factor_eval_eq_zero
    {p : RatPolynomial} (decomposition : Decomposition p) {x : ℚ}
    (polynomialZero : p.eval x = 0) :
    ∃ factor ∈ decomposition.factors, factor.polynomial.eval x = 0 := by
  have productZero : (factorProduct decomposition.factors).eval x = 0 := by
    rw [decomposition.eval_identity] at polynomialZero
    exact (mul_eq_zero.mp polynomialZero).resolve_left decomposition.scalar_ne_zero
  exact exists_factor_eval_eq_zero_of_factorProduct_eval_eq_zero productZero

/-- Multiplicity-sensitive doubled root count obtained by summing the finite
Sturm count of every squarefree factor in the degree descent.  Its zero case
is exactly the form needed by the arbitrary-factor lower-bound program. -/
def Decomposition.rootCount2 {p : RatPolynomial} (decomposition : Decomposition p)
    (a b : ℚ) : ℤ :=
  (decomposition.factors.map fun factor =>
    sturmRootCount2 factor.polynomial a b).sum

def factorRootCount2 (p : RatPolynomial) (hp : p.isZero = false)
    (a b : ℚ) : ℤ :=
  if hdegree : p.natDegree = 0 then 0
  else (decompose p hp hdegree).rootCount2 a b

theorem Decomposition.factor_count_nonnegative {p : RatPolynomial}
    (decomposition : Decomposition p) {a b : ℚ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0)
    {factor : Factor} (hmem : factor ∈ decomposition.factors) :
    0 ≤ sturmRootCount2 factor.polynomial a b := by
  have hproductA :=
    factorProduct_eval_ne_zero_of_decomposition_eval_ne_zero decomposition ha
  have hproductB :=
    factorProduct_eval_ne_zero_of_decomposition_eval_ne_zero decomposition hb
  have hfactorA :=
    factor.eval_ne_zero_of_mem_of_factorProduct_eval_ne_zero hmem hproductA
  have hfactorB :=
    factor.eval_ne_zero_of_mem_of_factorProduct_eval_ne_zero hmem hproductB
  exact (computedEventPartitionProgram factor.input).nonnegativeLaw
    hab hfactorA hfactorB

theorem Decomposition.rootCount2_nonnegative {p : RatPolynomial}
    (decomposition : Decomposition p) {a b : ℚ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    0 ≤ decomposition.rootCount2 a b := by
  apply List.sum_nonneg
  intro count hcount
  rcases List.mem_map.mp hcount with ⟨factor, hmem, rfl⟩
  exact decomposition.factor_count_nonnegative hab ha hb hmem

theorem factorRootCount2_nonnegative {p : RatPolynomial}
    (hp : p.isZero = false) {a b : ℚ} (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    0 ≤ factorRootCount2 p hp a b := by
  rw [factorRootCount2]
  split
  · exact le_rfl
  · exact (decompose p hp _).rootCount2_nonnegative hab ha hb

/-- A zero sum of nonnegative factor counts makes every displayed
squarefree-factor count zero. -/
theorem Decomposition.factor_count_eq_zero_of_rootCount2_eq_zero
    {p : RatPolynomial} (decomposition : Decomposition p) {a b : ℚ}
    (hab : a < b) (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0)
    (hzero : decomposition.rootCount2 a b = 0) {factor : Factor}
    (hmem : factor ∈ decomposition.factors) :
    sturmRootCount2 factor.polynomial a b = 0 := by
  have hnonnegative := decomposition.factor_count_nonnegative hab ha hb hmem
  have hle : sturmRootCount2 factor.polynomial a b ≤
      decomposition.rootCount2 a b := by
    apply List.single_le_sum
    · intro count hcount
      rcases List.mem_map.mp hcount with ⟨other, hother, rfl⟩
      exact decomposition.factor_count_nonnegative hab ha hb hother
    · exact List.mem_map.mpr ⟨factor, hmem, rfl⟩
  omega

private def repeatedPolynomial : RatPolynomial := ⟨[1, -3, 3, -1]⟩

/-- The cubic `(T-1)^3` follows a genuinely repeated-factor descent and all
returned factors pass the executable squarefreeness checker. -/
theorem decompose_repeated_cubic_factors_squarefree :
    (decompose repeatedPolynomial (by native_decide) (by native_decide)).factors.all
      (fun factor => squarefreeCheck factor.polynomial) = true := by
  native_decide

end FTA.SquarefreeFactorization
