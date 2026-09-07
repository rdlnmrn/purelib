import FTA.PolynomialBounds
import FTA.BoxGeometry
import FTA.ExecutableBivariate
import FTA.FiniteResultant

/-!
# Gaussian difference resultants

This module formalizes the algebraic and quantitative content of Section 8 of
*A Finite Constructive Fundamental Theorem of Algebra over the Gaussian
Rationals*.  For `f ∈ ℚ(i)[X]` it constructs the bivariate divided difference
`Δ_f(X,T)`, its separation resultant `S_f(T)`, the Sylvester-adjugate Bézout
identity, and the positive rational exclusion neighbourhood from Lemma 8.1.

Everything is expressed over `ℚ(i)` and bounded using the exact rational norm
`N`; no real or complex completion is used.
-/

namespace FTA.GaussianDifferenceResultant

open CCL Polynomial
open FTA.ComputablePolynomial
open FTA.ExecutableBivariate
open scoped BigOperators

/-! The executable representation stores both variables as finite
high-to-low coefficient lists. -/
abbrev Bivariate := DenseBivariate QI

/-- The outer elimination variable. -/
def xVar : Bivariate := DenseBivariate.outerX

/-- The inner displacement parameter, embedded as an outer constant. -/
def tVar : Bivariate := DenseBivariate.innerX

/-- The translated outer variable `X + T`. -/
def translatedX : Bivariate := DenseBivariate.add xVar tVar

/-- Embed `ℚ(i)[X]` into `ℚ(i)[T][X]`, retaining `X` as the outer variable. -/
def lift (p : Polynomial QI) : Bivariate := DenseBivariate.lift p

/-- Substitute `X + T` for the outer variable. -/
def translate (p : Polynomial QI) : Bivariate :=
  DenseBivariate.composeOuter p translatedX

/-- The finite geometric quotient of `(X+T)^n-X^n` by `T`. -/
def powerDifferenceQuotient (n : ℕ) : Bivariate :=
  DenseBivariate.powerDifferenceQuotient n

/-- The explicit polynomial divided difference `Δ_p(X,T)`. -/
def dividedDifference (p : Polynomial QI) : Bivariate :=
  DenseBivariate.dividedDifference p

/-- Specialize coefficient polynomials at an arbitrary Gaussian rational
displacement. -/
def atParameter (t : QI) (q : Bivariate) : Polynomial QI :=
  DenseBivariate.atParameter t q

/-- Specialize the displacement parameter to zero. -/
def atZero (q : Bivariate) : Polynomial QI := atParameter 0 q

theorem atParameter_lift (p : Polynomial QI) (t : QI) :
    atParameter t (lift p) = p :=
  DenseBivariate.atParameter_lift p t

theorem atZero_dividedDifference (p : Polynomial QI) :
    atZero (dividedDifference p) = p.derivative :=
  DenseBivariate.atParameter_zero_dividedDifference p

theorem natDegree_atParameter_dividedDifference_le
    (p : Polynomial QI) (t : QI) :
    (atParameter t (dividedDifference p)).natDegree ≤ p.natDegree := by
  by_cases ht : t = 0
  · subst t
    rw [show atParameter 0 (dividedDifference p) = p.derivative from
      atZero_dividedDifference p]
    exact (Polynomial.natDegree_derivative_le p).trans (Nat.sub_le _ _)
  · let q := atParameter t (dividedDifference p)
    have hidentity : Polynomial.C t * q =
        p.comp (Polynomial.X + Polynomial.C t) - p := by
      exact DenseBivariate.atParameter_dividedDifference_identity p t
    have hcomp : (p.comp (Polynomial.X + Polynomial.C t)).natDegree ≤
        p.natDegree := by
      calc
        _ ≤ p.natDegree * (Polynomial.X + Polynomial.C t).natDegree :=
          Polynomial.natDegree_comp_le
        _ ≤ p.natDegree * 1 := by
          gcongr
          exact (Polynomial.natDegree_add_le _ _).trans (by simp)
        _ = p.natDegree := Nat.mul_one _
    calc
      q.natDegree = (Polynomial.C t * q).natDegree := by
        rw [Polynomial.natDegree_C_mul ht]
      _ = (p.comp (Polynomial.X + Polynomial.C t) - p).natDegree :=
        congrArg Polynomial.natDegree hidentity
      _ ≤ max (p.comp (Polynomial.X + Polynomial.C t)).natDegree p.natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ ≤ p.natDegree := max_le hcomp le_rfl

/-- Evaluate a bivariate polynomial first at the displacement parameter and
then at the elimination variable. -/
def evalBivariate (q : Bivariate) (x t : QI) : QI :=
  DenseBivariate.eval q x t

@[simp] theorem evalBivariate_lift (p : Polynomial QI) (x t : QI) :
    evalBivariate (lift p) x t = p.eval x := by
  exact DenseBivariate.eval_lift p x t

theorem evalBivariate_eq_sum_range (q : Bivariate) (x t : QI) :
    evalBivariate q x t =
      ∑ j ∈ Finset.range q.coeffs.length,
        (q.coeff j).eval t * x ^ j := by
  exact DenseBivariate.eval_eq_sum_range q x t

/-- A finite rational coefficient bound for a bivariate polynomial on a pair
of rational boxes. -/
def bivariateEvalBound
    (q : Bivariate) (xBox tBox : CCL.RatBox) : ℚ :=
  (q.coeffs.length : ℕ) *
    ∑ j ∈ Finset.range q.coeffs.length,
      evalBound (q.coeff j).toPolynomial tBox * boxNormBound xBox ^ j

theorem bivariateEvalBound_nonneg
    (q : Bivariate) (xBox tBox : CCL.RatBox) :
    0 ≤ bivariateEvalBound q xBox tBox := by
  dsimp only [bivariateEvalBound]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (evalBound_nonneg (q.coeff j).toPolynomial tBox)
    (pow_nonneg (boxNormBound_nonneg xBox) _)

/-- Soundness of the nested finite coefficient bound. -/
theorem normSq_evalBivariate_le_bivariateEvalBound
    (q : Bivariate) {xBox tBox : CCL.RatBox} {x t : QI}
    (hx : xBox.Contains x) (ht : tBox.Contains t) :
    GaussianRat.normSq (evalBivariate q x t) ≤
      bivariateEvalBound q xBox tBox := by
  rw [evalBivariate_eq_sum_range]
  calc
    GaussianRat.normSq
        (∑ j ∈ Finset.range q.coeffs.length,
          (q.coeff j).eval t * x ^ j) ≤
        ((Finset.range q.coeffs.length).card : ℚ) *
          ∑ j ∈ Finset.range q.coeffs.length,
            GaussianRat.normSq ((q.coeff j).eval t * x ^ j) :=
      normSq_finset_sum_le _ _
    _ = (q.coeffs.length : ℕ) *
          ∑ j ∈ Finset.range q.coeffs.length,
            GaussianRat.normSq ((q.coeff j).eval t) *
              GaussianRat.normSq x ^ j := by
      simp only [Finset.card_range, GaussianRat.normSq_mul,
        GaussianRat.normSq_pow]
    _ ≤ (q.coeffs.length : ℕ) *
          ∑ j ∈ Finset.range q.coeffs.length,
            evalBound (q.coeff j).toPolynomial tBox * boxNormBound xBox ^ j := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul
        (by simpa only [DensePolynomial.eval_toPolynomial] using
          normSq_eval_le_evalBound (q.coeff j).toPolynomial ht)
        (pow_le_pow_left₀ (GaussianRat.normSq_nonneg x)
          (normSq_le_boxNormBound hx) j)
        (pow_nonneg (GaussianRat.normSq_nonneg x) _)
        (evalBound_nonneg (q.coeff j).toPolynomial tBox)
    _ = bivariateEvalBound q xBox tBox := rfl

/-- Pointwise form of equation (13). -/
theorem eval_dividedDifference_identity (p : Polynomial QI) (x t : QI) :
    t * (atParameter t (dividedDifference p)).eval x =
      p.eval (x + t) + -p.eval x := by
  change t * Polynomial.eval x
      (DenseBivariate.atParameter t (DenseBivariate.dividedDifference p)) = _
  calc
    _ = t * DenseBivariate.eval (DenseBivariate.dividedDifference p) x t := by
      rw [DenseBivariate.eval_atParameter]
    _ = _ := by simpa only [sub_eq_add_neg] using
      DenseBivariate.eval_dividedDifference_identity p x t

/-- Equation (14): the Sylvester determinant in the outer variable. -/
def separationResultant (p : Polynomial QI) : Polynomial QI :=
  (DenseBivariate.resultant (lift p) (dividedDifference p)
    p.natDegree p.natDegree).toPolynomial

theorem atZero_lift (p : Polynomial QI) : atZero (lift p) = p := by
  exact atParameter_lift p 0

theorem eval_zero_separationResultant (p : Polynomial QI) :
    (separationResultant p).eval 0 =
      p.resultant p.derivative p.natDegree p.natDegree := by
  rw [separationResultant,
    DenseBivariate.eval_toPolynomial_resultant]
  change (DenseBivariate.atParameter 0 (DenseBivariate.lift p)).resultant
      (DenseBivariate.atParameter 0 (DenseBivariate.dividedDifference p))
        p.natDegree p.natDegree = _
  rw [DenseBivariate.atParameter_lift,
    DenseBivariate.atParameter_zero_dividedDifference]

theorem eval_separationResultant (p : Polynomial QI) (t : QI) :
    (separationResultant p).eval t =
      p.resultant (atParameter t (dividedDifference p))
        p.natDegree p.natDegree := by
  rw [separationResultant,
    DenseBivariate.eval_toPolynomial_resultant]
  change (DenseBivariate.atParameter t (DenseBivariate.lift p)).resultant
      (DenseBivariate.atParameter t (DenseBivariate.dividedDifference p))
        p.natDegree p.natDegree = _
  rw [DenseBivariate.atParameter_lift]
  rfl

/-- A finite squarefree certificate proves that the discriminant resultant,
and hence the constant coefficient of `S_f`, is nonzero. -/
theorem coeff_zero_separationResultant_ne_zero
    {p : Polynomial QI} (certificate : SquarefreeCert p) :
    (separationResultant p).coeff 0 ≠ 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_zero_separationResultant]
  have hp : p ≠ 0 := by
    intro hpZero
    rcases certificate.isCoprime with ⟨u, v, huv⟩
    rw [hpZero] at huv
    simp at huv
  have hdegree : p.derivative.natDegree ≤ p.natDegree :=
    (Polynomial.natDegree_derivative_le p).trans (Nat.sub_le _ _)
  have hraise := Polynomial.resultant_add_right_deg
    (f := p) (g := p.derivative) (m := p.natDegree)
    (n := p.derivative.natDegree)
    (p.natDegree - p.derivative.natDegree) le_rfl
  have hsum : p.derivative.natDegree +
      (p.natDegree - p.derivative.natDegree) = p.natDegree :=
    Nat.add_sub_of_le hdegree
  rw [hsum] at hraise
  rw [hraise]
  apply mul_ne_zero
  · apply pow_ne_zero
    simpa using Polynomial.leadingCoeff_ne_zero.mpr hp
  · exact FTA.FiniteResultant.resultant_ne_zero_of_isCoprime
      _ _ certificate.isCoprime

/-- A dense bivariate represents a sparse theorem polynomial coefficient by
coefficient. -/
def Represents (dense : Bivariate)
    (sparse : Polynomial (Polynomial QI)) : Prop :=
  ∀ n, sparse.coeff n = (dense.coeff n).toPolynomial

theorem exists_represents (dense : Bivariate) :
    ∃ sparse : Polynomial (Polynomial QI), Represents dense sparse := by
  let sparse : Polynomial (Polynomial QI) :=
    polynomialOfHighCoeffs (dense.coeffs.map fun q ↦ q.toPolynomial)
  refine ⟨sparse, ?_⟩
  intro n
  dsimp only [sparse]
  rw [coeff_polynomialOfHighCoeffs, DenseBivariate.coeff]
  rw [← List.map_reverse]
  have hmap := List.getD_map (n := n) dense.coeffs.reverse
    (0 : DensePolynomial QI) (fun q : DensePolynomial QI => q.toPolynomial)
  have hzero : (0 : DensePolynomial QI).toPolynomial = 0 := by
    apply Polynomial.ext
    intro k
    rw [DensePolynomial.coeff_toPolynomial]
    change ([] : List QI).reverse.getD k 0 = 0
    simp
  rw [hzero] at hmap
  exact hmap

theorem map_eval_eq_atParameter_of_represents
    {dense : Bivariate} {sparse : Polynomial (Polynomial QI)}
    (h : Represents dense sparse) (t : QI) :
    sparse.map (Polynomial.evalRingHom t) = atParameter t dense := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map, h, atParameter,
    DenseBivariate.coeff_atParameter]
  change Polynomial.eval t (dense.coeff n).toPolynomial = _
  rw [DensePolynomial.eval_toPolynomial]

theorem eval_sparse_eq_evalBivariate_of_represents
    {dense : Bivariate} {sparse : Polynomial (Polynomial QI)}
    (h : Represents dense sparse) (x t : QI) :
    (sparse.eval (Polynomial.C x)).eval t = evalBivariate dense x t := by
  change (Polynomial.evalRingHom t) (sparse.eval (Polynomial.C x)) = _
  rw [← Polynomial.eval_map_apply]
  rw [map_eval_eq_atParameter_of_represents h]
  rw [show (Polynomial.evalRingHom t) (Polynomial.C x) = x by simp]
  change Polynomial.eval x (DenseBivariate.atParameter t dense) =
    DenseBivariate.eval dense x t
  exact DenseBivariate.eval_atParameter dense x t

theorem exists_dense_represents (sparse : Polynomial (Polynomial QI)) :
    ∃ dense : Bivariate, Represents dense sparse := by
  let dense : Bivariate :=
    ⟨sparse.coeffList.map fun q ↦
      (⟨q.coeffList⟩ : DensePolynomial QI)⟩
  refine ⟨dense, ?_⟩
  intro n
  have houter := congrArg (fun q : Polynomial (Polynomial QI) ↦ q.coeff n)
    (polynomialOfHighCoeffs_coeffList sparse)
  rw [coeff_polynomialOfHighCoeffs] at houter
  rw [DenseBivariate.coeff]
  dsimp only [dense]
  rw [← List.map_reverse]
  have hmap := List.getD_map (n := n) sparse.coeffList.reverse
    (0 : Polynomial QI) (fun q ↦ (⟨q.coeffList⟩ : DensePolynomial QI))
  rw [show (⟨(0 : Polynomial QI).coeffList⟩ : DensePolynomial QI) = 0 by
    apply DensePolynomial.ext
    exact Polynomial.coeffList_zero QI] at hmap
  rw [hmap]
  change sparse.coeff n =
    (⟨(sparse.coeffList.reverse.getD n 0).coeffList⟩ :
      DensePolynomial QI).toPolynomial
  rw [show (⟨(sparse.coeffList.reverse.getD n 0).coeffList⟩ :
      DensePolynomial QI).toPolynomial = sparse.coeffList.reverse.getD n 0 from
    polynomialOfHighCoeffs_coeffList _]
  exact houter.symm

/-- The pointwise Sylvester-adjugate identity consumed by the quantitative
root-pair contradiction. -/
def ResultantBezoutIdentity (p : Polynomial QI) (A B : Bivariate) : Prop :=
  ∀ u t,
    evalBivariate A u t * p.eval u +
      evalBivariate B u t * evalBivariate (dividedDifference p) u t =
        (separationResultant p).eval t

/-- Equation (15), obtained from the finite Sylvester adjugate. -/
theorem exists_resultant_bezout (p : Polynomial QI)
    (hdegree : p.natDegree ≠ 0) :
    ∃ A B : Bivariate,
      ResultantBezoutIdentity p A B := by
  obtain ⟨deltaSparse, hdelta⟩ := exists_represents (dividedDifference p)
  let liftSparse : Polynomial (Polynomial QI) := p.map Polynomial.C
  have hliftDegree : liftSparse.natDegree = p.natDegree := by
    exact Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective p
  have hdeltaDegree : deltaSparse.natDegree ≤ p.natDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    have hp : p ≠ 0 := by
      intro hpZero
      subst p
      simp at hdegree
    have hcoeffListLength : p.coeffList.length = p.natDegree + 1 := by
      rw [Polynomial.coeffList,
        Polynomial.withBotSucc_degree_eq_natDegree_add_one hp]
      simp
    have hdenseLength :=
      DenseBivariate.dividedDifference_coeffs_length_le_coeffList p
    have hnLength : (dividedDifference p).coeffs.length ≤ n := by
      change (DenseBivariate.dividedDifference p).coeffs.length ≤ n
      rw [hcoeffListLength] at hdenseLength
      omega
    have hdenseCoeff : (dividedDifference p).coeff n = 0 := by
      rw [DenseBivariate.coeff, List.getD_eq_default]
      simpa using hnLength
    rw [hdelta n, hdenseCoeff]
    exact DensePolynomial.toPolynomial_zero
  obtain ⟨A₀, B₀, _hA, _hB, hbezout⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant
      (R := Polynomial QI) (m := p.natDegree)
      (n := p.natDegree)
      liftSparse deltaSparse
      hliftDegree.le hdeltaDegree
      (Or.inl (by simpa using hdegree))
  obtain ⟨A, hA⟩ := exists_dense_represents A₀
  obtain ⟨B, hB⟩ := exists_dense_represents B₀
  refine ⟨A, B, ?_⟩
  intro u t
  have hevaluated := congrArg
    (fun q : Polynomial (Polynomial QI) ↦ (q.eval (Polynomial.C u)).eval t)
    hbezout
  have hresultant :
      (liftSparse.resultant deltaSparse p.natDegree p.natDegree).eval t =
        (separationResultant p).eval t := by
    have hmap := Polynomial.resultant_map_map
      (f := liftSparse) (g := deltaSparse)
      (m := p.natDegree) (n := p.natDegree) (Polynomial.evalRingHom t)
    calc
      _ = (liftSparse.map (Polynomial.evalRingHom t)).resultant
          (deltaSparse.map (Polynomial.evalRingHom t))
            p.natDegree p.natDegree := hmap.symm
      _ = p.resultant (atParameter t (dividedDifference p))
          p.natDegree p.natDegree := by
        rw [show liftSparse.map (Polynomial.evalRingHom t) = p from by
          dsimp only [liftSparse]
          rw [Polynomial.map_map]
          have hhom : (Polynomial.evalRingHom t).comp Polynomial.C =
              RingHom.id QI := by
            apply RingHom.ext
            intro a
            change Polynomial.eval t (Polynomial.C a) = a
            simp
          rw [hhom, Polynomial.map_id]]
        rw [map_eval_eq_atParameter_of_represents hdelta]
      _ = _ := (eval_separationResultant p t).symm
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hevaluated
  rw [eval_sparse_eq_evalBivariate_of_represents hA,
    eval_sparse_eq_evalBivariate_of_represents hB] at hevaluated
  have hliftEval : (liftSparse.eval (Polynomial.C u)).eval t = p.eval u := by
    simp [liftSparse, Polynomial.eval_map]
  rw [hliftEval,
    eval_sparse_eq_evalBivariate_of_represents hdelta, hresultant] at hevaluated
  simpa only [mul_comm] using hevaluated

/-! ## Lemma 8.1: a finite exclusion neighbourhood -/

/-- The fixed rational box used to bound `S_f` between zero and every
displacement of norm less than one. -/
def unitBox : CCL.RatBox := CCL.RatBox.symmetric 1 (by norm_num)

theorem unitBox_contains_zero : unitBox.Contains 0 := by
  norm_num [unitBox, CCL.RatBox.symmetric, CCL.RatBox.Contains]

theorem unitBox_contains_of_normSq_lt_one {z : QI}
    (hz : GaussianRat.normSq z < 1) : unitBox.Contains z := by
  have hreSq : z.re ^ 2 < 1 := by
    dsimp [GaussianRat.normSq] at hz
    nlinarith [sq_nonneg z.im]
  have himSq : z.im ^ 2 < 1 := by
    dsimp [GaussianRat.normSq] at hz
    nlinarith [sq_nonneg z.re]
  dsimp [unitBox, CCL.RatBox.symmetric, CCL.RatBox.Contains]
  constructor
  · nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.re - 1)]
  constructor
  · nlinarith [sq_nonneg (z.re + 1), sq_nonneg (z.re - 1)]
  constructor
  · nlinarith [sq_nonneg (z.im + 1), sq_nonneg (z.im - 1)]
  · nlinarith [sq_nonneg (z.im + 1), sq_nonneg (z.im - 1)]

/-- The positive radius computed from the coefficients of a polynomial and
its nonzero constant term. -/
def coefficientExclusionRadius (S : Polynomial QI) : ℚ :=
  min 1 (GaussianRat.normSq (S.coeff 0) /
    (4 * lipschitzBound S unitBox))

/-- The explicit lower norm margin used in Lemma 8.1. -/
def coefficientExclusionMargin (S : Polynomial QI) : ℚ :=
  GaussianRat.normSq (S.coeff 0) / 4

theorem coefficientExclusionRadius_pos {S : Polynomial QI}
    (hconstant : S.coeff 0 ≠ 0) :
    0 < coefficientExclusionRadius S := by
  have hnorm : 0 < GaussianRat.normSq (S.coeff 0) :=
    GaussianRat.normSq_pos hconstant
  have hL : 0 < lipschitzBound S unitBox := lipschitzBound_pos S unitBox
  apply lt_min
  · norm_num
  · positivity

theorem coefficientExclusionRadius_le_one (S : Polynomial QI) :
    coefficientExclusionRadius S ≤ 1 := min_le_left _ _

theorem coefficientExclusionMargin_pos {S : Polynomial QI}
    (hconstant : S.coeff 0 ≠ 0) :
    0 < coefficientExclusionMargin S := by
  exact div_pos (GaussianRat.normSq_pos hconstant) (by norm_num)

/-- The quantitative exclusion statement of Lemma 8.1. -/
theorem normSq_eval_ge_coefficientExclusionMargin
    {S : Polynomial QI} (hconstant : S.coeff 0 ≠ 0) {t : QI}
    (ht : GaussianRat.normSq t < coefficientExclusionRadius S ^ 2) :
    coefficientExclusionMargin S ≤ GaussianRat.normSq (S.eval t) := by
  let radius := coefficientExclusionRadius S
  let L := lipschitzBound S unitBox
  let N₀ := GaussianRat.normSq (S.coeff 0)
  have hradiusPos : 0 < radius := coefficientExclusionRadius_pos hconstant
  have hradiusOne : radius ≤ 1 := coefficientExclusionRadius_le_one S
  have hradiusNonneg : 0 ≤ radius := hradiusPos.le
  have hradiusSqLe : radius ^ 2 ≤ radius := by
    nlinarith [sq_nonneg radius, mul_nonneg hradiusNonneg (sub_nonneg.mpr hradiusOne)]
  have htRadius : GaussianRat.normSq t < radius := ht.trans_le hradiusSqLe
  have htOne : GaussianRat.normSq t < 1 := htRadius.trans_le hradiusOne
  have htContains : unitBox.Contains t := unitBox_contains_of_normSq_lt_one htOne
  have hzeroContains : unitBox.Contains (0 : QI) := unitBox_contains_zero
  have hLPos : 0 < L := lipschitzBound_pos S unitBox
  have hradiusRatio : radius ≤ N₀ / (4 * L) := min_le_right _ _
  have hdifferenceBound :=
    normSq_eval_sub_le_lipschitzBound_mul S hzeroContains htContains
  have hdifference :
      GaussianRat.normSq (S.coeff 0 - S.eval t) < N₀ / 4 := by
    have hscaled : L * GaussianRat.normSq t < N₀ / 4 := by
      calc
        L * GaussianRat.normSq t < L * radius :=
          mul_lt_mul_of_pos_left htRadius hLPos
        _ ≤ L * (N₀ / (4 * L)) :=
          mul_le_mul_of_nonneg_left hradiusRatio hLPos.le
        _ = N₀ / 4 := by field_simp [ne_of_gt hLPos]
    have hevalZero : S.eval 0 = S.coeff 0 :=
      (Polynomial.coeff_zero_eq_eval_zero S).symm
    rw [hevalZero, GaussianRat.zero_sub,
      GaussianRat.normSq_neg] at hdifferenceBound
    exact hdifferenceBound.trans_lt hscaled
  have hreverse := GaussianRat.normSq_add_le_two
    (S.coeff 0 - S.eval t) (S.eval t)
  have hadd : S.coeff 0 - S.eval t + S.eval t = S.coeff 0 := by
    apply GaussianRat.ext <;> simp
  rw [hadd] at hreverse
  dsimp only [coefficientExclusionMargin, N₀]
  nlinarith

/-- The coefficient-computable radius attached to the squarefree separation
resultant. -/
def squarefreeSeparationRadius
    {p : Polynomial QI} (_certificate : SquarefreeCert p) : ℚ :=
  coefficientExclusionRadius (separationResultant p)

/-- The coefficient-computable positive lower bound attached to `S_f`. -/
def squarefreeSeparationMargin
    {p : Polynomial QI} (_certificate : SquarefreeCert p) : ℚ :=
  coefficientExclusionMargin (separationResultant p)

theorem squarefreeSeparationRadius_pos
    {p : Polynomial QI} (certificate : SquarefreeCert p) :
    0 < squarefreeSeparationRadius certificate :=
  coefficientExclusionRadius_pos
    (coeff_zero_separationResultant_ne_zero certificate)

theorem squarefreeSeparationMargin_pos
    {p : Polynomial QI} (certificate : SquarefreeCert p) :
    0 < squarefreeSeparationMargin certificate :=
  coefficientExclusionMargin_pos
    (coeff_zero_separationResultant_ne_zero certificate)

/-- Lemma 8.1 specialized to the squarefree separation resultant. -/
theorem normSq_separationResultant_eval_ge_margin
    {p : Polynomial QI} (certificate : SquarefreeCert p) {t : QI}
    (ht : GaussianRat.normSq t <
      squarefreeSeparationRadius certificate ^ 2) :
    squarefreeSeparationMargin certificate ≤
      GaussianRat.normSq ((separationResultant p).eval t) :=
  normSq_eval_ge_coefficientExclusionMargin
    (coeff_zero_separationResultant_ne_zero certificate) ht

/-! ## The finite algebraic contradiction behind Theorem 8.2 -/

/-- Evaluating equation (15) at a Gaussian-rational pair `(u,t)`. -/
theorem eval_resultant_bezout
    {p : Polynomial QI} {A B : Bivariate}
    (hbezout : ResultantBezoutIdentity p A B) (u t : QI) :
    evalBivariate A u t * p.eval u +
        evalBivariate B u t *
          evalBivariate (dividedDifference p) u t =
      (separationResultant p).eval t := hbezout u t

/-- Two sufficiently accurate approximate roots with a certified positive
gap and displacement below the exclusion radius contradict the Sylvester
adjugate identity.  This is the exact finite inequality argument at the core
of Theorem 8.2. -/
theorem residual_pair_contradiction
    {p : Polynomial QI} (certificate : SquarefreeCert p)
    (ambient : CCL.RatBox) {A B : Bivariate}
    (hbezout : ResultantBezoutIdentity p A B)
    {u v : QI} (hu : ambient.Contains u)
    {gapSq residual : ℚ} (hgapPos : 0 < gapSq)
    (hgap : gapSq ≤ GaussianRat.normSq (v - u))
    (hclose : GaussianRat.normSq (v - u) <
      squarefreeSeparationRadius certificate ^ 2)
    (huResidual : GaussianRat.normSq (p.eval u) ≤ residual)
    (hvResidual : GaussianRat.normSq (p.eval v) ≤ residual)
    (hsmall :
      2 * (bivariateEvalBound A ambient unitBox * residual +
        bivariateEvalBound B ambient unitBox * (4 * residual / gapSq)) <
          squarefreeSeparationMargin certificate) : False := by
  let t := v - u
  let delta := evalBivariate (dividedDifference p) u t
  have htGap : gapSq ≤ GaussianRat.normSq t := by
    simpa only [t] using hgap
  have htNormPos : 0 < GaussianRat.normSq t := hgapPos.trans_le htGap
  have htNe : t ≠ 0 := by
    intro htZero
    rw [htZero, GaussianRat.normSq_zero] at htNormPos
    exact lt_irrefl 0 htNormPos
  have huShift : u + t = v := by
    dsimp only [t]
    apply GaussianRat.ext <;> simp
  have hdeltaIdentity :
      t * delta = p.eval v + -p.eval u := by
    have h := eval_dividedDifference_identity p u t
    rw [huShift] at h
    simpa only [delta, evalBivariate, atParameter, dividedDifference,
      DenseBivariate.eval_atParameter] using h
  have hresidualDifference :
      GaussianRat.normSq (p.eval v + -p.eval u) ≤ 4 * residual := by
    calc
      GaussianRat.normSq (p.eval v + -p.eval u) ≤
          2 * (GaussianRat.normSq (p.eval v) +
            GaussianRat.normSq (-p.eval u)) :=
        GaussianRat.normSq_add_le_two _ _
      _ = 2 * (GaussianRat.normSq (p.eval v) +
            GaussianRat.normSq (p.eval u)) := by
        rw [GaussianRat.normSq_neg]
      _ ≤ 2 * (residual + residual) := by gcongr
      _ = 4 * residual := by ring
  have hdeltaProduct :
      GaussianRat.normSq t * GaussianRat.normSq delta ≤ 4 * residual := by
    have hnorm := congrArg GaussianRat.normSq hdeltaIdentity
    rw [GaussianRat.normSq_mul] at hnorm
    rw [hnorm]
    exact hresidualDifference
  have hgapProduct :
      gapSq * GaussianRat.normSq delta ≤ 4 * residual :=
    (mul_le_mul_of_nonneg_right htGap
      (GaussianRat.normSq_nonneg delta)).trans hdeltaProduct
  have hdeltaBound :
      GaussianRat.normSq delta ≤ 4 * residual / gapSq := by
    rw [le_div_iff₀ hgapPos]
    simpa only [mul_comm] using hgapProduct
  have hradiusPos : 0 < squarefreeSeparationRadius certificate :=
    squarefreeSeparationRadius_pos certificate
  have hradiusOne : squarefreeSeparationRadius certificate ≤ 1 :=
    coefficientExclusionRadius_le_one (separationResultant p)
  have hradiusSqLe :
      squarefreeSeparationRadius certificate ^ 2 ≤
        squarefreeSeparationRadius certificate := by
    nlinarith [sq_nonneg (squarefreeSeparationRadius certificate),
      mul_nonneg hradiusPos.le (sub_nonneg.mpr hradiusOne)]
  have htClose : GaussianRat.normSq t <
      squarefreeSeparationRadius certificate ^ 2 := by
    simpa only [t] using hclose
  have htOne : GaussianRat.normSq t < 1 :=
    htClose.trans_le (hradiusSqLe.trans hradiusOne)
  have htContains : unitBox.Contains t :=
    unitBox_contains_of_normSq_lt_one htOne
  have hA := normSq_evalBivariate_le_bivariateEvalBound A hu htContains
  have hB := normSq_evalBivariate_le_bivariateEvalBound B hu htContains
  have hAterm :
      GaussianRat.normSq (evalBivariate A u t) *
          GaussianRat.normSq (p.eval u) ≤
        bivariateEvalBound A ambient unitBox * residual :=
    mul_le_mul hA huResidual
      (GaussianRat.normSq_nonneg (p.eval u))
      (bivariateEvalBound_nonneg A ambient unitBox)
  have hBterm :
      GaussianRat.normSq (evalBivariate B u t) *
          GaussianRat.normSq delta ≤
        bivariateEvalBound B ambient unitBox *
          (4 * residual / gapSq) :=
    mul_le_mul hB hdeltaBound
      (GaussianRat.normSq_nonneg delta)
      (bivariateEvalBound_nonneg B ambient unitBox)
  have hbezoutEval := eval_resultant_bezout hbezout u t
  have hresultantUpper :
      GaussianRat.normSq ((separationResultant p).eval t) ≤
        2 * (bivariateEvalBound A ambient unitBox * residual +
          bivariateEvalBound B ambient unitBox *
            (4 * residual / gapSq)) := by
    rw [← hbezoutEval]
    calc
      GaussianRat.normSq
          (evalBivariate A u t * p.eval u +
            evalBivariate B u t * delta) ≤
          2 * (GaussianRat.normSq (evalBivariate A u t * p.eval u) +
            GaussianRat.normSq (evalBivariate B u t * delta)) :=
        GaussianRat.normSq_add_le_two _ _
      _ = 2 *
          (GaussianRat.normSq (evalBivariate A u t) *
              GaussianRat.normSq (p.eval u) +
            GaussianRat.normSq (evalBivariate B u t) *
              GaussianRat.normSq delta) := by
        rw [GaussianRat.normSq_mul, GaussianRat.normSq_mul]
      _ ≤ 2 * (bivariateEvalBound A ambient unitBox * residual +
          bivariateEvalBound B ambient unitBox *
            (4 * residual / gapSq)) := by
        gcongr
  have hresultantLower :=
    normSq_separationResultant_eval_ge_margin certificate
      (by simpa only [t] using hclose)
  linarith

/-- A positive rational residual threshold which makes the final inequality
in the two-centre contradiction automatic. -/
def rootPairResidualThreshold
    {p : Polynomial QI} (certificate : SquarefreeCert p)
    (A B : Bivariate) (ambient : CCL.RatBox) (gapSq : ℚ) : ℚ :=
  squarefreeSeparationMargin certificate /
    (4 * max 1
      (bivariateEvalBound A ambient unitBox +
        4 * bivariateEvalBound B ambient unitBox / gapSq))

theorem rootPairResidualThreshold_pos
    {p : Polynomial QI} (certificate : SquarefreeCert p)
    (A B : Bivariate) (ambient : CCL.RatBox) {gapSq : ℚ}
    (hgapPos : 0 < gapSq) :
    0 < rootPairResidualThreshold certificate A B ambient gapSq := by
  have hA := bivariateEvalBound_nonneg A ambient unitBox
  have hB := bivariateEvalBound_nonneg B ambient unitBox
  have hsum : 0 ≤ bivariateEvalBound A ambient unitBox +
      4 * bivariateEvalBound B ambient unitBox / gapSq := by
    positivity
  have hmajorant : 0 < max 1
      (bivariateEvalBound A ambient unitBox +
        4 * bivariateEvalBound B ambient unitBox / gapSq) :=
    zero_lt_one.trans_le (le_max_left _ _)
  exact div_pos (squarefreeSeparationMargin_pos certificate)
    (mul_pos (by norm_num) hmajorant)

theorem rootPairResidualThreshold_small
    {p : Polynomial QI} (certificate : SquarefreeCert p)
    (A B : Bivariate) (ambient : CCL.RatBox) {gapSq : ℚ}
    (hgapPos : 0 < gapSq) :
    2 * (bivariateEvalBound A ambient unitBox *
          rootPairResidualThreshold certificate A B ambient gapSq +
        bivariateEvalBound B ambient unitBox *
          (4 * rootPairResidualThreshold certificate A B ambient gapSq /
            gapSq)) < squarefreeSeparationMargin certificate := by
  let coefficient := bivariateEvalBound A ambient unitBox +
    4 * bivariateEvalBound B ambient unitBox / gapSq
  let majorant := max 1 coefficient
  let margin := squarefreeSeparationMargin certificate
  let threshold := rootPairResidualThreshold certificate A B ambient gapSq
  have hmajorantPos : 0 < majorant :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hcoefficientLe : coefficient ≤ majorant := le_max_right _ _
  have hthresholdNonneg : 0 ≤ threshold :=
    (rootPairResidualThreshold_pos certificate A B ambient hgapPos).le
  have hmarginPos : 0 < margin := squarefreeSeparationMargin_pos certificate
  calc
    2 * (bivariateEvalBound A ambient unitBox * threshold +
        bivariateEvalBound B ambient unitBox * (4 * threshold / gapSq)) =
        2 * (coefficient * threshold) := by
      dsimp only [coefficient]
      ring
    _ ≤ 2 * (majorant * threshold) := by
      gcongr
    _ = margin / 2 := by
      dsimp only [threshold, rootPairResidualThreshold, margin, majorant,
        coefficient]
      field_simp [ne_of_gt hmajorantPos]
      ring
    _ < margin := by linarith

/-- The two-centre contradiction with the computed residual threshold, so no
caller-supplied analytic smallness inequality remains. -/
theorem residual_pair_contradiction_at_computed_threshold
    {p : Polynomial QI} (certificate : SquarefreeCert p)
    (ambient : CCL.RatBox) {A B : Bivariate}
    (hbezout : ResultantBezoutIdentity p A B)
    {u v : QI} (hu : ambient.Contains u)
    {gapSq : ℚ} (hgapPos : 0 < gapSq)
    (hgap : gapSq ≤ GaussianRat.normSq (v - u))
    (hclose : GaussianRat.normSq (v - u) <
      squarefreeSeparationRadius certificate ^ 2)
    (huResidual : GaussianRat.normSq (p.eval u) ≤
      rootPairResidualThreshold certificate A B ambient gapSq)
    (hvResidual : GaussianRat.normSq (p.eval v) ≤
      rootPairResidualThreshold certificate A B ambient gapSq) : False := by
  exact residual_pair_contradiction certificate ambient hbezout hu
    hgapPos hgap hclose huResidual hvResidual
    (rootPairResidualThreshold_small certificate A B ambient hgapPos)

/-- Common-box geometry supplies the small-displacement premise in the
preceding contradiction theorem. -/
theorem residual_pair_contradiction_of_common_box
    {p : Polynomial QI} (certificate : SquarefreeCert p)
    (ambient common : CCL.RatBox) {A B : Bivariate}
    (hbezout : ResultantBezoutIdentity p A B)
    {u v : QI} (huAmbient : ambient.Contains u)
    (huCommon : common.Contains u) (hvCommon : common.Contains v)
    {gapSq residual : ℚ} (hgapPos : 0 < gapSq)
    (hgap : gapSq ≤ GaussianRat.normSq (v - u))
    (hdiagonal : common.diagonalSq <
      squarefreeSeparationRadius certificate ^ 2)
    (huResidual : GaussianRat.normSq (p.eval u) ≤ residual)
    (hvResidual : GaussianRat.normSq (p.eval v) ≤ residual)
    (hsmall :
      2 * (bivariateEvalBound A ambient unitBox * residual +
        bivariateEvalBound B ambient unitBox * (4 * residual / gapSq)) <
          squarefreeSeparationMargin certificate) : False := by
  apply residual_pair_contradiction certificate ambient hbezout huAmbient
    hgapPos hgap
  · exact (CCL.RatBox.normSq_sub_le_diagonalSq hvCommon huCommon).trans_lt
      hdiagonal
  · exact huResidual
  · exact hvResidual
  · exact hsmall

/-- Fully geometric two-track contradiction for displayed finite separation
data.  The winding-one hypothesis of Theorem 8.2 is used only to obtain the
two residual premises via Lemma 7.2; all remaining work is discharged here. -/
theorem residual_pair_contradiction_of_coordinate_gap
    {p : Polynomial QI} (certificate : SquarefreeCert p)
    (ambient common left right : CCL.RatBox) {A B : Bivariate}
    (hbezout : ResultantBezoutIdentity p A B)
    {u v : QI} (huAmbient : ambient.Contains u)
    (huLeft : left.Contains u) (hvRight : right.Contains v)
    (huCommon : common.Contains u) (hvCommon : common.Contains v)
    {gap : ℚ} (hgapPos : 0 < gap)
    (hgap : left.xUpper + gap ≤ right.xLower ∨
      right.xUpper + gap ≤ left.xLower ∨
      left.yUpper + gap ≤ right.yLower ∨
      right.yUpper + gap ≤ left.yLower)
    (hdiagonal : common.diagonalSq <
      squarefreeSeparationRadius certificate ^ 2)
    (huResidual : GaussianRat.normSq (p.eval u) ≤
      rootPairResidualThreshold certificate A B ambient (gap ^ 2))
    (hvResidual : GaussianRat.normSq (p.eval v) ≤
      rootPairResidualThreshold certificate A B ambient (gap ^ 2)) : False := by
  have hgapSqPos : 0 < gap ^ 2 := sq_pos_of_pos hgapPos
  have hgapSq : gap ^ 2 ≤ GaussianRat.normSq (v - u) :=
    CCL.RatBox.sq_le_normSq_sub_of_coordinate_gap
      hgapPos hgap huLeft hvRight
  apply residual_pair_contradiction_at_computed_threshold
    certificate ambient hbezout huAmbient hgapSqPos hgapSq
  · exact (CCL.RatBox.normSq_sub_le_diagonalSq hvCommon huCommon).trans_lt
      hdiagonal
  · exact huResidual
  · exact hvResidual

end FTA.GaussianDifferenceResultant
