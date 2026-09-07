import FTA.AxisResultantNonzero
import FTA.ExecutableBivariate

/-!
# Closed executable axis resultants

This module closes the last representation gap in the safe-axis search.  It
builds the real and imaginary bivariate coordinate polynomials with finite
dense Horner programs, normalizes their outer coefficient lists, runs the
finite dense Sylvester determinant, and proves that the two resulting dense
rational polynomials are exactly the formal resultants used in the
nonvanishing proof.
-/

namespace FTA.AxisExecutableResultant

section

set_option quotPrecheck false

open CCL CCL.GaussianRat
open FTA.AxisResultant
open FTA.AxisResultantNonzero
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.ExecutableBivariate
open FTA.ExecutableBivariate.DenseBivariate

abbrev GaussianPolynomial := DensePolynomial QI
abbrev RatPolynomial := DensePolynomial ℚ
abbrev DenseBivariate := FTA.ExecutableBivariate.DenseBivariate ℚ
abbrev SparseBivariate := Polynomial (Polynomial ℚ)

/-! ## Executable coordinate polynomials -/

def coordinateStep (xVar yVar : DenseBivariate)
    (state : DenseBivariate × DenseBivariate) (a : QI) :
    DenseBivariate × DenseBivariate :=
  (add (sub (mul state.1 xVar) (mul state.2 yVar)) (constant a.re),
    add (add (mul state.1 yVar) (mul state.2 xVar)) (constant a.im))

def coordinatePolynomials (p : GaussianPolynomial)
    (xVar yVar : DenseBivariate) : DenseBivariate × DenseBivariate :=
  p.normalize.coeffs.foldl (coordinateStep xVar yVar) (zero, zero)

/-- `Y` is the outer/main variable and `X` the inner coefficient variable. -/
def verticalCoordinates (p : GaussianPolynomial) :
    DenseBivariate × DenseBivariate :=
  coordinatePolynomials p innerX outerX

/-- `X` is the outer/main variable and `Y` the inner coefficient variable. -/
def horizontalCoordinates (p : GaussianPolynomial) :
    DenseBivariate × DenseBivariate :=
  coordinatePolynomials p outerX innerX

private theorem eval_foldl_neg (x t : ℚ) :
    ∀ (coeffs : List RatPolynomial) (acc : ℚ),
      (coeffs.map (-·)).foldl
          (fun value a ↦ value * x + a.eval t) (-acc) =
        -(coeffs.foldl (fun value a ↦ value * x + a.eval t) acc)
  | [], _ => rfl
  | a :: as, acc => by
      simp only [List.map_cons, List.foldl_cons,
        FTA.ComputablePolynomial.DensePolynomial.eval_neg]
      rw [show -acc * x + -(a.eval t) = -(acc * x + a.eval t) by ring]
      exact eval_foldl_neg x t as (acc * x + a.eval t)

@[simp] theorem eval_neg (p : DenseBivariate) (x t : ℚ) :
    eval (neg p) x t = -eval p x t := by
  change (p.coeffs.map (-·)).foldl
      (fun value a ↦ value * x + a.eval t) 0 =
    -(p.coeffs.foldl (fun value a ↦ value * x + a.eval t) 0)
  exact eval_foldl_neg x t p.coeffs 0

@[simp] theorem eval_sub (p q : DenseBivariate) (x t : ℚ) :
    eval (DenseBivariate.sub p q) x t = eval p x t - eval q x t := by
  simp only [DenseBivariate.sub, DenseBivariate.eval_add, eval_neg,
    _root_.sub_eq_add_neg]

private theorem eval_coordinateFold_from
    (xVar yVar : DenseBivariate) (outer inner x y : ℚ)
    (hx : eval xVar outer inner = x) (hy : eval yVar outer inner = y)
    (coeffs : List QI) (A B : DenseBivariate) (z : QI)
    (hA : eval A outer inner = z.re) (hB : eval B outer inner = z.im) :
    let result := coeffs.foldl (coordinateStep xVar yVar) (A, B)
    eval result.1 outer inner =
        (coeffs.foldl (fun value a ↦ value * GaussianRat.mk x y + a) z).re ∧
      eval result.2 outer inner =
        (coeffs.foldl (fun value a ↦ value * GaussianRat.mk x y + a) z).im := by
  induction coeffs generalizing A B z with
  | nil => exact ⟨hA, hB⟩
  | cons a remaining ih =>
      simp only [List.foldl_cons]
      apply ih
      · simp [hx, hy, hA, hB, mul_re, add_re]
      · simp [hx, hy, hA, hB, mul_im, add_im]

theorem eval_verticalCoordinates (p : GaussianPolynomial) (x y : ℚ) :
    eval (verticalCoordinates p).1 y x =
        (p.eval (GaussianRat.mk x y)).re ∧
      eval (verticalCoordinates p).2 y x =
        (p.eval (GaussianRat.mk x y)).im := by
  rw [← DensePolynomial.eval_normalize p (GaussianRat.mk x y)]
  have evaluated := eval_coordinateFold_from innerX outerX y x x y
    (by simp) (by simp) p.normalize.coeffs zero zero 0 (by simp) (by simp)
  simpa only [verticalCoordinates, coordinatePolynomials,
    DensePolynomial.eval, DensePolynomial.evalCoeffs, zero_re, zero_im] using
      evaluated

theorem eval_horizontalCoordinates (p : GaussianPolynomial) (x y : ℚ) :
    eval (horizontalCoordinates p).1 x y =
        (p.eval (GaussianRat.mk x y)).re ∧
      eval (horizontalCoordinates p).2 x y =
        (p.eval (GaussianRat.mk x y)).im := by
  rw [← DensePolynomial.eval_normalize p (GaussianRat.mk x y)]
  have evaluated := eval_coordinateFold_from outerX innerX x y x y
    (by simp) (by simp) p.normalize.coeffs zero zero 0 (by simp) (by simp)
  simpa only [horizontalCoordinates, coordinatePolynomials,
    DensePolynomial.eval, DensePolynomial.evalCoeffs, zero_re, zero_im] using
      evaluated

/-! ## Proof-only sparse representation -/

def Represents (dense : DenseBivariate) (sparse : SparseBivariate) : Prop :=
  ∀ n, sparse.coeff n = (dense.coeff n).toPolynomial

theorem exists_represents (dense : DenseBivariate) :
    ∃ sparse : SparseBivariate, Represents dense sparse := by
  let sparse : SparseBivariate :=
    polynomialOfHighCoeffs (dense.coeffs.map fun q ↦ q.toPolynomial)
  refine ⟨sparse, ?_⟩
  intro n
  dsimp only [sparse]
  rw [coeff_polynomialOfHighCoeffs, coeff]
  rw [← List.map_reverse]
  have mapped := List.getD_map (n := n) dense.coeffs.reverse
    (0 : RatPolynomial) (fun q : RatPolynomial ↦ q.toPolynomial)
  rw [DensePolynomial.toPolynomial_zero] at mapped
  exact mapped

theorem map_eval_eq_atParameter_of_represents
    {dense : DenseBivariate} {sparse : SparseBivariate}
    (represents : Represents dense sparse) (t : ℚ) :
    sparse.map (Polynomial.evalRingHom t) = atParameter t dense := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map, represents, coeff_atParameter]
  change Polynomial.eval t (dense.coeff n).toPolynomial = _
  rw [DensePolynomial.eval_toPolynomial]

theorem represents_of_eval_eq
    (dense : DenseBivariate) (sparse : SparseBivariate)
    (equal : ∀ outer inner : ℚ,
      eval dense outer inner =
        (sparse.map (Polynomial.evalRingHom inner)).eval outer) :
    Represents dense sparse := by
  rcases exists_represents dense with ⟨candidate, candidateRepresents⟩
  have candidateEq : candidate = sparse := by
    apply Polynomial.ext
    intro n
    apply rationalPolynomial_eq_of_eval_eq_on_fin
    intro i
    let inner : ℚ := ((i : ℕ) : ℚ)
    have specialized :
        candidate.map (Polynomial.evalRingHom inner) =
          sparse.map (Polynomial.evalRingHom inner) := by
      apply rationalPolynomial_eq_of_eval_eq_on_fin
      intro j
      let outer : ℚ := ((j : ℕ) : ℚ)
      have candidateAtOuter := congrArg (Polynomial.eval outer)
        (map_eval_eq_atParameter_of_represents candidateRepresents inner)
      rw [eval_atParameter] at candidateAtOuter
      exact candidateAtOuter.trans (equal outer inner)
    have coefficients := congrArg (fun q : Polynomial ℚ ↦ q.coeff n)
      specialized
    simp only [Polynomial.coeff_map] at coefficients
    change Polynomial.eval inner (candidate.coeff n) =
      Polynomial.eval inner (sparse.coeff n) at coefficients
    exact coefficients
  rw [← candidateEq]
  exact candidateRepresents

private abbrev FormalBivariate := Polynomial (Polynomial ℚ)

local notation "formalCoordinateStep" =>
  fun (xVar yVar : FormalBivariate)
      (state : FormalBivariate × FormalBivariate) (a : QI) =>
    (state.1 * xVar - state.2 * yVar + Polynomial.C (Polynomial.C a.re),
      state.1 * yVar + state.2 * xVar + Polynomial.C (Polynomial.C a.im))

local notation "formalCoordinatePolynomials" =>
  fun (p : GaussianPolynomial) (xVar yVar : FormalBivariate) =>
    p.normalize.coeffs.foldl (formalCoordinateStep xVar yVar) (0, 0)

local notation "formalVerticalCoordinates" =>
  fun (p : GaussianPolynomial) =>
    formalCoordinatePolynomials p (Polynomial.C Polynomial.X) Polynomial.X

local notation "formalHorizontalCoordinates" =>
  fun (p : GaussianPolynomial) =>
    formalCoordinatePolynomials p Polynomial.X (Polynomial.C Polynomial.X)

theorem verticalCoordinates_represents (p : GaussianPolynomial) :
    Represents (verticalCoordinates p).1 (formalVerticalCoordinates p).1 ∧
      Represents (verticalCoordinates p).2 (formalVerticalCoordinates p).2 := by
  constructor
  · apply represents_of_eval_eq
    intro y x
    exact (eval_verticalCoordinates p x y).1.trans
      (FTA.AxisResultant.eval_verticalCoordinates p x y).1.symm
  · apply represents_of_eval_eq
    intro y x
    exact (eval_verticalCoordinates p x y).2.trans
      (FTA.AxisResultant.eval_verticalCoordinates p x y).2.symm

theorem horizontalCoordinates_represents (p : GaussianPolynomial) :
    Represents (horizontalCoordinates p).1 (formalHorizontalCoordinates p).1 ∧
      Represents (horizontalCoordinates p).2
        (formalHorizontalCoordinates p).2 := by
  constructor
  · apply represents_of_eval_eq
    intro x y
    exact (eval_horizontalCoordinates p x y).1.trans
      (FTA.AxisResultant.eval_horizontalCoordinates p x y).1.symm
  · apply represents_of_eval_eq
    intro x y
    exact (eval_horizontalCoordinates p x y).2.trans
      (FTA.AxisResultant.eval_horizontalCoordinates p x y).2.symm

/-! ## Executable outer normalization and degrees -/

def normalizeOuter (p : DenseBivariate) : DenseBivariate :=
  ⟨p.coeffs.dropWhile (·.isZero)⟩

def outerNatDegree (p : DenseBivariate) : ℕ :=
  (normalizeOuter p).coeffs.length - 1

private theorem eval_foldl_dropWhile_zero
    (coeffs : List RatPolynomial) (outer inner : ℚ) :
    (coeffs.dropWhile (·.isZero)).foldl
        (fun value a ↦ value * outer + a.eval inner) 0 =
      coeffs.foldl (fun value a ↦ value * outer + a.eval inner) 0 := by
  induction coeffs with
  | nil => rfl
  | cons a remaining ih =>
      by_cases zero : a.isZero = true
      · rw [List.dropWhile_cons_of_pos zero, List.foldl_cons,
          eval_eq_zero_of_isZero zero]
        rw [show (0 : ℚ) * outer + 0 = 0 by ring]
        exact ih
      · rw [List.dropWhile_cons_of_neg zero]

@[simp] theorem eval_normalizeOuter
    (p : DenseBivariate) (outer inner : ℚ) :
    eval (normalizeOuter p) outer inner = eval p outer inner := by
  exact eval_foldl_dropWhile_zero p.coeffs outer inner

theorem normalizeOuter_represents
    {dense : DenseBivariate} {sparse : SparseBivariate}
    (represents : Represents dense sparse) :
    Represents (normalizeOuter dense) sparse := by
  apply represents_of_eval_eq
  intro outer inner
  rw [eval_normalizeOuter]
  rw [← eval_atParameter]
  rw [← map_eval_eq_atParameter_of_represents represents]

theorem natDegree_eq_outerNatDegree
    {dense : DenseBivariate} {sparse : SparseBivariate}
    (represents : Represents dense sparse) :
    sparse.natDegree = outerNatDegree dense := by
  let normalized := normalizeOuter dense
  have normalizedRepresents : Represents normalized sparse :=
    normalizeOuter_represents represents
  cases coefficients : normalized.coeffs with
  | nil =>
      have sparseZero : sparse = 0 := by
        apply Polynomial.ext
        intro n
        rw [normalizedRepresents, coeff, coefficients]
        simp [DensePolynomial.toPolynomial_zero]
      simp [outerNatDegree, normalized, coefficients, sparseZero]
  | cons leading remaining =>
      have leadingNonzero : leading.isZero = false := by
        have normalizedCoefficients :
            normalized.coeffs =
              dense.coeffs.dropWhile (·.isZero) := rfl
        rw [coefficients] at normalizedCoefficients
        have head := List.head?_dropWhile_not
          (l := dense.coeffs) (p := fun q ↦ q.isZero)
        rw [← normalizedCoefficients] at head
        simpa only [List.head?_cons, Option.some.injEq] using head
      have leadingPolynomialNonzero : leading.toPolynomial ≠ 0 :=
        DensePolynomial.toPolynomial_ne_zero_of_isZero_false leadingNonzero
      have topCoefficient : normalized.coeff remaining.length = leading := by
        simp [coeff, coefficients]
      have sparseTop : sparse.coeff remaining.length ≠ 0 := by
        rw [normalizedRepresents, topCoefficient]
        exact leadingPolynomialNonzero
      have upper : sparse.natDegree ≤ remaining.length := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro n above
        rw [normalizedRepresents, coeff, coefficients]
        have outside : (leading :: remaining).reverse.length ≤ n := by
          simp only [List.length_reverse, List.length_cons]
          omega
        rw [List.getD_eq_default _ 0 outside,
          DensePolynomial.toPolynomial_zero]
      have lower : remaining.length ≤ sparse.natDegree :=
        Polynomial.le_natDegree_of_ne_zero sparseTop
      have degree : sparse.natDegree = remaining.length :=
        Nat.le_antisymm upper lower
      rw [degree]
      simp [outerNatDegree, normalized, coefficients]

/-! ## Closed dense Sylvester outputs -/

def verticalResultant (p : GaussianPolynomial) : RatPolynomial :=
  resultant (normalizeOuter (verticalCoordinates p).1)
    (normalizeOuter (verticalCoordinates p).2)
    (outerNatDegree (verticalCoordinates p).1)
    (outerNatDegree (verticalCoordinates p).2)

def horizontalResultant (p : GaussianPolynomial) : RatPolynomial :=
  resultant (normalizeOuter (horizontalCoordinates p).1)
    (normalizeOuter (horizontalCoordinates p).2)
    (outerNatDegree (horizontalCoordinates p).1)
    (outerNatDegree (horizontalCoordinates p).2)

local notation "formalVerticalResultant" =>
  fun (p : GaussianPolynomial) =>
    (formalVerticalCoordinates p).1.resultant (formalVerticalCoordinates p).2
      (formalVerticalCoordinates p).1.natDegree
      (formalVerticalCoordinates p).2.natDegree

local notation "formalHorizontalResultant" =>
  fun (p : GaussianPolynomial) =>
    (formalHorizontalCoordinates p).1.resultant
      (formalHorizontalCoordinates p).2
      (formalHorizontalCoordinates p).1.natDegree
      (formalHorizontalCoordinates p).2.natDegree

theorem verticalResultant_spec (p : GaussianPolynomial) :
    (verticalResultant p).toPolynomial = formalVerticalResultant p := by
  have eval_identity (x : ℚ) :
      (verticalResultant p).eval x = Polynomial.eval x (formalVerticalResultant p) := by
    let real := (verticalCoordinates p).1
    let imag := (verticalCoordinates p).2
    have realRepresents := (verticalCoordinates_represents p).1
    have imagRepresents := (verticalCoordinates_represents p).2
    have realNormalized := normalizeOuter_represents realRepresents
    have imagNormalized := normalizeOuter_represents imagRepresents
    have realDegree := natDegree_eq_outerNatDegree realRepresents
    have imagDegree := natDegree_eq_outerNatDegree imagRepresents
    rw [verticalResultant, eval_resultant]
    rw [evaluated_sylvester]
    rw [← map_eval_eq_atParameter_of_represents realNormalized,
      ← map_eval_eq_atParameter_of_represents imagNormalized]
    rw [← realDegree, ← imagDegree]
    exact (FTA.AxisResultant.eval_verticalResultant p x).symm
  apply rationalPolynomial_eq_of_eval_eq_on_fin
  intro i
  let x : ℚ := ((i : ℕ) : ℚ)
  rw [DensePolynomial.eval_toPolynomial]
  exact eval_identity x

theorem horizontalResultant_spec (p : GaussianPolynomial) :
    (horizontalResultant p).toPolynomial = formalHorizontalResultant p := by
  have eval_identity (y : ℚ) :
      (horizontalResultant p).eval y =
        Polynomial.eval y (formalHorizontalResultant p) := by
    let real := (horizontalCoordinates p).1
    let imag := (horizontalCoordinates p).2
    have realRepresents := (horizontalCoordinates_represents p).1
    have imagRepresents := (horizontalCoordinates_represents p).2
    have realNormalized := normalizeOuter_represents realRepresents
    have imagNormalized := normalizeOuter_represents imagRepresents
    have realDegree := natDegree_eq_outerNatDegree realRepresents
    have imagDegree := natDegree_eq_outerNatDegree imagRepresents
    rw [horizontalResultant, eval_resultant]
    rw [evaluated_sylvester]
    rw [← map_eval_eq_atParameter_of_represents realNormalized,
      ← map_eval_eq_atParameter_of_represents imagNormalized]
    rw [← realDegree, ← imagDegree]
    exact (FTA.AxisResultant.eval_horizontalResultant p y).symm
  apply rationalPolynomial_eq_of_eval_eq_on_fin
  intro i
  let y : ℚ := ((i : ℕ) : ℚ)
  rw [DensePolynomial.eval_toPolynomial]
  exact eval_identity y

/-- The fully computed coefficient data consumed by bounded safe-axis
searches. -/
def denseAxisResultants (p : GaussianPolynomial) (hp : p.isZero = false)
    (degree : 0 < p.natDegree) : DenseAxisResultants p :=
  denseAxisResultantsOfSpecifications p hp degree
    (verticalResultant p) (horizontalResultant p)
    (verticalResultant_spec p) (horizontalResultant_spec p)

/-- Closed coefficient-to-certificate program for both safe-axis
resultants. -/
def computedAxisEliminationCertificate
    (p : GaussianPolynomial) (hp : p.isZero = false)
    (degree : 0 < p.natDegree) :
    FTA.AxisSafeCuts.AxisEliminationCertificate p
      (2 * p.natDegree ^ 2) :=
  (denseAxisResultants p hp degree).toEliminationCertificate hp degree

end

end FTA.AxisExecutableResultant
