import FTA.AxisSafeCuts
import FTA.FiniteResultant

/-!
# Bivariate coordinate polynomials for axis elimination

For a dense Gaussian-rational polynomial `p`, this module constructs the two
rational bivariate polynomials `A_p(X,Y)` and `B_p(X,Y)` by a finite Horner
fold.  Both orientations used by the paper are retained: in the vertical
orientation `Y` is the Sylvester variable and `X` belongs to the coefficient
ring; in the horizontal orientation those roles are reversed.

The main results below identify exact coefficient specialization with the
already executable dense path polynomials.  Thus the subsequent Sylvester
determinants operate on precisely the coordinate polynomials used by winding
and path-clearance code, rather than on a parallel specification.
-/

namespace FTA.AxisResultant

section

set_option quotPrecheck false

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.Winding

abbrev GaussianPolynomial := DensePolynomial QI
abbrev RatPolynomial := DensePolynomial ℚ
abbrev Bivariate := Polynomial (Polynomial ℚ)

/-- Evaluate the coefficient variable first and the main polynomial variable
second. -/
local notation "bivariateEval" =>
  fun (q : Bivariate) (coefficientValue variableValue : ℚ) =>
    (q.map (Polynomial.evalRingHom coefficientValue)).eval variableValue

/-- One bivariate Horner step for
`(A+iB)(X+iY)+(a.re+i*a.im)`. -/
local notation "coordinateStep" =>
  fun (xVar yVar : Bivariate) (state : Bivariate × Bivariate) (a : QI) =>
    (state.1 * xVar - state.2 * yVar + Polynomial.C (Polynomial.C a.re),
      state.1 * yVar + state.2 * xVar + Polynomial.C (Polynomial.C a.im))

/-- Finite high-to-low Horner construction of `(A_p,B_p)`. -/
local notation "coordinatePolynomials" =>
  fun (p : GaussianPolynomial) (xVar yVar : Bivariate) =>
    p.normalize.coeffs.foldl (coordinateStep xVar yVar) (0, 0)

private theorem eval_coordinateFold_from
    (xVar yVar : Bivariate) (coefficientValue variableValue x y : ℚ)
    (hx : bivariateEval xVar coefficientValue variableValue = x)
    (hy : bivariateEval yVar coefficientValue variableValue = y)
    (cs : List QI) (A B : Bivariate) (z : QI)
    (hA : bivariateEval A coefficientValue variableValue = z.re)
    (hB : bivariateEval B coefficientValue variableValue = z.im) :
    let result := cs.foldl (coordinateStep xVar yVar) (A, B)
    bivariateEval result.1 coefficientValue variableValue =
        (cs.foldl (fun value a => value * GaussianRat.mk x y + a) z).re ∧
      bivariateEval result.2 coefficientValue variableValue =
        (cs.foldl (fun value a => value * GaussianRat.mk x y + a) z).im := by
  induction cs generalizing A B z with
  | nil => exact ⟨hA, hB⟩
  | cons a as ih =>
      simp only [List.foldl_cons]
      apply ih
      · dsimp only at hx hy hA hB ⊢
        simp [hx, hy, hA, hB, mul_re, add_re]
      · dsimp only at hx hy hA hB ⊢
        simp [hx, hy, hA, hB, mul_im, add_im]

private theorem coordinateStep_natDegree_le
    (xVar yVar : Bivariate) (hx : xVar.natDegree ≤ 1)
    (hy : yVar.natDegree ≤ 1) (A B : Bivariate) (a : QI) (k : ℕ)
    (hA : A.natDegree ≤ k) (hB : B.natDegree ≤ k) :
    let result := coordinateStep xVar yVar (A, B) a
    result.1.natDegree ≤ k + 1 ∧ result.2.natDegree ≤ k + 1 := by
  have hAx : (A * xVar).natDegree ≤ k + 1 :=
    Polynomial.natDegree_mul_le.trans (add_le_add hA hx)
  have hAy : (A * yVar).natDegree ≤ k + 1 :=
    Polynomial.natDegree_mul_le.trans (add_le_add hA hy)
  have hBx : (B * xVar).natDegree ≤ k + 1 :=
    Polynomial.natDegree_mul_le.trans (add_le_add hB hx)
  have hBy : (B * yVar).natDegree ≤ k + 1 :=
    Polynomial.natDegree_mul_le.trans (add_le_add hB hy)
  have hreConstant :
      (Polynomial.C (Polynomial.C a.re) : Bivariate).natDegree ≤ k + 1 :=
    by simp
  have himConstant :
      (Polynomial.C (Polynomial.C a.im) : Bivariate).natDegree ≤ k + 1 :=
    by simp
  exact
    ⟨Polynomial.natDegree_add_le_of_degree_le
        ((Polynomial.natDegree_sub_le (A * xVar) (B * yVar)).trans
          (max_le hAx hBy)) hreConstant,
      Polynomial.natDegree_add_le_of_degree_le
        (Polynomial.natDegree_add_le_of_degree_le hAy hBx) himConstant⟩

private theorem coordinateFold_natDegree_le
    (xVar yVar : Bivariate) (hx : xVar.natDegree ≤ 1)
    (hy : yVar.natDegree ≤ 1) (cs : List QI)
    (A B : Bivariate) (k : ℕ) (hA : A.natDegree ≤ k)
    (hB : B.natDegree ≤ k) :
    let result := cs.foldl (coordinateStep xVar yVar) (A, B)
    result.1.natDegree ≤ k + cs.length ∧
      result.2.natDegree ≤ k + cs.length := by
  induction cs generalizing A B k with
  | nil => simpa using And.intro hA hB
  | cons a as ih =>
      simp only [List.foldl_cons, List.length_cons]
      have hstep := coordinateStep_natDegree_le xVar yVar hx hy A B a k hA hB
      have htail := ih
        (coordinateStep xVar yVar (A, B) a).1
        (coordinateStep xVar yVar (A, B) a).2 (k + 1) hstep.1 hstep.2
      constructor
      · exact htail.1.trans_eq (by omega)
      · exact htail.2.trans_eq (by omega)

private theorem verticalStep_high_coeff
    (A B : Bivariate) (a : QI) (k : ℕ)
    (hA : A.natDegree ≤ k) (hB : B.natDegree ≤ k) :
    let result := coordinateStep (Polynomial.C Polynomial.X) Polynomial.X (A, B) a
    result.1.coeff (k + 1) = -B.coeff k ∧
      result.2.coeff (k + 1) = A.coeff k := by
  have hAHigh : A.coeff (k + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by omega))
  have hBHigh : B.coeff (k + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by omega))
  constructor <;>
    simp [Polynomial.coeff_mul_C, Polynomial.coeff_mul_X,
      hAHigh, hBHigh]

private theorem horizontalStep_high_coeff
    (A B : Bivariate) (a : QI) (k : ℕ)
    (hA : A.natDegree ≤ k) (hB : B.natDegree ≤ k) :
    let result := coordinateStep Polynomial.X (Polynomial.C Polynomial.X) (A, B) a
    result.1.coeff (k + 1) = A.coeff k ∧
      result.2.coeff (k + 1) = B.coeff k := by
  have hAHigh : A.coeff (k + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by omega))
  have hBHigh : B.coeff (k + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by omega))
  constructor <;>
    simp [Polynomial.coeff_mul_C, Polynomial.coeff_mul_X,
      hAHigh, hBHigh]

private theorem verticalFold_high_nonzero
    (cs : List QI) (A B : Bivariate) (k : ℕ)
    (hA : A.natDegree ≤ k) (hB : B.natDegree ≤ k)
    (hhigh : A.coeff k ≠ 0 ∨ B.coeff k ≠ 0) :
    let result := cs.foldl
      (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X) (A, B)
    result.1.natDegree ≤ k + cs.length ∧
      result.2.natDegree ≤ k + cs.length ∧
      (result.1.coeff (k + cs.length) ≠ 0 ∨
        result.2.coeff (k + cs.length) ≠ 0) := by
  induction cs generalizing A B k with
  | nil => exact ⟨hA, hB, hhigh⟩
  | cons a as ih =>
      let step := coordinateStep
        (Polynomial.C Polynomial.X) Polynomial.X (A, B) a
      have hstepDegree := coordinateStep_natDegree_le
        (Polynomial.C Polynomial.X) Polynomial.X (by simp) (by simp)
        A B a k hA hB
      have hstepCoeff := verticalStep_high_coeff A B a k hA hB
      have hstepHigh : step.1.coeff (k + 1) ≠ 0 ∨
          step.2.coeff (k + 1) ≠ 0 := by
        rcases hhigh with hreal | himag
        · exact Or.inr (by rw [hstepCoeff.2]; exact hreal)
        · exact Or.inl (by rw [hstepCoeff.1]; exact neg_ne_zero.mpr himag)
      have htail := ih step.1 step.2 (k + 1)
        hstepDegree.1 hstepDegree.2 hstepHigh
      simpa only [List.foldl_cons, List.length_cons, step,
        show k + 1 + as.length = k + (as.length + 1) by omega] using htail

private theorem horizontalFold_high_nonzero
    (cs : List QI) (A B : Bivariate) (k : ℕ)
    (hA : A.natDegree ≤ k) (hB : B.natDegree ≤ k)
    (hhigh : A.coeff k ≠ 0 ∨ B.coeff k ≠ 0) :
    let result := cs.foldl
      (coordinateStep Polynomial.X (Polynomial.C Polynomial.X)) (A, B)
    result.1.natDegree ≤ k + cs.length ∧
      result.2.natDegree ≤ k + cs.length ∧
      (result.1.coeff (k + cs.length) ≠ 0 ∨
        result.2.coeff (k + cs.length) ≠ 0) := by
  induction cs generalizing A B k with
  | nil => exact ⟨hA, hB, hhigh⟩
  | cons a as ih =>
      let step := coordinateStep
        Polynomial.X (Polynomial.C Polynomial.X) (A, B) a
      have hstepDegree := coordinateStep_natDegree_le
        Polynomial.X (Polynomial.C Polynomial.X) (by simp) (by simp)
        A B a k hA hB
      have hstepCoeff := horizontalStep_high_coeff A B a k hA hB
      have hstepHigh : step.1.coeff (k + 1) ≠ 0 ∨
          step.2.coeff (k + 1) ≠ 0 := by
        rcases hhigh with hreal | himag
        · exact Or.inl (by rw [hstepCoeff.1]; exact hreal)
        · exact Or.inr (by rw [hstepCoeff.2]; exact himag)
      have htail := ih step.1 step.2 (k + 1)
        hstepDegree.1 hstepDegree.2 hstepHigh
      simpa only [List.foldl_cons, List.length_cons, step,
        show k + 1 + as.length = k + (as.length + 1) by omega] using htail

theorem coordinatePolynomials_natDegree_le
    (p : GaussianPolynomial) (hp : p.isZero = false)
    (xVar yVar : Bivariate) (hx : xVar.natDegree ≤ 1)
    (hy : yVar.natDegree ≤ 1) :
    (coordinatePolynomials p xVar yVar).1.natDegree ≤ p.natDegree ∧
      (coordinatePolynomials p xVar yVar).2.natDegree ≤ p.natDegree := by
  have hcoeffsNe : p.normalize.coeffs ≠ [] := by
    simpa [DensePolynomial.isZero] using hp
  cases hcoeffs : p.normalize.coeffs with
  | nil => exact (hcoeffsNe hcoeffs).elim
  | cons a as =>
      have htailLength : as.length = p.natDegree := by
        dsimp only [DensePolynomial.natDegree, DensePolynomial.degreeCount]
        rw [hcoeffs]
        simp
      have hinitial :
          (coordinateStep xVar yVar (0, 0) a).1.natDegree ≤ 0 ∧
            (coordinateStep xVar yVar (0, 0) a).2.natDegree ≤ 0 := by
        simp
      have htail := coordinateFold_natDegree_le xVar yVar hx hy as
        (coordinateStep xVar yVar (0, 0) a).1
        (coordinateStep xVar yVar (0, 0) a).2 0 hinitial.1 hinitial.2
      simp only [hcoeffs, List.foldl_cons]
      constructor
      · exact htail.1.trans_eq (by omega)
      · exact htail.2.trans_eq (by omega)

/-- `Y` is the main polynomial variable and `X` is the coefficient variable. -/
local notation "verticalCoordinates" =>
  fun (p : GaussianPolynomial) =>
    coordinatePolynomials p (Polynomial.C Polynomial.X) Polynomial.X

/-- `X` is the main polynomial variable and `Y` is the coefficient variable. -/
local notation "horizontalCoordinates" =>
  fun (p : GaussianPolynomial) =>
    coordinatePolynomials p Polynomial.X (Polynomial.C Polynomial.X)

theorem verticalCoordinates_natDegree_le
    (p : GaussianPolynomial) (hp : p.isZero = false) :
    (verticalCoordinates p).1.natDegree ≤ p.natDegree ∧
      (verticalCoordinates p).2.natDegree ≤ p.natDegree := by
  exact coordinatePolynomials_natDegree_le p hp _ _ (by simp) (by simp)

theorem horizontalCoordinates_natDegree_le
    (p : GaussianPolynomial) (hp : p.isZero = false) :
    (horizontalCoordinates p).1.natDegree ≤ p.natDegree ∧
      (horizontalCoordinates p).2.natDegree ≤ p.natDegree := by
  exact coordinatePolynomials_natDegree_le p hp _ _ (by simp) (by simp)

private theorem gaussian_coordinate_ne_zero {z : QI} (hz : z ≠ 0) :
    z.re ≠ 0 ∨ z.im ≠ 0 := by
  by_contra hcoordinates
  rw [not_or, not_ne_iff, not_ne_iff] at hcoordinates
  apply hz
  ext
  · exact hcoordinates.1
  · exact hcoordinates.2

private theorem initial_coordinate_high_nonzero
    (xVar yVar : Bivariate) {a : QI} (ha : a ≠ 0) :
    (coordinateStep xVar yVar (0, 0) a).1.coeff 0 ≠ 0 ∨
      (coordinateStep xVar yVar (0, 0) a).2.coeff 0 ≠ 0 := by
  simpa using gaussian_coordinate_ne_zero ha

theorem verticalCoordinates_dimension_pos
    (p : GaussianPolynomial) (hp : p.isZero = false)
    (hdegree : 0 < p.natDegree) :
    0 < (verticalCoordinates p).1.natDegree +
      (verticalCoordinates p).2.natDegree := by
  have hcoeffsNe : p.normalize.coeffs ≠ [] := by
    simpa [DensePolynomial.isZero] using hp
  cases hcoeffs : p.normalize.coeffs with
  | nil => exact (hcoeffsNe hcoeffs).elim
  | cons a as =>
      have ha : a ≠ 0 := by
        have hleading := DensePolynomial.leadingCoeff_ne_zero hp
        change p.normalize.coeffs.headD 0 ≠ 0 at hleading
        rw [hcoeffs] at hleading
        simpa using hleading
      have hinitialDegree :
          (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X
              (0, 0) a).1.natDegree ≤ 0 ∧
            (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X
              (0, 0) a).2.natDegree ≤ 0 := by
        simp
      have hfold := verticalFold_high_nonzero as
        (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X (0, 0) a).1
        (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X (0, 0) a).2
        0 hinitialDegree.1 hinitialDegree.2
        (initial_coordinate_high_nonzero _ _ ha)
      have htailLength : as.length = p.natDegree := by
        dsimp only [DensePolynomial.natDegree, DensePolynomial.degreeCount]
        rw [hcoeffs]
        simp
      have hcoordinates : verticalCoordinates p =
          as.foldl
            (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X)
            (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X
              (0, 0) a) := by
        simp only [hcoeffs, List.foldl_cons]
      have hfinal :
          (verticalCoordinates p).1.coeff p.natDegree ≠ 0 ∨
            (verticalCoordinates p).2.coeff p.natDegree ≠ 0 := by
        rw [hcoordinates]
        simpa [htailLength] using hfold.2.2
      rcases hfinal with hreal | himag
      · have hle := Polynomial.le_natDegree_of_ne_zero hreal
        omega
      · have hle := Polynomial.le_natDegree_of_ne_zero himag
        omega

theorem horizontalCoordinates_dimension_pos
    (p : GaussianPolynomial) (hp : p.isZero = false)
    (hdegree : 0 < p.natDegree) :
    0 < (horizontalCoordinates p).1.natDegree +
      (horizontalCoordinates p).2.natDegree := by
  have hcoeffsNe : p.normalize.coeffs ≠ [] := by
    simpa [DensePolynomial.isZero] using hp
  cases hcoeffs : p.normalize.coeffs with
  | nil => exact (hcoeffsNe hcoeffs).elim
  | cons a as =>
      have ha : a ≠ 0 := by
        have hleading := DensePolynomial.leadingCoeff_ne_zero hp
        change p.normalize.coeffs.headD 0 ≠ 0 at hleading
        rw [hcoeffs] at hleading
        simpa using hleading
      have hinitialDegree :
          (coordinateStep Polynomial.X (Polynomial.C Polynomial.X)
              (0, 0) a).1.natDegree ≤ 0 ∧
            (coordinateStep Polynomial.X (Polynomial.C Polynomial.X)
              (0, 0) a).2.natDegree ≤ 0 := by
        simp
      have hfold := horizontalFold_high_nonzero as
        (coordinateStep Polynomial.X (Polynomial.C Polynomial.X) (0, 0) a).1
        (coordinateStep Polynomial.X (Polynomial.C Polynomial.X) (0, 0) a).2
        0 hinitialDegree.1 hinitialDegree.2
        (initial_coordinate_high_nonzero _ _ ha)
      have htailLength : as.length = p.natDegree := by
        dsimp only [DensePolynomial.natDegree, DensePolynomial.degreeCount]
        rw [hcoeffs]
        simp
      have hcoordinates : horizontalCoordinates p =
          as.foldl
            (coordinateStep Polynomial.X (Polynomial.C Polynomial.X))
            (coordinateStep Polynomial.X (Polynomial.C Polynomial.X)
              (0, 0) a) := by
        simp only [hcoeffs, List.foldl_cons]
      have hfinal :
          (horizontalCoordinates p).1.coeff p.natDegree ≠ 0 ∨
            (horizontalCoordinates p).2.coeff p.natDegree ≠ 0 := by
        rw [hcoordinates]
        simpa [htailLength] using hfold.2.2
      rcases hfinal with hreal | himag
      · have hle := Polynomial.le_natDegree_of_ne_zero hreal
        omega
      · have hle := Polynomial.le_natDegree_of_ne_zero himag
        omega

/-! ## Swapping the two polynomial variables -/

/- The generic Mathlib bivariate-swap module is built around a
choice-dependent algebra-equivalence API and imports adjoining-root machinery.
For these rational coefficient polynomials, the required swap is the explicit
finite `eval₂` homomorphism below. -/
local notation "rationalConstants" =>
  (Polynomial.C.comp Polynomial.C : ℚ →+* Bivariate)

local notation "innerVariableToOuter" =>
  Polynomial.eval₂RingHom rationalConstants Polynomial.X

local notation "swapVariables" =>
  Polynomial.eval₂RingHom innerVariableToOuter (Polynomial.C Polynomial.X)

@[simp] private theorem swapVariables_X :
    swapVariables Polynomial.X = Polynomial.C Polynomial.X := by
  simp

@[simp] private theorem swapVariables_C_X :
    swapVariables (Polynomial.C Polynomial.X) = Polynomial.X := by
  simp

@[simp] private theorem swapVariables_C_C (r : ℚ) :
    swapVariables (Polynomial.C (Polynomial.C r)) =
      Polynomial.C (Polynomial.C r) := by
  simp

@[simp] private theorem swapVariables_monomial_monomial
    (n m : ℕ) (r : ℚ) :
    swapVariables (Polynomial.monomial n (Polynomial.monomial m r)) =
      Polynomial.monomial m (Polynomial.monomial n r) := by
  change Polynomial.eval₂ innerVariableToOuter (Polynomial.C Polynomial.X)
      (Polynomial.monomial n (Polynomial.monomial m r)) = _
  rw [Polynomial.eval₂_monomial]
  change Polynomial.eval₂ rationalConstants Polynomial.X
      (Polynomial.monomial m r) * Polynomial.C Polynomial.X ^ n = _
  rw [Polynomial.eval₂_monomial]
  simp [← map_pow, Polynomial.C_mul_X_pow_eq_monomial]

local notation "swapPair" =>
  fun (state : Bivariate × Bivariate) =>
    (swapVariables state.1, swapVariables state.2)

private theorem swapPair_verticalStep (state : Bivariate × Bivariate) (a : QI) :
    swapPair (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X state a) =
      coordinateStep Polynomial.X (Polynomial.C Polynomial.X)
        (swapPair state) a := by
  ext <;> simp

private theorem swapPair_verticalFold (cs : List QI)
    (state : Bivariate × Bivariate) :
    swapPair (cs.foldl
      (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X) state) =
      cs.foldl (coordinateStep Polynomial.X (Polynomial.C Polynomial.X))
        (swapPair state) := by
  induction cs generalizing state with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      calc
        swapPair (as.foldl
            (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X)
            (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X state a)) =
          as.foldl (coordinateStep Polynomial.X (Polynomial.C Polynomial.X))
            (swapPair
              (coordinateStep (Polynomial.C Polynomial.X) Polynomial.X state a)) :=
                ih _
        _ = as.foldl (coordinateStep Polynomial.X (Polynomial.C Polynomial.X))
            (coordinateStep Polynomial.X (Polynomial.C Polynomial.X)
              (swapPair state) a) := by rw [swapPair_verticalStep]

theorem swapPair_verticalCoordinates (p : GaussianPolynomial) :
    swapPair (verticalCoordinates p) = horizontalCoordinates p := by
  have h := swapPair_verticalFold p.normalize.coeffs (0, 0)
  simpa using h

theorem coeff_coeff_swap (q : Bivariate) (i j : ℕ) :
    ((swapVariables q).coeff j).coeff i =
      (q.coeff i).coeff j := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      simp only [Polynomial.coeff_add, hp, hq]
  | monomial n a =>
      induction a using Polynomial.induction_on' with
      | add p q hp hq =>
          rw [map_add (Polynomial.monomial n) p q, map_add]
          simp only [Polynomial.coeff_add, hp, hq]
      | monomial m r =>
          rw [swapVariables_monomial_monomial]
          simp only [Polynomial.coeff_monomial]
          split_ifs <;> simp_all [Polynomial.coeff_monomial]

theorem swapPair_horizontalCoordinates (p : GaussianPolynomial) :
    swapPair (horizontalCoordinates p) = verticalCoordinates p := by
  have h := swapPair_verticalCoordinates p
  have hinvolutive (q : Bivariate) : swapVariables (swapVariables q) = q := by
    ext i j
    rw [coeff_coeff_swap, coeff_coeff_swap]
  apply Prod.ext
  · have hfirst := congrArg (fun q : Bivariate => swapVariables q)
      (congrArg Prod.fst h)
    rw [hinvolutive] at hfirst
    exact hfirst.symm
  · have hsecond := congrArg (fun q : Bivariate => swapVariables q)
      (congrArg Prod.snd h)
    rw [hinvolutive] at hsecond
    exact hsecond.symm

theorem coeff_natDegree_le_swap_natDegree (q : Bivariate) (i : ℕ) :
    (q.coeff i).natDegree ≤ (swapVariables q).natDegree := by
  by_cases hcoeff : q.coeff i = 0
  · simp [hcoeff]
  · have hleading :
        (q.coeff i).coeff (q.coeff i).natDegree ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hcoeff
    rw [← coeff_coeff_swap] at hleading
    apply Polynomial.le_natDegree_of_ne_zero
    intro houter
    rw [houter] at hleading
    exact hleading (by simp)

theorem verticalCoordinates_coefficient_natDegree_le
    (p : GaussianPolynomial) (hp : p.isZero = false) (i : ℕ) :
    ((verticalCoordinates p).1.coeff i).natDegree ≤ p.natDegree ∧
      ((verticalCoordinates p).2.coeff i).natDegree ≤ p.natDegree := by
  have hdegree := horizontalCoordinates_natDegree_le p hp
  have hswap := swapPair_verticalCoordinates p
  have hswapReal : swapVariables (verticalCoordinates p).1 =
      (horizontalCoordinates p).1 := congrArg Prod.fst hswap
  have hswapImag : swapVariables (verticalCoordinates p).2 =
      (horizontalCoordinates p).2 := congrArg Prod.snd hswap
  constructor
  · exact (coeff_natDegree_le_swap_natDegree (verticalCoordinates p).1 i).trans
      (by rw [hswapReal]; exact hdegree.1)
  · exact (coeff_natDegree_le_swap_natDegree (verticalCoordinates p).2 i).trans
      (by rw [hswapImag]; exact hdegree.2)

theorem horizontalCoordinates_coefficient_natDegree_le
    (p : GaussianPolynomial) (hp : p.isZero = false) (i : ℕ) :
    ((horizontalCoordinates p).1.coeff i).natDegree ≤ p.natDegree ∧
      ((horizontalCoordinates p).2.coeff i).natDegree ≤ p.natDegree := by
  have hdegree := verticalCoordinates_natDegree_le p hp
  have hswap := swapPair_horizontalCoordinates p
  have hswapReal : swapVariables (horizontalCoordinates p).1 =
      (verticalCoordinates p).1 := congrArg Prod.fst hswap
  have hswapImag : swapVariables (horizontalCoordinates p).2 =
      (verticalCoordinates p).2 := congrArg Prod.snd hswap
  constructor
  · exact (coeff_natDegree_le_swap_natDegree (horizontalCoordinates p).1 i).trans
      (by rw [hswapReal]; exact hdegree.1)
  · exact (coeff_natDegree_le_swap_natDegree (horizontalCoordinates p).2 i).trans
      (by rw [hswapImag]; exact hdegree.2)

/-! ## Sylvester degree bounds -/

theorem natDegree_det_le
    {n d : ℕ} (M : Matrix (Fin n) (Fin n) (Polynomial ℚ))
    (hentry : ∀ i j, (M i j).natDegree ≤ d) :
    M.det.natDegree ≤ n * d := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro permutation _
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le
    (s := Finset.univ)
    (f := fun i : Fin n => M (permutation i) i)).trans ?_
  calc
    ∑ i : Fin n, (M (permutation i) i).natDegree ≤ ∑ _i : Fin n, d := by
      exact Finset.sum_le_sum fun i _ => hentry (permutation i) i
    _ = n * d := by simp

theorem natDegree_resultant_le_of_coefficients
    (f g : Bivariate) (m n d : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ d)
    (hg : ∀ i, (g.coeff i).natDegree ≤ d) :
    (f.resultant g m n).natDegree ≤ (m + n) * d := by
  unfold Polynomial.resultant
  apply natDegree_det_le
  intro i j
  induction j using Fin.addCases with
  | left j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hg _
      · simp
  | right j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hf _
      · simp

theorem eval_verticalCoordinates (p : GaussianPolynomial) (x y : ℚ) :
    bivariateEval (verticalCoordinates p).1 x y =
        (p.eval (GaussianRat.mk x y)).re ∧
      bivariateEval (verticalCoordinates p).2 x y =
        (p.eval (GaussianRat.mk x y)).im := by
  rw [← eval_normalize p (GaussianRat.mk x y)]
  have h := eval_coordinateFold_from
    (Polynomial.C Polynomial.X) Polynomial.X x y x y
    (by simp) (by simp) p.normalize.coeffs 0 0 0
    (by simp) (by simp)
  simpa only [DensePolynomial.eval, DensePolynomial.evalCoeffs,
    zero_re, zero_im] using h

theorem eval_horizontalCoordinates (p : GaussianPolynomial) (x y : ℚ) :
    bivariateEval (horizontalCoordinates p).1 y x =
        (p.eval (GaussianRat.mk x y)).re ∧
      bivariateEval (horizontalCoordinates p).2 y x =
        (p.eval (GaussianRat.mk x y)).im := by
  rw [← eval_normalize p (GaussianRat.mk x y)]
  have h := eval_coordinateFold_from
    Polynomial.X (Polynomial.C Polynomial.X) y x x y
    (by simp) (by simp) p.normalize.coeffs 0 0 0
    (by simp) (by simp)
  simpa only [DensePolynomial.eval, DensePolynomial.evalCoeffs,
    zero_re, zero_im] using h

/-- Specialize the coefficient variable of a bivariate polynomial. -/
local notation "specializeCoefficient" =>
  fun (q : Bivariate) (c : ℚ) => q.map (Polynomial.evalRingHom c)

@[simp] theorem eval_specializeCoefficient (q : Bivariate) (c t : ℚ) :
    (specializeCoefficient q c).eval t = bivariateEval q c t := rfl

local notation "verticalRealSpecialization" =>
  fun (p : GaussianPolynomial) (x : ℚ) =>
    specializeCoefficient (verticalCoordinates p).1 x

local notation "verticalImagSpecialization" =>
  fun (p : GaussianPolynomial) (x : ℚ) =>
    specializeCoefficient (verticalCoordinates p).2 x

local notation "horizontalRealSpecialization" =>
  fun (p : GaussianPolynomial) (y : ℚ) =>
    specializeCoefficient (horizontalCoordinates p).1 y

local notation "horizontalImagSpecialization" =>
  fun (p : GaussianPolynomial) (y : ℚ) =>
    specializeCoefficient (horizontalCoordinates p).2 y

theorem verticalRealSpecialization_eq (p : GaussianPolynomial) (x : ℚ) :
    verticalRealSpecialization p x = (verticalPathReal p x).toPolynomial := by
  apply rationalPolynomial_eq_of_eval_eq_on_fin
  intro i
  let y : ℚ := ((i : ℕ) : ℚ)
  rw [eval_toPolynomial]
  change bivariateEval (verticalCoordinates p).1 x y =
    (verticalPathReal p x).eval y
  rw [verticalPathReal, eval_pathReal, line_vertical]
  exact (eval_verticalCoordinates p x y).1

theorem verticalImagSpecialization_eq (p : GaussianPolynomial) (x : ℚ) :
    verticalImagSpecialization p x = (verticalPathImag p x).toPolynomial := by
  apply rationalPolynomial_eq_of_eval_eq_on_fin
  intro i
  let y : ℚ := ((i : ℕ) : ℚ)
  rw [eval_toPolynomial]
  change bivariateEval (verticalCoordinates p).2 x y =
    (verticalPathImag p x).eval y
  rw [verticalPathImag, eval_pathImag, line_vertical]
  exact (eval_verticalCoordinates p x y).2

theorem horizontalRealSpecialization_eq (p : GaussianPolynomial) (y : ℚ) :
    horizontalRealSpecialization p y = (horizontalPathReal p y).toPolynomial := by
  apply rationalPolynomial_eq_of_eval_eq_on_fin
  intro i
  let x : ℚ := ((i : ℕ) : ℚ)
  rw [eval_toPolynomial]
  change bivariateEval (horizontalCoordinates p).1 y x =
    (horizontalPathReal p y).eval x
  rw [horizontalPathReal, eval_pathReal, line_horizontal]
  exact (eval_horizontalCoordinates p x y).1

theorem horizontalImagSpecialization_eq (p : GaussianPolynomial) (y : ℚ) :
    horizontalImagSpecialization p y = (horizontalPathImag p y).toPolynomial := by
  apply rationalPolynomial_eq_of_eval_eq_on_fin
  intro i
  let x : ℚ := ((i : ℕ) : ℚ)
  rw [eval_toPolynomial]
  change bivariateEval (horizontalCoordinates p).2 y x =
    (horizontalPathImag p y).eval x
  rw [horizontalPathImag, eval_pathImag, line_horizontal]
  exact (eval_horizontalCoordinates p x y).2

/-! ## Sylvester determinants and specialization -/

/-- `R_x(X)`: eliminate the main variable `Y` from the vertical orientation. -/
local notation "verticalResultant" =>
  fun (p : GaussianPolynomial) =>
    (verticalCoordinates p).1.resultant (verticalCoordinates p).2
      (verticalCoordinates p).1.natDegree (verticalCoordinates p).2.natDegree

/-- `R_y(Y)`: eliminate the main variable `X` from the horizontal orientation. -/
local notation "horizontalResultant" =>
  fun (p : GaussianPolynomial) =>
    (horizontalCoordinates p).1.resultant (horizontalCoordinates p).2
      (horizontalCoordinates p).1.natDegree (horizontalCoordinates p).2.natDegree

theorem verticalResultant_natDegree_le
    (p : GaussianPolynomial) (hp : p.isZero = false) :
    (verticalResultant p).natDegree ≤ 2 * p.natDegree ^ 2 := by
  have hmain := verticalCoordinates_natDegree_le p hp
  have hresultant := natDegree_resultant_le_of_coefficients
    (verticalCoordinates p).1 (verticalCoordinates p).2
    (verticalCoordinates p).1.natDegree
    (verticalCoordinates p).2.natDegree p.natDegree
    (fun i => (verticalCoordinates_coefficient_natDegree_le p hp i).1)
    (fun i => (verticalCoordinates_coefficient_natDegree_le p hp i).2)
  change (verticalResultant p).natDegree ≤ 2 * p.natDegree ^ 2
  calc
    (verticalResultant p).natDegree ≤
        ((verticalCoordinates p).1.natDegree +
          (verticalCoordinates p).2.natDegree) * p.natDegree := hresultant
    _ ≤ (2 * p.natDegree) * p.natDegree :=
      Nat.mul_le_mul_right _ (by omega)
    _ = 2 * p.natDegree ^ 2 := by ring

theorem horizontalResultant_natDegree_le
    (p : GaussianPolynomial) (hp : p.isZero = false) :
    (horizontalResultant p).natDegree ≤ 2 * p.natDegree ^ 2 := by
  have hmain := horizontalCoordinates_natDegree_le p hp
  have hresultant := natDegree_resultant_le_of_coefficients
    (horizontalCoordinates p).1 (horizontalCoordinates p).2
    (horizontalCoordinates p).1.natDegree
    (horizontalCoordinates p).2.natDegree p.natDegree
    (fun i => (horizontalCoordinates_coefficient_natDegree_le p hp i).1)
    (fun i => (horizontalCoordinates_coefficient_natDegree_le p hp i).2)
  change (horizontalResultant p).natDegree ≤ 2 * p.natDegree ^ 2
  calc
    (horizontalResultant p).natDegree ≤
        ((horizontalCoordinates p).1.natDegree +
          (horizontalCoordinates p).2.natDegree) * p.natDegree := hresultant
    _ ≤ (2 * p.natDegree) * p.natDegree :=
      Nat.mul_le_mul_right _ (by omega)
    _ = 2 * p.natDegree ^ 2 := by ring

theorem eval_verticalResultant (p : GaussianPolynomial) (x : ℚ) :
    (verticalResultant p).eval x =
      (verticalRealSpecialization p x).resultant
        (verticalImagSpecialization p x)
        (verticalCoordinates p).1.natDegree
        (verticalCoordinates p).2.natDegree := by
  have hmap := Polynomial.resultant_map_map
    (f := (verticalCoordinates p).1) (g := (verticalCoordinates p).2)
    (m := (verticalCoordinates p).1.natDegree)
    (n := (verticalCoordinates p).2.natDegree)
    (Polynomial.evalRingHom x)
  exact hmap.symm

theorem eval_horizontalResultant (p : GaussianPolynomial) (y : ℚ) :
    (horizontalResultant p).eval y =
      (horizontalRealSpecialization p y).resultant
        (horizontalImagSpecialization p y)
        (horizontalCoordinates p).1.natDegree
        (horizontalCoordinates p).2.natDegree := by
  have hmap := Polynomial.resultant_map_map
    (f := (horizontalCoordinates p).1) (g := (horizontalCoordinates p).2)
    (m := (horizontalCoordinates p).1.natDegree)
    (n := (horizontalCoordinates p).2.natDegree)
    (Polynomial.evalRingHom y)
  exact hmap.symm

theorem pair_ne_zero_of_explicit_resultant_ne_zero
    {f g : Polynomial ℚ} {m n : ℕ} (hdimension : 0 < m + n)
    (hresultant : f.resultant g m n ≠ 0) : f ≠ 0 ∨ g ≠ 0 := by
  by_contra hzero
  rw [not_or, not_ne_iff, not_ne_iff] at hzero
  apply hresultant
  rw [hzero.1, hzero.2, Polynomial.resultant_zero_zero,
    zero_pow (Nat.ne_of_gt hdimension)]

/-- A nonzero explicitly sized Sylvester determinant implies ordinary
coprimality whenever the displayed sizes bound the actual degrees and the
matrix has positive dimension. -/
theorem isCoprime_of_explicit_resultant_ne_zero
    {f g : Polynomial ℚ} {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hdimension : 0 < m + n) (hresultant : f.resultant g m n ≠ 0) :
    IsCoprime f g := by
  have hdimension' : m ≠ 0 ∨ n ≠ 0 := by
    omega
  obtain ⟨a, b, _ha, _hb, hbezout⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant
      f g hf hg hdimension'
  refine ⟨Polynomial.C (f.resultant g m n)⁻¹ * a,
    Polynomial.C (f.resultant g m n)⁻¹ * b, ?_⟩
  calc
    (Polynomial.C (f.resultant g m n)⁻¹ * a) * f +
        (Polynomial.C (f.resultant g m n)⁻¹ * b) * g =
      Polynomial.C (f.resultant g m n)⁻¹ * (f * a + g * b) := by ring
    _ = Polynomial.C (f.resultant g m n)⁻¹ *
        Polynomial.C (f.resultant g m n) := by rw [hbezout]
    _ = 1 := by
      rw [← Polynomial.C_mul]
      simp [hresultant]

theorem verticalSpecialization_isCoprime
    (p : GaussianPolynomial)
    (hdimension : 0 < (verticalCoordinates p).1.natDegree +
      (verticalCoordinates p).2.natDegree)
    {x : ℚ} (hresultant : (verticalResultant p).eval x ≠ 0) :
    IsCoprime (verticalPathReal p x).toPolynomial
      (verticalPathImag p x).toPolynomial := by
  have hsized :
      (verticalRealSpecialization p x).resultant
        (verticalImagSpecialization p x)
        (verticalCoordinates p).1.natDegree
        (verticalCoordinates p).2.natDegree ≠ 0 := by
    rwa [eval_verticalResultant] at hresultant
  have hcoprime := isCoprime_of_explicit_resultant_ne_zero
    (Polynomial.natDegree_map_le.trans le_rfl)
    (Polynomial.natDegree_map_le.trans le_rfl) hdimension hsized
  change IsCoprime (verticalRealSpecialization p x)
    (verticalImagSpecialization p x) at hcoprime
  rwa [verticalRealSpecialization_eq, verticalImagSpecialization_eq] at hcoprime

theorem horizontalSpecialization_isCoprime
    (p : GaussianPolynomial)
    (hdimension : 0 < (horizontalCoordinates p).1.natDegree +
      (horizontalCoordinates p).2.natDegree)
    {y : ℚ} (hresultant : (horizontalResultant p).eval y ≠ 0) :
    IsCoprime (horizontalPathReal p y).toPolynomial
      (horizontalPathImag p y).toPolynomial := by
  have hsized :
      (horizontalRealSpecialization p y).resultant
        (horizontalImagSpecialization p y)
        (horizontalCoordinates p).1.natDegree
        (horizontalCoordinates p).2.natDegree ≠ 0 := by
    rwa [eval_horizontalResultant] at hresultant
  have hcoprime := isCoprime_of_explicit_resultant_ne_zero
    (Polynomial.natDegree_map_le.trans le_rfl)
    (Polynomial.natDegree_map_le.trans le_rfl) hdimension hsized
  change IsCoprime (horizontalRealSpecialization p y)
    (horizontalImagSpecialization p y) at hcoprime
  rwa [horizontalRealSpecialization_eq, horizontalImagSpecialization_eq] at hcoprime

def verticalSpecializationCertificate
    (p : GaussianPolynomial)
    (hdimension : 0 < (verticalCoordinates p).1.natDegree +
      (verticalCoordinates p).2.natDegree)
    (x : ℚ) (hresultant : (verticalResultant p).eval x ≠ 0) :
    FTA.DenseSquarefree.CoprimeCertificate
      (verticalPathReal p x) (verticalPathImag p x) :=
  FTA.DenseSquarefree.certificateOfIsCoprimeNonzero _ _
    (by
      have hsized :
          (verticalRealSpecialization p x).resultant
            (verticalImagSpecialization p x)
            (verticalCoordinates p).1.natDegree
            (verticalCoordinates p).2.natDegree ≠ 0 := by
        rwa [eval_verticalResultant] at hresultant
      rcases pair_ne_zero_of_explicit_resultant_ne_zero hdimension hsized with
        hreal | himag
      · exact Or.inl (FTA.CauchyProduct.isZero_false_of_toPolynomial_ne_zero
          (verticalRealSpecialization_eq p x ▸ hreal))
      · exact Or.inr (FTA.CauchyProduct.isZero_false_of_toPolynomial_ne_zero
          (verticalImagSpecialization_eq p x ▸ himag)))
    (verticalSpecialization_isCoprime p hdimension hresultant)

def horizontalSpecializationCertificate
    (p : GaussianPolynomial)
    (hdimension : 0 < (horizontalCoordinates p).1.natDegree +
      (horizontalCoordinates p).2.natDegree)
    (y : ℚ) (hresultant : (horizontalResultant p).eval y ≠ 0) :
    FTA.DenseSquarefree.CoprimeCertificate
      (horizontalPathReal p y) (horizontalPathImag p y) :=
  FTA.DenseSquarefree.certificateOfIsCoprimeNonzero _ _
    (by
      have hsized :
          (horizontalRealSpecialization p y).resultant
            (horizontalImagSpecialization p y)
            (horizontalCoordinates p).1.natDegree
            (horizontalCoordinates p).2.natDegree ≠ 0 := by
        rwa [eval_horizontalResultant] at hresultant
      rcases pair_ne_zero_of_explicit_resultant_ne_zero hdimension hsized with
        hreal | himag
      · exact Or.inl (FTA.CauchyProduct.isZero_false_of_toPolynomial_ne_zero
          (horizontalRealSpecialization_eq p y ▸ hreal))
      · exact Or.inr (FTA.CauchyProduct.isZero_false_of_toPolynomial_ne_zero
          (horizontalImagSpecialization_eq p y ▸ himag)))
    (horizontalSpecialization_isCoprime p hdimension hresultant)

/-! ## Dense eliminant bridge -/

/-- A dense executable representation of the two specification-level
Sylvester determinants, with the global facts needed by bounded search.  The
next construction supplies these fields from the finite determinant program
and proves the paper's `2d²` bounds. -/
structure DenseAxisResultants (p : GaussianPolynomial) where
  vertical : RatPolynomial
  horizontal : RatPolynomial
  vertical_spec : vertical.toPolynomial = verticalResultant p
  horizontal_spec : horizontal.toPolynomial = horizontalResultant p
  vertical_nonzero : verticalResultant p ≠ 0
  horizontal_nonzero : horizontalResultant p ≠ 0

/-- Convert actual dense Sylvester outputs into the exact interface consumed
by the four Newton-band searches. -/
def DenseAxisResultants.toEliminationCertificate
    {p : GaussianPolynomial} (resultants : DenseAxisResultants p)
    (hp : p.isZero = false) (hdegree : 0 < p.natDegree) :
    AxisEliminationCertificate p (2 * p.natDegree ^ 2) where
  vertical := resultants.vertical
  horizontal := resultants.horizontal
  vertical_nonzero := by
    rw [resultants.vertical_spec]
    exact resultants.vertical_nonzero
  horizontal_nonzero := by
    rw [resultants.horizontal_spec]
    exact resultants.horizontal_nonzero
  vertical_degree := by
    rw [resultants.vertical_spec]
    exact verticalResultant_natDegree_le p hp
  horizontal_degree := by
    rw [resultants.horizontal_spec]
    exact horizontalResultant_natDegree_le p hp
  vertical_coprime := by
    intro x hx
    apply verticalSpecializationCertificate p
      (verticalCoordinates_dimension_pos p hp hdegree) x
    rw [← resultants.vertical_spec, eval_toPolynomial]
    exact hx
  horizontal_coprime := by
    intro y hy
    apply horizontalSpecializationCertificate p
      (horizontalCoordinates_dimension_pos p hp hdegree) y
    rw [← resultants.horizontal_spec, eval_toPolynomial]
    exact hy

end

end FTA.AxisResultant
