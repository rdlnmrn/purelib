import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructivePolynomial

/-!
# Constructive polynomial images of affine paths

Finite Horner substitution turns a two-coordinate Gaussian polynomial on
`origin + t · direction` into two dense constructive-coordinate polynomials.
All semantics are proved directly from the folds; no evaluation-extensionality
principle is used.
-/

namespace RFAP.PathPolynomial

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial

/-- Embed one constructive coordinate on the real axis. -/
def ofCoordinate (t : Coordinate) : Gaussian := ⟨t, 0⟩

@[simp] theorem ofCoordinate_re (t : Coordinate) : (ofCoordinate t).re = t := rfl
@[simp] theorem ofCoordinate_im (t : Coordinate) : (ofCoordinate t).im = 0 := rfl

/-- Affine parameterization `origin + t · direction`. -/
def line (origin direction : Gaussian) (t : Coordinate) : Gaussian :=
  origin + ofCoordinate t * direction

/-- Multiply a polynomial in the parameter by the affine line expression. -/
def mulLine (origin direction : Gaussian) (p : GaussianPolynomial) :
    GaussianPolynomial :=
  scale origin p + shift 1 (scale direction p)

@[simp] theorem mulLine_zero (origin direction : Gaussian) :
    mulLine origin direction (0 : GaussianPolynomial) = 0 := by
  rw [mulLine, scale_zero_right, scale_zero_right, shift_zero,
    zero_add_normalize, normalize_zero]

@[simp] theorem eval_mulLine (origin direction : Gaussian)
    (p : GaussianPolynomial) (t : Coordinate) :
    (mulLine origin direction p).eval (ofCoordinate t) =
      p.eval (ofCoordinate t) * line origin direction t := by
  rw [mulLine, eval_add, eval_scale, eval_shift, eval_scale]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [line, add_re, add_im, mul_re, mul_im, ofCoordinate_re,
      ofCoordinate_im, pow_one] <;>
    ring1

@[simp] theorem eval_mulLineGaussian (origin direction : Gaussian)
    (p : GaussianPolynomial) (z : Gaussian) :
    (mulLine origin direction p).eval z =
      p.eval z * (origin + z * direction) := by
  rw [mulLine, eval_add, eval_scale, eval_shift, eval_scale]
  change origin * p.eval z + direction * p.eval z * z ^ 1 = _
  ring1

def composeLineCoeffs (origin direction : Gaussian)
    (coefficients : List Gaussian) : GaussianPolynomial :=
  coefficients.foldl
    (fun accumulator coefficient =>
      mulLine origin direction accumulator + constant coefficient) 0

private theorem composeLineCoeffs_dropWhile_zero
    (origin direction : Gaussian) (coefficients : List Gaussian) :
    composeLineCoeffs origin direction (coefficients.dropWhile (· = 0)) =
      composeLineCoeffs origin direction coefficients := by
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      by_cases coefficientZero : coefficient = 0
      · subst coefficient
        rw [List.dropWhile_cons_of_pos (by simp)]
        rw [inductionHypothesis]
        unfold composeLineCoeffs
        simp only [List.foldl_cons]
        rw [mulLine_zero, zero_add_normalize, normalize_constant_zero]
      · rw [List.dropWhile_cons_of_neg (by simpa using coefficientZero)]

private theorem eval_composeLineCoeffs_from
    (origin direction : Gaussian) (t : Coordinate)
    (coefficients : List Gaussian) (accumulator : GaussianPolynomial) :
    (coefficients.foldl
      (fun value coefficient =>
        mulLine origin direction value + constant coefficient)
      accumulator).eval (ofCoordinate t) =
    coefficients.foldl
      (fun value coefficient => value * line origin direction t + coefficient)
      (accumulator.eval (ofCoordinate t)) := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient coefficients ih =>
      simp only [List.foldl_cons]
      rw [ih, eval_add, eval_mulLine, eval_constant]

/-- Executable affine substitution. -/
def composeLine (p : GaussianPolynomial) (origin direction : Gaussian) :
    GaussianPolynomial :=
  composeLineCoeffs origin direction p.coeffs

/-- Affine substitution ignores only the finite prefix of representation
zeros removed by normalization. -/
@[simp] theorem composeLine_normalize (p : GaussianPolynomial)
    (origin direction : Gaussian) :
    composeLine p.normalize origin direction = composeLine p origin direction := by
  unfold composeLine
  exact composeLineCoeffs_dropWhile_zero origin direction p.coeffs

theorem eval_composeLine (p : GaussianPolynomial) (origin direction : Gaussian)
    (t : Coordinate) :
    (composeLine p origin direction).eval (ofCoordinate t) =
      p.eval (line origin direction t) := by
  rw [composeLine, composeLineCoeffs, eval_composeLineCoeffs_from]
  rfl

private theorem eval_composeLineCoeffsGaussian_from
    (origin direction z : Gaussian) (coefficients : List Gaussian)
    (accumulator : GaussianPolynomial) :
    (coefficients.foldl
      (fun value coefficient =>
        mulLine origin direction value + constant coefficient)
      accumulator).eval z =
    coefficients.foldl
      (fun value coefficient =>
        value * (origin + z * direction) + coefficient)
      (accumulator.eval z) := by
  induction coefficients generalizing accumulator with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [inductionHypothesis, eval_add, eval_mulLineGaussian, eval_constant]

/-- Affine substitution semantics at an arbitrary Gaussian argument. -/
theorem eval_composeLineGaussian (p : GaussianPolynomial)
    (origin direction z : Gaussian) :
    (composeLine p origin direction).eval z =
      p.eval (origin + z * direction) := by
  rw [composeLine, composeLineCoeffs,
    eval_composeLineCoeffsGaussian_from]
  rfl

/-- Real coordinate coefficient list. -/
def realPart (p : GaussianPolynomial) : CoordinatePolynomial :=
  ⟨p.coeffs.map (fun z => z.re)⟩

/-- Imaginary coordinate coefficient list. -/
def imagPart (p : GaussianPolynomial) : CoordinatePolynomial :=
  ⟨p.coeffs.map (fun z => z.im)⟩

private theorem foldl_map_re (t : Coordinate) (coefficients : List Gaussian)
    (r : Coordinate) (z : Gaussian) (hrz : r = z.re) :
    (coefficients.map (fun z => z.re)).foldl
        (fun value coefficient => value * t + coefficient) r =
      (coefficients.foldl
        (fun value coefficient => value * ofCoordinate t + coefficient) z).re := by
  induction coefficients generalizing r z with
  | nil => exact hrz
  | cons coefficient coefficients ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      simp only [mul_re, ofCoordinate_re, ofCoordinate_im, add_re]
      rw [hrz]
      ring1

private theorem foldl_map_im (t : Coordinate) (coefficients : List Gaussian)
    (r : Coordinate) (z : Gaussian) (hrz : r = z.im) :
    (coefficients.map (fun z => z.im)).foldl
        (fun value coefficient => value * t + coefficient) r =
      (coefficients.foldl
        (fun value coefficient => value * ofCoordinate t + coefficient) z).im := by
  induction coefficients generalizing r z with
  | nil => exact hrz
  | cons coefficient coefficients ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      simp only [mul_im, ofCoordinate_re, ofCoordinate_im, add_im]
      rw [hrz]
      ring1

@[simp] theorem eval_realPart (p : GaussianPolynomial) (t : Coordinate) :
    (realPart p).eval t = (p.eval (ofCoordinate t)).re := by
  dsimp only [realPart, eval, evalCoeffs]
  exact foldl_map_re t p.coeffs 0 0 rfl

@[simp] theorem eval_imagPart (p : GaussianPolynomial) (t : Coordinate) :
    (imagPart p).eval t = (p.eval (ofCoordinate t)).im := by
  dsimp only [imagPart, eval, evalCoeffs]
  exact foldl_map_im t p.coeffs 0 0 rfl

def pathReal (p : GaussianPolynomial) (origin direction : Gaussian) :
    CoordinatePolynomial :=
  realPart (composeLine p origin direction)

def pathImag (p : GaussianPolynomial) (origin direction : Gaussian) :
    CoordinatePolynomial :=
  imagPart (composeLine p origin direction)

@[simp] theorem pathReal_normalize (p : GaussianPolynomial)
    (origin direction : Gaussian) :
    pathReal p.normalize origin direction = pathReal p origin direction := by
  change realPart (composeLine p.normalize origin direction) =
    realPart (composeLine p origin direction)
  rw [composeLine_normalize]

@[simp] theorem pathImag_normalize (p : GaussianPolynomial)
    (origin direction : Gaussian) :
    pathImag p.normalize origin direction = pathImag p origin direction := by
  change imagPart (composeLine p.normalize origin direction) =
    imagPart (composeLine p origin direction)
  rw [composeLine_normalize]

theorem eval_pathReal (p : GaussianPolynomial) (origin direction : Gaussian)
    (t : Coordinate) :
    (pathReal p origin direction).eval t =
      (p.eval (line origin direction t)).re := by
  rw [pathReal, eval_realPart, eval_composeLine]

theorem eval_pathImag (p : GaussianPolynomial) (origin direction : Gaussian)
    (t : Coordinate) :
    (pathImag p origin direction).eval t =
      (p.eval (line origin direction t)).im := by
  rw [pathImag, eval_imagPart, eval_composeLine]

/-- Real coordinate of a pointwise product of two paths. -/
def productReal (A B C D : CoordinatePolynomial) : CoordinatePolynomial :=
  A * C - B * D

/-- Imaginary coordinate of a pointwise product of two paths. -/
def productImag (A B C D : CoordinatePolynomial) : CoordinatePolynomial :=
  A * D + B * C

@[simp] theorem eval_productReal (A B C D : CoordinatePolynomial)
    (t : Coordinate) :
    (productReal A B C D).eval t =
      A.eval t * C.eval t - B.eval t * D.eval t := by
  simp only [productReal, eval_sub, eval_mul]

@[simp] theorem eval_productImag (A B C D : CoordinatePolynomial)
    (t : Coordinate) :
    (productImag A B C D).eval t =
      A.eval t * D.eval t + B.eval t * C.eval t := by
  simp only [productImag, eval_add, eval_mul]

theorem eval_pathReal_mul (p q : GaussianPolynomial)
    (origin direction : Gaussian) (t : Coordinate) :
    (pathReal (p * q) origin direction).eval t =
      (productReal (pathReal p origin direction) (pathImag p origin direction)
        (pathReal q origin direction) (pathImag q origin direction)).eval t := by
  rw [eval_pathReal, eval_productReal, eval_pathReal, eval_pathImag,
    eval_pathReal, eval_pathImag, eval_mul]
  rfl

theorem eval_pathImag_mul (p q : GaussianPolynomial)
    (origin direction : Gaussian) (t : Coordinate) :
    (pathImag (p * q) origin direction).eval t =
      (productImag (pathReal p origin direction) (pathImag p origin direction)
        (pathReal q origin direction) (pathImag q origin direction)).eval t := by
  rw [eval_pathImag, eval_productImag, eval_pathReal, eval_pathImag,
    eval_pathReal, eval_pathImag, eval_mul]
  rfl

end RFAP.PathPolynomial
