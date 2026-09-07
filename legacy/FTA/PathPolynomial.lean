import CCL.Gaussian
import FTA.DensePolynomialBridge

/-!
# Polynomial images of rational affine paths

This module supplies the exact bridge used in Definition 4.1.  Given a dense
Gaussian-rational polynomial `p` and a rational affine path `u + t d`, it
computes a dense Gaussian-rational polynomial in `t`, then extracts rational
real and imaginary coordinate polynomials.  All three evaluation identities
are proved directly from finite Horner folds.
-/

namespace FTA.PathPolynomial

open CCL CCL.GaussianRat
open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI
abbrev RatPolynomial := DensePolynomial ℚ

/-- The coordinate embedding `ℚ → ℚ(i)`, kept transparent for evaluation proofs. -/
def ofRat (t : ℚ) : QI where
  re := t
  im := 0

@[simp] theorem ofRat_re (t : ℚ) : (ofRat t).re = t := rfl
@[simp] theorem ofRat_im (t : ℚ) : (ofRat t).im = 0 := rfl

/-- The affine parameterization `u + t d`. -/
def line (u d : QI) (t : ℚ) : QI := u + ofRat t * d

/-- Multiply a polynomial in `t` by the affine expression `u + t d`. -/
def mulLine (u d : QI) (p : GaussianPolynomial) : GaussianPolynomial :=
  scale u p + shift 1 (scale d p)

@[simp] theorem eval_mulLine (u d : QI) (p : GaussianPolynomial) (t : ℚ) :
    (mulLine u d p).eval (ofRat t) = p.eval (ofRat t) * line u d t := by
  rw [mulLine, eval_add, eval_scale, eval_shift, eval_scale]
  simp only [line]
  ring

/-- Horner substitution of `u + t d` into a finite coefficient list. -/
def composeLineCoeffs (u d : QI) (cs : List QI) : GaussianPolynomial :=
  cs.foldl (fun acc a => mulLine u d acc + constant a) 0

private theorem eval_composeLineCoeffs_from (u d : QI) (t : ℚ) (cs : List QI)
    (acc : GaussianPolynomial) :
    (cs.foldl (fun value a => mulLine u d value + constant a) acc).eval (ofRat t) =
      cs.foldl (fun value a => value * line u d t + a) (acc.eval (ofRat t)) := by
  induction cs generalizing acc with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      rw [ih, eval_add, eval_mulLine, eval_constant]

/-- Executable affine substitution for a dense Gaussian-rational polynomial. -/
def composeLine (p : GaussianPolynomial) (u d : QI) : GaussianPolynomial :=
  composeLineCoeffs u d p.coeffs

/-- Exact semantics of the affine-substitution program. -/
theorem eval_composeLine (p : GaussianPolynomial) (u d : QI) (t : ℚ) :
    (composeLine p u d).eval (ofRat t) = p.eval (line u d t) := by
  rw [composeLine, composeLineCoeffs, eval_composeLineCoeffs_from]
  rfl

/-- Rational polynomial formed from the real parts of finite coefficients. -/
def realPart (p : GaussianPolynomial) : RatPolynomial :=
  ⟨p.coeffs.map GaussianRat.re⟩

/-- Rational polynomial formed from the imaginary parts of finite coefficients. -/
def imagPart (p : GaussianPolynomial) : RatPolynomial :=
  ⟨p.coeffs.map GaussianRat.im⟩

private theorem foldl_map_re (t : ℚ) (cs : List QI) (r : ℚ) (z : QI)
    (hrz : r = z.re) :
    (cs.map GaussianRat.re).foldl (fun value a => value * t + a) r =
      (cs.foldl (fun value a => value * ofRat t + a) z).re := by
  induction cs generalizing r z with
  | nil => exact hrz
  | cons a as ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      simp only [mul_re, ofRat_re, ofRat_im, add_re]
      rw [hrz]
      ring

private theorem foldl_map_im (t : ℚ) (cs : List QI) (r : ℚ) (z : QI)
    (hrz : r = z.im) :
    (cs.map GaussianRat.im).foldl (fun value a => value * t + a) r =
      (cs.foldl (fun value a => value * ofRat t + a) z).im := by
  induction cs generalizing r z with
  | nil => exact hrz
  | cons a as ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      simp only [mul_im, ofRat_re, ofRat_im, add_im]
      rw [hrz]
      ring

/-- Coordinate extraction commutes with exact Horner evaluation. -/
@[simp] theorem eval_realPart (p : GaussianPolynomial) (t : ℚ) :
    (realPart p).eval t = (p.eval (ofRat t)).re := by
  dsimp only [realPart, DensePolynomial.eval, DensePolynomial.evalCoeffs]
  exact foldl_map_re t p.coeffs 0 0 rfl

/-- Coordinate extraction commutes with exact Horner evaluation. -/
@[simp] theorem eval_imagPart (p : GaussianPolynomial) (t : ℚ) :
    (imagPart p).eval t = (p.eval (ofRat t)).im := by
  dsimp only [imagPart, DensePolynomial.eval, DensePolynomial.evalCoeffs]
  exact foldl_map_im t p.coeffs 0 0 rfl

/-- Real coordinate polynomial of `p(u + t d)`. -/
def pathReal (p : GaussianPolynomial) (u d : QI) : RatPolynomial :=
  realPart (composeLine p u d)

/-- Imaginary coordinate polynomial of `p(u + t d)`. -/
def pathImag (p : GaussianPolynomial) (u d : QI) : RatPolynomial :=
  imagPart (composeLine p u d)

theorem eval_pathReal (p : GaussianPolynomial) (u d : QI) (t : ℚ) :
    (pathReal p u d).eval t = (p.eval (line u d t)).re := by
  rw [pathReal, eval_realPart, eval_composeLine]

theorem eval_pathImag (p : GaussianPolynomial) (u d : QI) (t : ℚ) :
    (pathImag p u d).eval t = (p.eval (line u d t)).im := by
  rw [pathImag, eval_imagPart, eval_composeLine]

/-! ## Products along one affine path -/

/-- Real coordinate of the product of two rational-coordinate paths. -/
def productReal (A B C D : RatPolynomial) : RatPolynomial :=
  A * C - B * D

/-- Imaginary coordinate of the product of two rational-coordinate paths. -/
def productImag (A B C D : RatPolynomial) : RatPolynomial :=
  A * D + B * C

@[simp] theorem eval_productReal (A B C D : RatPolynomial) (t : ℚ) :
    (productReal A B C D).eval t =
      A.eval t * C.eval t - B.eval t * D.eval t := by
  simp [productReal]

@[simp] theorem eval_productImag (A B C D : RatPolynomial) (t : ℚ) :
    (productImag A B C D).eval t =
      A.eval t * D.eval t + B.eval t * C.eval t := by
  simp [productImag]

/-- Exact real-coordinate product identity for two Gaussian-rational
polynomials evaluated on the same affine path. -/
theorem eval_pathReal_mul (p q : GaussianPolynomial) (u d : QI) (t : ℚ) :
    (pathReal (p * q) u d).eval t =
      (productReal (pathReal p u d) (pathImag p u d)
        (pathReal q u d) (pathImag q u d)).eval t := by
  rw [eval_pathReal, eval_productReal, eval_pathReal, eval_pathImag,
    eval_pathReal, eval_pathImag, eval_mul]
  rfl

/-- Exact imaginary-coordinate product identity on the same path. -/
theorem eval_pathImag_mul (p q : GaussianPolynomial) (u d : QI) (t : ℚ) :
    (pathImag (p * q) u d).eval t =
      (productImag (pathReal p u d) (pathImag p u d)
        (pathReal q u d) (pathImag q u d)).eval t := by
  rw [eval_pathImag, eval_productImag, eval_pathReal, eval_pathImag,
    eval_pathReal, eval_pathImag, eval_mul]
  rfl

/-- Sparse specification form, used by resultant and Sturm proofs without
depending on a particular dense coefficient normalization. -/
theorem toPolynomial_pathReal_mul (p q : GaussianPolynomial) (u d : QI) :
    (pathReal (p * q) u d).toPolynomial =
      (productReal (pathReal p u d) (pathImag p u d)
        (pathReal q u d) (pathImag q u d)).toPolynomial := by
  apply rationalPolynomial_eq_of_eval_eq_on_fin
  intro i
  rw [eval_toPolynomial, eval_toPolynomial]
  exact eval_pathReal_mul p q u d ((i : ℕ) : ℚ)

theorem toPolynomial_pathImag_mul (p q : GaussianPolynomial) (u d : QI) :
    (pathImag (p * q) u d).toPolynomial =
      (productImag (pathReal p u d) (pathImag p u d)
        (pathReal q u d) (pathImag q u d)).toPolynomial := by
  apply rationalPolynomial_eq_of_eval_eq_on_fin
  intro i
  rw [eval_toPolynomial, eval_toPolynomial]
  exact eval_pathImag_mul p q u d ((i : ℕ) : ℚ)

/-- Native coefficient-path regression: squaring `Z` on the real line gives
real value four and imaginary value zero at parameter two. -/
theorem pathProduct_quadratic_example :
    (pathReal ((⟨[1, 0]⟩ : GaussianPolynomial) * ⟨[1, 0]⟩) 0 1).eval 2 = 4 ∧
      (pathImag ((⟨[1, 0]⟩ : GaussianPolynomial) * ⟨[1, 0]⟩) 0 1).eval 2 = 0 := by
  native_decide

end FTA.PathPolynomial
