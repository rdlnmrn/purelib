import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructiveGaussian
import mathlib.RFAP.ComputablePolynomial

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

namespace RFAP.ConstructiveFiniteNorm

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Gaussian

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial

def coordinateSum : List Coordinate → Coordinate
  | [] => 0
  | value :: values => value + coordinateSum values

def coordinateSquareSum : List Coordinate → Coordinate
  | [] => 0
  | value :: values => value ^ 2 + coordinateSquareSum values

def squareDistanceSum (value : Coordinate) : List Coordinate → Coordinate
  | [] => 0
  | other :: others =>
      (value - other) ^ 2 + squareDistanceSum value others

def pairSquareDistanceSum : List Coordinate → Coordinate
  | [] => 0
  | value :: values =>
      squareDistanceSum value values + pairSquareDistanceSum values

theorem coordinateSquareSum_nonneg (values : List Coordinate) :
    0 ≤ coordinateSquareSum values := by
  induction values with
  | nil => exact le_rfl
  | cons value values inductionHypothesis =>
      exact add_nonneg
        (RFAP.ConstructiveFraction.sq_nonneg_direct value)
        inductionHypothesis

theorem squareDistanceSum_nonneg (value : Coordinate)
    (values : List Coordinate) :
    0 ≤ squareDistanceSum value values := by
  induction values with
  | nil => exact le_rfl
  | cons other others inductionHypothesis =>
      exact add_nonneg
        (RFAP.ConstructiveFraction.sq_nonneg_direct (value - other))
        inductionHypothesis

theorem pairSquareDistanceSum_nonneg (values : List Coordinate) :
    0 ≤ pairSquareDistanceSum values := by
  induction values with
  | nil => exact le_rfl
  | cons value values inductionHypothesis =>
      exact add_nonneg (squareDistanceSum_nonneg value values)
        inductionHypothesis

theorem squareDistanceSum_eq (value : Coordinate) :
    ∀ values : List Coordinate,
      squareDistanceSum value values =
        (values.length : Coordinate) * value ^ 2 -
          2 * value * coordinateSum values + coordinateSquareSum values
  | [] => by
      change (0 : Coordinate) = 0 * value ^ 2 - 2 * value * 0 + 0
      ring1
  | other :: others => by
      rw [squareDistanceSum, squareDistanceSum_eq value others,
        coordinateSum, coordinateSquareSum]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring1

/-- Exact finite sum-of-square-differences identity. -/
theorem sum_sq_identity : ∀ values : List Coordinate,
    (values.length : Coordinate) * coordinateSquareSum values -
        coordinateSum values ^ 2 =
      pairSquareDistanceSum values
  | [] => by
      change (0 : Coordinate) * 0 - 0 ^ 2 = 0
      ring1
  | value :: values => by
      rw [coordinateSquareSum, coordinateSum, pairSquareDistanceSum,
        squareDistanceSum_eq value values, ← sum_sq_identity values]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring1

/-- Finite scalar Cauchy--Schwarz, with the list length as the explicit
cardinality witness. -/
theorem coordinateSum_sq_le (values : List Coordinate) :
    coordinateSum values ^ 2 ≤
      (values.length : Coordinate) * coordinateSquareSum values := by
  apply sub_nonneg.mp
  rw [sum_sq_identity]
  exact pairSquareDistanceSum_nonneg values

def gaussianSum : List Gaussian → Gaussian
  | [] => 0
  | value :: values => value + gaussianSum values

def gaussianNormSqSum : List Gaussian → Coordinate
  | [] => 0
  | value :: values => normSq value + gaussianNormSqSum values

@[simp] theorem gaussianSum_re : ∀ values : List Gaussian,
    (gaussianSum values).re = coordinateSum (values.map (fun z => z.re))
  | [] => rfl
  | value :: values => by
      rw [gaussianSum, add_re, gaussianSum_re, List.map_cons, coordinateSum]

@[simp] theorem gaussianSum_im : ∀ values : List Gaussian,
    (gaussianSum values).im = coordinateSum (values.map (fun z => z.im))
  | [] => rfl
  | value :: values => by
      rw [gaussianSum, add_im, gaussianSum_im, List.map_cons, coordinateSum]

theorem gaussianNormSqSum_coordinates : ∀ values : List Gaussian,
    gaussianNormSqSum values =
      coordinateSquareSum (values.map (fun z => z.re)) +
        coordinateSquareSum (values.map (fun z => z.im))
  | [] => by
      change (0 : Coordinate) = 0 + 0
      ring1
  | value :: values => by
      rw [gaussianNormSqSum, gaussianNormSqSum_coordinates]
      simp only [List.map_cons, coordinateSquareSum]
      change value.re ^ 2 + value.im ^ 2 +
          (coordinateSquareSum (values.map fun z => z.re) +
            coordinateSquareSum (values.map fun z => z.im)) = _
      ring1

/-- Finite Gaussian Cauchy--Schwarz for a displayed list. -/
theorem normSq_gaussianSum_le (values : List Gaussian) :
    normSq (gaussianSum values) ≤
      (values.length : Coordinate) * gaussianNormSqSum values := by
  have realBound := coordinateSum_sq_le (values.map fun z => z.re)
  have imaginaryBound := coordinateSum_sq_le (values.map fun z => z.im)
  simp only [List.length_map] at realBound imaginaryBound
  change
    (gaussianSum values).re ^ 2 + (gaussianSum values).im ^ 2 ≤ _
  rw [gaussianSum_re, gaussianSum_im,
    gaussianNormSqSum_coordinates]
  calc
    coordinateSum (values.map fun z => z.re) ^ 2 +
          coordinateSum (values.map fun z => z.im) ^ 2 ≤
        (values.length : Coordinate) *
            coordinateSquareSum (values.map fun z => z.re) +
          (values.length : Coordinate) *
            coordinateSquareSum (values.map fun z => z.im) :=
      add_le_add realBound imaginaryBound
    _ = (values.length : Coordinate) *
        (coordinateSquareSum (values.map fun z => z.re) +
          coordinateSquareSum (values.map fun z => z.im)) := by ring1

/-! ## Finite monomial lists -/

/-- The displayed monomials of one high-to-low coefficient list. -/
def monomialTerms : List Gaussian → Gaussian → List Gaussian
  | [], _ => []
  | coefficient :: coefficients, z =>
      coefficient * z ^ coefficients.length :: monomialTerms coefficients z

@[simp] theorem monomialTerms_length (coefficients : List Gaussian)
    (z : Gaussian) :
    (monomialTerms coefficients z).length = coefficients.length := by
  induction coefficients with
  | nil => rfl
  | cons coefficient coefficients inductionHypothesis =>
      rw [monomialTerms, List.length_cons, inductionHypothesis,
        List.length_cons]

/-- Structural monomial expansion of the finite Horner program. -/
theorem gaussianSum_monomialTerms :
    ∀ (coefficients : List Gaussian) (z : Gaussian),
      gaussianSum (monomialTerms coefficients z) =
        evalCoeffs z coefficients
  | [], _ => rfl
  | coefficient :: coefficients, z => by
      rw [monomialTerms, gaussianSum,
        gaussianSum_monomialTerms coefficients z,
        evalCoeffs_cons_expansion]

/-- Sum of the squared norms of the displayed monomials. -/
def monomialNormSqSum : List Gaussian → Coordinate → Coordinate
  | [], _ => 0
  | coefficient :: coefficients, radiusSq =>
      normSq coefficient * radiusSq ^ coefficients.length +
        monomialNormSqSum coefficients radiusSq

theorem gaussianNormSqSum_monomialTerms :
    ∀ (coefficients : List Gaussian) (z : Gaussian),
      gaussianNormSqSum (monomialTerms coefficients z) =
        monomialNormSqSum coefficients (normSq z)
  | [], _ => rfl
  | coefficient :: coefficients, z => by
      rw [monomialTerms, gaussianNormSqSum,
        gaussianNormSqSum_monomialTerms coefficients z,
        monomialNormSqSum, normSq_mul, normSq_pow]

/-- Cauchy--Schwarz specialized to the finite Horner monomial expansion. -/
theorem normSq_evalCoeffs_le (coefficients : List Gaussian) (z : Gaussian) :
    normSq (evalCoeffs z coefficients) ≤
      (coefficients.length : Coordinate) *
        monomialNormSqSum coefficients (normSq z) := by
  rw [← gaussianSum_monomialTerms coefficients z,
    ← gaussianNormSqSum_monomialTerms coefficients z,
    ← monomialTerms_length coefficients z]
  exact normSq_gaussianSum_le (monomialTerms coefficients z)

end RFAP.ConstructiveFiniteNorm
