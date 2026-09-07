import CCL.Riemann.AlgebraicDifferentials

/-!
# The finite odd-degree chart at infinity

For an odd-degree hyperelliptic equation `y^2 = f(x)`, put

`x = t⁻²` and `Y = t^degree * y`.

Then `Y^2` is the finite even polynomial

`F(t) = t^(2 * degree) * f(t⁻²)`.

This file constructs `F` directly from the normalized finite coefficient
list.  In particular, `F(0)` is the leading coefficient of `f`, so the
apparent endpoint at infinity becomes an ordinary nonzero square-root
problem.  The evaluation identity is proved by induction over that finite
list; no completed projective curve or limiting point is used.
-/

namespace CCL.Riemann.HyperellipticInfinity

open CCL.Riemann.AlgebraicDifferentials

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev ChartPolynomial := CCL.FiniteGaussianPolynomial.Polynomial

/-- Insert one zero after every coefficient.  Since the source list is
high-to-low and the chart polynomial is low-to-high, this sends
`[a_d, ..., a_0]` to the coefficients of
`a_d + a_(d-1)t^2 + ... + a_0 t^(2d)` (with one harmless final zero). -/
def evenCoefficients : List Gaussian -> List Gaussian
  | [] => []
  | coefficient :: remaining =>
      coefficient :: 0 :: evenCoefficients remaining

/-- Direct finite Horner evaluation in the squared chart parameter. -/
def evenHorner (squareParameter : Gaussian) : List Gaussian -> Gaussian
  | [] => 0
  | coefficient :: remaining =>
      coefficient + squareParameter * evenHorner squareParameter remaining

@[simp] theorem evenHorner_nil (squareParameter : Gaussian) :
    evenHorner squareParameter [] = 0 := rfl

@[simp] theorem evenHorner_cons (squareParameter coefficient : Gaussian)
    (remaining : List Gaussian) :
    evenHorner squareParameter (coefficient :: remaining) =
      coefficient + squareParameter *
        evenHorner squareParameter remaining := rfl

/-- The low-to-high polynomial evaluator computes exactly the displayed
finite even Horner recursion. -/
theorem evalCoeffs_evenCoefficients (parameter : Gaussian) :
    forall coefficients : List Gaussian,
      CCL.FiniteGaussianPolynomial.evalCoeffs
          (evenCoefficients coefficients) parameter =
        evenHorner (parameter ^ 2) coefficients
  | [] => rfl
  | coefficient :: remaining => by
      simp only [evenCoefficients, CCL.FiniteGaussianPolynomial.evalCoeffs,
        List.foldr_cons]
      change coefficient + parameter *
          (0 + parameter *
            CCL.FiniteGaussianPolynomial.evalCoeffs
              (evenCoefficients remaining) parameter) =
        coefficient + parameter ^ 2 *
          evenHorner (parameter ^ 2) remaining
      rw [evalCoeffs_evenCoefficients parameter remaining]
      ring1

/-- The executable chart radicand obtained from the normalized affine
coefficient list. -/
def chartPolynomial (polynomial : GaussianPolynomial) : ChartPolynomial :=
  ⟨evenCoefficients polynomial.normalize.coeffs⟩

theorem chartPolynomial_eval (polynomial : GaussianPolynomial)
    (parameter : Gaussian) :
    CCL.FiniteGaussianPolynomial.eval (chartPolynomial polynomial) parameter =
      evenHorner (parameter ^ 2) polynomial.normalize.coeffs := by
  exact evalCoeffs_evenCoefficients parameter polynomial.normalize.coeffs

/-- At the chart origin the transformed radicand is the affine leading
coefficient. -/
theorem evenHorner_zero : forall coefficients : List Gaussian,
    evenHorner 0 coefficients = coefficients.headD 0
  | [] => rfl
  | coefficient :: remaining => by
      simp only [evenHorner, List.headD_cons, zero_mul, add_zero]

theorem chartPolynomial_eval_zero (polynomial : GaussianPolynomial) :
    CCL.FiniteGaussianPolynomial.eval (chartPolynomial polynomial) 0 =
      polynomial.leadingCoeff := by
  rw [chartPolynomial_eval]
  change evenHorner 0 polynomial.normalize.coeffs = _
  rw [evenHorner_zero]
  rfl

theorem chartPolynomial_eval_zero_ne {polynomial : GaussianPolynomial}
    (nonzero : polynomial.isZero = false) :
    CCL.FiniteGaussianPolynomial.eval (chartPolynomial polynomial) 0 ≠ 0 := by
  rw [chartPolynomial_eval_zero]
  exact RFAP.ComputablePolynomial.DensePolynomial.leadingCoeff_ne_zero nonzero

/-- The chart radicand attached to a hyperelliptic curve. -/
def curveRadicand {genus : Nat} (curve : HyperellipticCurve genus) :
    ChartPolynomial :=
  chartPolynomial curve.polynomial

theorem curveRadicand_origin {genus : Nat}
    (curve : HyperellipticCurve genus) :
    CCL.FiniteGaussianPolynomial.eval (curveRadicand curve) 0 =
      curve.polynomial.leadingCoeff :=
  chartPolynomial_eval_zero curve.polynomial

theorem curveRadicand_origin_ne {genus : Nat}
    (curve : HyperellipticCurve genus) :
    CCL.FiniteGaussianPolynomial.eval (curveRadicand curve) 0 ≠ 0 :=
  chartPolynomial_eval_zero_ne curve.nonzero

/-- Either square-root sheet of the transformed nonzero radicand at the
chart origin is immediately available to the finite root machinery. -/
def originSquareRoot {genus : Nat} (curve : HyperellipticCurve genus)
    (sheet : Fin 2) : CCL.Riemann.SquareRootSheets.Sheet
      (CCL.FiniteGaussianPolynomial.eval (curveRadicand curve) 0) :=
  CCL.Riemann.SquareRootSheets.sheet
    (curveRadicand_origin_ne curve) sheet

/-- Homogenized finite-list identity.  The hypothesis `affine * chart = 1`
is the only reciprocal fact needed by the induction.  Keeping it explicit
also makes the theorem useful independently of the particular substitution
`affine = (t^2)⁻¹`. -/
theorem homogenized_evalCoeffs (affine chart : Gaussian)
    (cancel : affine * chart = 1) :
    forall coefficients : List Gaussian,
      chart ^ coefficients.length *
          RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
            affine coefficients =
        chart * evenHorner chart coefficients
  | [] => by
      simp only [List.length_nil, pow_zero,
        RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs_nil,
        evenHorner_nil, mul_zero]
  | coefficient :: remaining => by
      rw [RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs_cons_expansion]
      simp only [List.length_cons, pow_succ, evenHorner_cons]
      rw [mul_add]
      have poweredCancel :
          affine ^ remaining.length * chart ^ remaining.length = 1 := by
        rw [← mul_pow, cancel, one_pow]
      have leadingTerm :
          (chart ^ remaining.length * chart) *
              (coefficient * affine ^ remaining.length) =
            chart * coefficient := by
        calc
          (chart ^ remaining.length * chart) *
                (coefficient * affine ^ remaining.length) =
              chart * coefficient *
                (affine ^ remaining.length * chart ^ remaining.length) := by
                  ring1
          _ = chart * coefficient := by rw [poweredCancel, mul_one]
      rw [leadingTerm]
      have inductionIdentity :=
        homogenized_evalCoeffs affine chart cancel remaining
      calc
        chart * coefficient +
              chart ^ remaining.length * chart *
                RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
                  affine remaining =
            chart * coefficient + chart *
              (chart ^ remaining.length *
                RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
                  affine remaining) := by ring1
        _ = chart * coefficient + chart *
              (chart * evenHorner chart remaining) := by
                rw [inductionIdentity]
        _ = chart *
              (coefficient + chart * evenHorner chart remaining) := by
                ring1

/-- Exact affine-to-chart equation away from the chart origin. -/
theorem chartPolynomial_affine_identity {polynomial : GaussianPolynomial}
    (nonzero : polynomial.isZero = false)
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0) :
    CCL.FiniteGaussianPolynomial.eval (chartPolynomial polynomial) parameter =
      (parameter ^ 2) ^ polynomial.natDegree *
        polynomial.eval ((parameter ^ 2)⁻¹) := by
  let chart := parameter ^ 2
  have chartNonzero : chart ≠ 0 :=
    RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct
      parameter parameterNonzero 2
  have cancel : chart⁻¹ * chart = 1 :=
    RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel chart chartNonzero
  have homogenized := homogenized_evalCoeffs chart⁻¹ chart cancel
    polynomial.normalize.coeffs
  have normalizedEval :
      RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs chart⁻¹
          polynomial.normalize.coeffs = polynomial.eval chart⁻¹ := by
    change polynomial.normalize.eval chart⁻¹ = polynomial.eval chart⁻¹
    exact RFAP.ComputablePolynomial.DensePolynomial.eval_normalize
      polynomial chart⁻¹
  have chartValue :
      CCL.FiniteGaussianPolynomial.eval (chartPolynomial polynomial)
          parameter = evenHorner chart polynomial.normalize.coeffs := by
    change CCL.FiniteGaussianPolynomial.eval (chartPolynomial polynomial)
        parameter = evenHorner (parameter ^ 2) polynomial.normalize.coeffs
    exact chartPolynomial_eval polynomial parameter
  have coefficientCount :
      polynomial.normalize.coeffs.length = polynomial.natDegree + 1 := by
    exact
      (RFAP.ComputablePolynomial.DensePolynomial.natDegree_add_one_eq_degreeCount
        nonzero).symm
  rw [chartValue, ← normalizedEval]
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne chartNonzero
  calc
    evenHorner chart polynomial.normalize.coeffs * chart =
        chart * evenHorner chart polynomial.normalize.coeffs := by ring1
    _ = chart ^ polynomial.normalize.coeffs.length *
          RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
            chart⁻¹ polynomial.normalize.coeffs := homogenized.symm
    _ = (chart ^ polynomial.natDegree *
          RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
            chart⁻¹ polynomial.normalize.coeffs) * chart := by
      rw [coefficientCount, pow_succ]
      ring1

/-- In the odd-degree case the exponent in the affine identity is exactly
the displayed degree `2g+1`. -/
theorem curveRadicand_affine_identity {genus : Nat}
    (curve : HyperellipticCurve genus)
    (oddDegree : curve.polynomial.natDegree = 2 * genus + 1)
    (parameter : Gaussian) (parameterNonzero : parameter ≠ 0) :
    CCL.FiniteGaussianPolynomial.eval (curveRadicand curve) parameter =
      (parameter ^ 2) ^ (2 * genus + 1) *
        curve.polynomial.eval ((parameter ^ 2)⁻¹) := by
  rw [curveRadicand, chartPolynomial_affine_identity curve.nonzero
    parameter parameterNonzero, oddDegree]

/-- Exact transformed curve equation.  If `(x,y)` satisfies the affine
equation at `x=t⁻²`, then `Y=t^(2g+1)y` satisfies the finite chart equation.
-/
theorem scaled_curve_equation {genus : Nat}
    (curve : HyperellipticCurve genus)
    (oddDegree : curve.polynomial.natDegree = 2 * genus + 1)
    (parameter y : Gaussian) (parameterNonzero : parameter ≠ 0)
    (affineEquation : y ^ 2 =
      curve.polynomial.eval ((parameter ^ 2)⁻¹)) :
    (parameter ^ (2 * genus + 1) * y) ^ 2 =
      CCL.FiniteGaussianPolynomial.eval (curveRadicand curve) parameter := by
  rw [curveRadicand_affine_identity curve oddDegree parameter
    parameterNonzero, mul_pow, affineEquation]
  congr 1
  rw [← pow_mul, ← pow_mul]
  congr 1
  omega0

/-- The nonnegative exponent of the regularized odd-degree differential
`-2 t^(2g-2k-2) dt/Y`, for the zero-based basis index `k < g`. -/
def differentialExponent {genus : Nat}
    (differential : Differential genus) : Nat :=
  2 * (genus - differential.index.val - 1)

theorem differentialExponent_eq {genus : Nat}
    (differential : Differential genus) :
    differentialExponent differential =
      2 * genus - 2 * differential.index.val - 2 := by
  unfold differentialExponent
  have bound := differential.index.isLt
  omega0

end CCL.Riemann.HyperellipticInfinity
