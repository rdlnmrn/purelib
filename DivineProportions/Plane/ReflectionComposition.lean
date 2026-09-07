import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Plane.LineReflection

/-!
# Divine Proportions, Theorem 16: composition of reflections

Nested affine formulas obscure the polynomial core of the reflection theorem.
This file uses a finite homogeneous coordinate triple only as a displayed
record—there is no projective quotient.  Reflection is a polynomial map on
that triple.  The conjugation identity is then a direct ring calculation, and
explicit nonzero products justify returning to the affine chart.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

@[ext]
structure HomogeneousPoint (K : Type*) where
  x : K
  y : K
  z : K

def HomogeneousPoint.ofPoint (point : Point K) : HomogeneousPoint K :=
  ⟨point.x, point.y, 1⟩

def HomogeneousPoint.affineChart (point : HomogeneousPoint K) : Point K :=
  ⟨point.x / point.z, point.y / point.z⟩

def HomogeneousPoint.scale (factor : K) (point : HomogeneousPoint K) :
    HomogeneousPoint K :=
  ⟨factor * point.x, factor * point.y, factor * point.z⟩

/-- Polynomial homogeneous action corresponding to reflection in `line`. -/
def reflectHomogeneous (line : Line K) (point : HomogeneousPoint K) :
    HomogeneousPoint K :=
  ⟨(line.b ^ 2 - line.a ^ 2) * point.x -
      2 * line.a * line.b * point.y - 2 * line.a * line.c * point.z,
    -2 * line.a * line.b * point.x +
      (line.a ^ 2 - line.b ^ 2) * point.y - 2 * line.b * line.c * point.z,
    lineNorm line * point.z⟩

private theorem rightInverse_unique {value candidate : K}
    (valueNonzero : value ≠ 0) (candidateRightInverse : value * candidate = 1) :
    value⁻¹ = candidate := by
  have canonicalRightInverse : value * value⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel value valueNonzero
  calc
    value⁻¹ = value⁻¹ * 1 := by rw [mul_one]
    _ = value⁻¹ * (value * candidate) := by rw [candidateRightInverse]
    _ = (value * value⁻¹) * candidate := by ring1
    _ = candidate := by rw [canonicalRightInverse]; exact one_mul candidate

private theorem inverse_mul {left right : K}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    (left * right)⁻¹ = right⁻¹ * left⁻¹ := by
  apply rightInverse_unique
  · exact RFAP.ExplicitField.mul_ne_zero leftNonzero rightNonzero
  · have leftCancel : left * left⁻¹ = (1 : K) :=
      RFAP.ExplicitField.mul_inv_cancel left leftNonzero
    have rightCancel : right * right⁻¹ = (1 : K) :=
      RFAP.ExplicitField.mul_inv_cancel right rightNonzero
    calc
      left * right * (right⁻¹ * left⁻¹) =
          (left * left⁻¹) * (right * right⁻¹) := by ring1
      _ = 1 := by rw [leftCancel, rightCancel, one_mul]

theorem HomogeneousPoint.affineChart_ofPoint [Nontrivial K] (point : Point K) :
    (HomogeneousPoint.ofPoint point).affineChart = point := by
  have oneInverse : (1 : K)⁻¹ = 1 := by
    apply rightInverse_unique one_ne_zero
    exact mul_one 1
  apply Point.ext
  · change point.x / (1 : K) = point.x
    rw [RFAP.ExplicitField.div_eq_mul_inv, oneInverse, mul_one]
  · change point.y / (1 : K) = point.y
    rw [RFAP.ExplicitField.div_eq_mul_inv, oneInverse, mul_one]

/-- The affine chart is invariant under a displayed nonzero homogeneous
scaling. -/
theorem HomogeneousPoint.affineChart_scale
    (factor : K) (point : HomogeneousPoint K)
    (factorNonzero : factor ≠ 0) (zNonzero : point.z ≠ 0) :
    (point.scale factor).affineChart = point.affineChart := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  have productInverse := inverse_mul factorNonzero zNonzero
  apply Point.ext
  · change (factor * point.x) / (factor * point.z) = point.x / point.z
    simp only [RFAP.ExplicitField.div_eq_mul_inv, productInverse]
    calc
      factor * point.x * (point.z⁻¹ * factor⁻¹) =
          (factor * factor⁻¹) * (point.x * point.z⁻¹) := by ring1
      _ = point.x * point.z⁻¹ := by rw [factorCancel, one_mul]
  · change (factor * point.y) / (factor * point.z) = point.y / point.z
    simp only [RFAP.ExplicitField.div_eq_mul_inv, productInverse]
    calc
      factor * point.y * (point.z⁻¹ * factor⁻¹) =
          (factor * factor⁻¹) * (point.y * point.z⁻¹) := by ring1
      _ = point.y * point.z⁻¹ := by rw [factorCancel, one_mul]

/-- Reflecting a displayed homogeneous triple and then taking its affine chart
is the same as applying the affine reflection formula to its chart. -/
theorem affineChart_reflectHomogeneous (line : Line K)
    (lineNonNull : ¬ line.IsNull) (point : HomogeneousPoint K)
    (zNonzero : point.z ≠ 0) :
    (reflectHomogeneous line point).affineChart =
      reflectionFormula line point.affineChart := by
  have normNonzero : lineNorm line ≠ 0 := lineNonNull
  have zCancel : point.z * point.z⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel point.z zNonzero
  have productInverse := inverse_mul normNonzero zNonzero
  apply Point.ext
  · change
      ((line.b ^ 2 - line.a ^ 2) * point.x -
          2 * line.a * line.b * point.y - 2 * line.a * line.c * point.z) /
          (lineNorm line * point.z) =
        ((line.b ^ 2 - line.a ^ 2) * (point.x / point.z) -
          2 * line.a * line.b * (point.y / point.z) -
          2 * line.a * line.c) / lineNorm line
    simp only [RFAP.ExplicitField.div_eq_mul_inv, productInverse]
    calc
      ((line.b ^ 2 - line.a ^ 2) * point.x -
            2 * line.a * line.b * point.y -
            2 * line.a * line.c * point.z) *
          (point.z⁻¹ * (lineNorm line)⁻¹) =
        ((line.b ^ 2 - line.a ^ 2) * (point.x * point.z⁻¹) -
            2 * line.a * line.b * (point.y * point.z⁻¹) -
            2 * line.a * line.c * (point.z * point.z⁻¹)) *
          (lineNorm line)⁻¹ := by ring1
      _ = ((line.b ^ 2 - line.a ^ 2) * (point.x * point.z⁻¹) -
            2 * line.a * line.b * (point.y * point.z⁻¹) -
            2 * line.a * line.c) * (lineNorm line)⁻¹ := by rw [zCancel]; ring1
  · change
      (-2 * line.a * line.b * point.x +
          (line.a ^ 2 - line.b ^ 2) * point.y -
          2 * line.b * line.c * point.z) /
          (lineNorm line * point.z) =
        (-2 * line.a * line.b * (point.x / point.z) +
          (line.a ^ 2 - line.b ^ 2) * (point.y / point.z) -
          2 * line.b * line.c) / lineNorm line
    simp only [RFAP.ExplicitField.div_eq_mul_inv, productInverse]
    calc
      (-2 * line.a * line.b * point.x +
            (line.a ^ 2 - line.b ^ 2) * point.y -
            2 * line.b * line.c * point.z) *
          (point.z⁻¹ * (lineNorm line)⁻¹) =
        (-2 * line.a * line.b * (point.x * point.z⁻¹) +
            (line.a ^ 2 - line.b ^ 2) * (point.y * point.z⁻¹) -
            2 * line.b * line.c * (point.z * point.z⁻¹)) *
          (lineNorm line)⁻¹ := by ring1
      _ = (-2 * line.a * line.b * (point.x * point.z⁻¹) +
            (line.a ^ 2 - line.b ^ 2) * (point.y * point.z⁻¹) -
            2 * line.b * line.c) * (lineNorm line)⁻¹ := by rw [zCancel]; ring1

/-- The polynomial conjugation identity underlying Theorem 16. -/
theorem reflectHomogeneous_conjugation [DecidableEq K]
    (firstMirror secondMirror : Line K)
    (secondNonNull : ¬ secondMirror.IsNull)
    (point : HomogeneousPoint K) :
    reflectHomogeneous
        (reflectLine secondMirror firstMirror secondNonNull)
        (reflectHomogeneous secondMirror point) =
      HomogeneousPoint.scale (lineNorm secondMirror ^ 2)
        (reflectHomogeneous secondMirror
          (reflectHomogeneous firstMirror point)) := by
  apply HomogeneousPoint.ext <;>
    unfold reflectHomogeneous HomogeneousPoint.scale reflectLine
      reflectedLineA reflectedLineB reflectedLineC lineNorm <;>
    ring1

/-- Theorem 16 (Reflection): conjugating a reflection by another reflection
reflects its mirror line. -/
theorem reflection_composition [Nontrivial K] [DecidableEq K]
    (firstMirror secondMirror : Line K)
    (firstNonNull : ¬ firstMirror.IsNull)
    (secondNonNull : ¬ secondMirror.IsNull)
    (point : Point K) :
    reflectPoint secondMirror secondNonNull
        (reflectPoint firstMirror firstNonNull point) =
      reflectPoint (reflectLine secondMirror firstMirror secondNonNull)
        (reflectLine_nonNull secondMirror firstMirror secondNonNull firstNonNull)
        (reflectPoint secondMirror secondNonNull point) := by
  let source := HomogeneousPoint.ofPoint point
  let reflectedMirror := reflectLine secondMirror firstMirror secondNonNull
  let reflectedMirrorNonNull :=
    reflectLine_nonNull secondMirror firstMirror secondNonNull firstNonNull
  have sourceZ : source.z ≠ 0 := one_ne_zero
  have firstZ : (reflectHomogeneous firstMirror source).z ≠ 0 := by
    change lineNorm firstMirror * 1 ≠ 0
    exact RFAP.ExplicitField.mul_ne_zero firstNonNull one_ne_zero
  have secondZ : (reflectHomogeneous secondMirror source).z ≠ 0 := by
    change lineNorm secondMirror * 1 ≠ 0
    exact RFAP.ExplicitField.mul_ne_zero secondNonNull one_ne_zero
  have secondAfterFirstZ :
      (reflectHomogeneous secondMirror
        (reflectHomogeneous firstMirror source)).z ≠ 0 := by
    change lineNorm secondMirror * (lineNorm firstMirror * 1) ≠ 0
    exact RFAP.ExplicitField.mul_ne_zero secondNonNull firstZ
  have scaleNonzero : lineNorm secondMirror ^ 2 ≠ 0 := by
    intro squareZero
    apply (RFAP.ExplicitField.mul_ne_zero secondNonNull secondNonNull)
    calc
      lineNorm secondMirror * lineNorm secondMirror =
          lineNorm secondMirror ^ 2 := by ring1
      _ = 0 := squareZero
  have polynomialIdentity :=
    reflectHomogeneous_conjugation firstMirror secondMirror secondNonNull source
  have chartIdentity := congrArg HomogeneousPoint.affineChart polynomialIdentity
  rw [HomogeneousPoint.affineChart_scale _ _ scaleNonzero secondAfterFirstZ]
    at chartIdentity
  have leftChart :
      (reflectHomogeneous secondMirror
        (reflectHomogeneous firstMirror source)).affineChart =
      reflectionFormula secondMirror (reflectionFormula firstMirror point) := by
    rw [affineChart_reflectHomogeneous secondMirror secondNonNull _ firstZ,
      affineChart_reflectHomogeneous firstMirror firstNonNull source sourceZ,
      HomogeneousPoint.affineChart_ofPoint]
  have rightChart :
      (reflectHomogeneous reflectedMirror
        (reflectHomogeneous secondMirror source)).affineChart =
      reflectionFormula reflectedMirror (reflectionFormula secondMirror point) := by
    rw [affineChart_reflectHomogeneous reflectedMirror reflectedMirrorNonNull _ secondZ,
      affineChart_reflectHomogeneous secondMirror secondNonNull source sourceZ,
      HomogeneousPoint.affineChart_ofPoint]
  rw [rightChart, leftChart] at chartIdentity
  rw [reflectPoint_formula, reflectPoint_formula, reflectPoint_formula,
    reflectPoint_formula]
  exact chartIdentity.symm

end DivineProportions
