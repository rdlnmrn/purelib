import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Isometries.Basic
import DivineProportions.Plane.Reflection

/-!
# Divine Proportions, §13.1: translations, rotations, and reflections

This file gives executable isometries for the coordinate transformations in
Examples 13.1–13.3 and proves the composition calculations requested in
Exercises 13.2, 13.4, and 13.5.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The coordinate map `τ_{u,v}([x,y]) = [x+u,y+v]`. -/
def translationPoint (u v : K) (point : Point K) : Point K :=
  ⟨point.x + u, point.y + v⟩

/-- Example 13.1: translation by `[u,v]`, with translation by `[-u,-v]` as
its displayed inverse. -/
def translation (u v : K) : PlaneIsometry K where
  toFun := translationPoint u v
  inverseFun := translationPoint (-u) (-v)
  inverse_after := by
    intro point
    apply Point.ext <;>
      unfold translationPoint <;>
      ring1
  after_inverse := by
    intro point
    apply Point.ext <;>
      unfold translationPoint <;>
      ring1
  preservesQuadrance := by
    intro first second
    unfold quadrance translationPoint
    ring1

@[simp] theorem translation_apply (u v : K) (point : Point K) :
    translation u v point = translationPoint u v point := rfl

/-- The inverse formula printed in Example 13.1. -/
theorem translation_inverse_apply (u v : K) (point : Point K) :
    (translation u v).inverse point = translation (-u) (-v) point := rfl

/-- Exercise 13.2: rotation in any point is an isometry.  Its displayed
inverse is itself, exactly as established in Exercise 4.1. -/
def rotationInPointIsometry (center : Point K) : PlaneIsometry K where
  toFun := rotateInPoint center
  inverseFun := rotateInPoint center
  inverse_after := rotateInPoint_involutive center
  after_inverse := rotateInPoint_involutive center
  preservesQuadrance := by
    intro first second
    unfold quadrance rotateInPoint
    ring1

/-- The finite polynomial calculation that reflection in a non-null line
preserves quadrance. -/
theorem reflectPoint_preserves_quadrance
    (line : Line K) (nonNull : ¬ line.IsNull) (first second : Point K) :
    quadrance (reflectPoint line nonNull first)
        (reflectPoint line nonNull second) =
      quadrance first second := by
  have normCancel : lineNorm line * (lineNorm line)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ nonNull
  rw [reflectPoint_formula, reflectPoint_formula]
  unfold quadrance reflectionFormula
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    ((((line.b ^ 2 - line.a ^ 2) * second.x -
              2 * line.a * line.b * second.y - 2 * line.a * line.c) *
            (lineNorm line)⁻¹ -
          ((line.b ^ 2 - line.a ^ 2) * first.x -
              2 * line.a * line.b * first.y - 2 * line.a * line.c) *
            (lineNorm line)⁻¹) ^ 2 +
        ((-2 * line.a * line.b * second.x +
              (line.a ^ 2 - line.b ^ 2) * second.y -
              2 * line.b * line.c) * (lineNorm line)⁻¹ -
          (-2 * line.a * line.b * first.x +
              (line.a ^ 2 - line.b ^ 2) * first.y -
              2 * line.b * line.c) * (lineNorm line)⁻¹) ^ 2) =
      ((second.x - first.x) ^ 2 + (second.y - first.y) ^ 2) *
        (lineNorm line * (lineNorm line)⁻¹) ^ 2 := by
          unfold lineNorm
          ring1
    _ = (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 := by
      rw [normCancel]
      ring1

/-- Exercise 13.2: reflection in a displayed non-null line is an isometry,
with its explicit involution as inverse. -/
def lineReflectionIsometry (line : Line K) (nonNull : ¬ line.IsNull) :
    PlaneIsometry K where
  toFun := reflectPoint line nonNull
  inverseFun := reflectPoint line nonNull
  inverse_after := reflectPoint_involutive line nonNull
  after_inverse := reflectPoint_involutive line nonNull
  preservesQuadrance := reflectPoint_preserves_quadrance line nonNull

/-- The coordinate map `σ_{q,r}([x,y]) = [qx+ry,rx-qy]`. -/
def centralReflectionPoint (q r : K) (point : Point K) : Point K :=
  ⟨q * point.x + r * point.y, r * point.x - q * point.y⟩

/-- Example 13.2: a unit pair gives a self-inverse central reflection. -/
def centralReflection (q r : K) (unit : q ^ 2 + r ^ 2 = 1) :
    PlaneIsometry K where
  toFun := centralReflectionPoint q r
  inverseFun := centralReflectionPoint q r
  inverse_after := by
    intro point
    apply Point.ext
    · simp only [centralReflectionPoint]
      calc
        q * (q * point.x + r * point.y) +
            r * (r * point.x - q * point.y) =
          (q ^ 2 + r ^ 2) * point.x := by ring1
        _ = point.x := by rw [unit]; ring1
    · simp only [centralReflectionPoint]
      calc
        r * (q * point.x + r * point.y) -
            q * (r * point.x - q * point.y) =
          (q ^ 2 + r ^ 2) * point.y := by ring1
        _ = point.y := by rw [unit]; ring1
  after_inverse := by
    intro point
    apply Point.ext
    · simp only [centralReflectionPoint]
      calc
        q * (q * point.x + r * point.y) +
            r * (r * point.x - q * point.y) =
          (q ^ 2 + r ^ 2) * point.x := by ring1
        _ = point.x := by rw [unit]; ring1
    · simp only [centralReflectionPoint]
      calc
        r * (q * point.x + r * point.y) -
            q * (r * point.x - q * point.y) =
          (q ^ 2 + r ^ 2) * point.y := by ring1
        _ = point.y := by rw [unit]; ring1
  preservesQuadrance := by
    intro first second
    unfold quadrance
    simp only [centralReflectionPoint]
    calc
      (q * second.x + r * second.y -
            (q * first.x + r * first.y)) ^ 2 +
          (r * second.x - q * second.y -
            (r * first.x - q * first.y)) ^ 2 =
        (q ^ 2 + r ^ 2) *
          ((second.x - first.x) ^ 2 + (second.y - first.y) ^ 2) := by
            ring1
      _ = (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 := by
        rw [unit]
        ring1

/-- Example 13.2: a central reflection fixes the origin. -/
theorem centralReflection_orthogonality (q r : K)
    (unit : q ^ 2 + r ^ 2 = 1) :
    (centralReflection q r unit).IsOrthogonality := by
  unfold PlaneIsometry.IsOrthogonality planeOrigin centralReflection
    centralReflectionPoint
  apply Point.ext <;>
    ring1

/-- The coordinate map `ρ_{q,r}([x,y]) = [qx-ry,rx+qy]`. -/
def centralRotationPoint (q r : K) (point : Point K) : Point K :=
  ⟨q * point.x - r * point.y, r * point.x + q * point.y⟩

/-- Example 13.3: a unit pair gives a central rotation whose displayed inverse
has parameters `[q,-r]`. -/
def centralRotation (q r : K) (unit : q ^ 2 + r ^ 2 = 1) :
    PlaneIsometry K where
  toFun := centralRotationPoint q r
  inverseFun := centralRotationPoint q (-r)
  inverse_after := by
    intro point
    apply Point.ext
    · simp only [centralRotationPoint]
      calc
        q * (q * point.x - r * point.y) -
            (-r) * (r * point.x + q * point.y) =
          (q ^ 2 + r ^ 2) * point.x := by ring1
        _ = point.x := by rw [unit]; ring1
    · simp only [centralRotationPoint]
      calc
        (-r) * (q * point.x - r * point.y) +
            q * (r * point.x + q * point.y) =
          (q ^ 2 + r ^ 2) * point.y := by ring1
        _ = point.y := by rw [unit]; ring1
  after_inverse := by
    intro point
    apply Point.ext
    · simp only [centralRotationPoint]
      calc
        q * (q * point.x - (-r) * point.y) -
            r * ((-r) * point.x + q * point.y) =
          (q ^ 2 + r ^ 2) * point.x := by ring1
        _ = point.x := by rw [unit]; ring1
    · simp only [centralRotationPoint]
      calc
        r * (q * point.x - (-r) * point.y) +
            q * ((-r) * point.x + q * point.y) =
          (q ^ 2 + r ^ 2) * point.y := by ring1
        _ = point.y := by rw [unit]; ring1
  preservesQuadrance := by
    intro first second
    unfold quadrance
    simp only [centralRotationPoint]
    calc
      (q * second.x - r * second.y -
            (q * first.x - r * first.y)) ^ 2 +
          (r * second.x + q * second.y -
            (r * first.x + q * first.y)) ^ 2 =
        (q ^ 2 + r ^ 2) *
          ((second.x - first.x) ^ 2 + (second.y - first.y) ^ 2) := by
            ring1
      _ = (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 := by
        rw [unit]
        ring1

/-- The inverse formula printed in Example 13.3. -/
theorem centralRotation_inverse_apply (q r : K)
    (unit : q ^ 2 + r ^ 2 = 1) (point : Point K) :
    (centralRotation q r unit).inverse point =
      centralRotationPoint q (-r) point := rfl

/-- Example 13.3: a central rotation fixes the origin. -/
theorem centralRotation_orthogonality (q r : K)
    (unit : q ^ 2 + r ^ 2 = 1) :
    (centralRotation q r unit).IsOrthogonality := by
  unfold PlaneIsometry.IsOrthogonality planeOrigin centralRotation
    centralRotationPoint
  apply Point.ext <;>
    ring1

/-- Exercise 13.4: the identity is the central rotation with parameters
`[1,0]`. -/
theorem identity_centralRotationPoint (point : Point K) :
    centralRotationPoint 1 0 point = point := by
  apply Point.ext <;>
    simp only [centralRotationPoint] <;>
    ring1

/-- Exercise 13.4: outside characteristic two, a unit central rotation cannot
also have the coordinate form of a central reflection. -/
theorem centralRotationPoint_ne_centralReflectionPoint
    [Nontrivial K] (q r t u : K) (unit : q ^ 2 + r ^ 2 = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    ¬ ∀ point : Point K,
      centralRotationPoint q r point = centralReflectionPoint t u point := by
  intro sameMap
  have firstAxis := sameMap (⟨1, 0⟩ : Point K)
  have secondAxis := sameMap (⟨0, 1⟩ : Point K)
  have qEqT : q = t := by
    simpa [centralRotationPoint, centralReflectionPoint] using
      congrArg Point.x firstAxis
  have rEqU : r = u := by
    simpa [centralRotationPoint, centralReflectionPoint] using
      congrArg Point.y firstAxis
  have negREqU : -r = u := by
    simpa [centralRotationPoint, centralReflectionPoint] using
      congrArg Point.x secondAxis
  have qEqNegT : q = -t := by
    simpa [centralRotationPoint, centralReflectionPoint] using
      congrArg Point.y secondAxis
  have twoQZero : (2 : K) * q = 0 := by
    calc
      (2 : K) * q = q + t := by rw [← qEqT]; ring1
      _ = 0 := by rw [qEqNegT]; ring1
  have twoRZero : (2 : K) * r = 0 := by
    calc
      (2 : K) * r = r + u := by rw [← rEqU]; ring1
      _ = 0 := by rw [← negREqU]; ring1
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  have qZero : q = 0 := by
    calc
      q = 1 * q := by ring1
      _ = (2 * (2 : K)⁻¹) * q := by rw [twoCancel]
      _ = (2 : K)⁻¹ * (2 * q) := by ring1
      _ = 0 := by rw [twoQZero]; ring1
  have rZero : r = 0 := by
    calc
      r = 1 * r := by ring1
      _ = (2 * (2 : K)⁻¹) * r := by rw [twoCancel]
      _ = (2 : K)⁻¹ * (2 * r) := by ring1
      _ = 0 := by rw [twoRZero]; ring1
  have zeroEqualsOne : (0 : K) = 1 := by
    calc
      0 = q ^ 2 + r ^ 2 := by rw [qZero, rZero]; ring1
      _ = 1 := unit
  exact zero_ne_one zeroEqualsOne

/-- The output parameters for a composition of two central reflections are
again a unit pair. -/
theorem centralReflectionComposition_unit
    (q r t u : K) (firstUnit : q ^ 2 + r ^ 2 = 1)
    (secondUnit : t ^ 2 + u ^ 2 = 1) :
    (q * t + r * u) ^ 2 + (q * u - r * t) ^ 2 = 1 := by
  calc
    (q * t + r * u) ^ 2 + (q * u - r * t) ^ 2 =
        (q ^ 2 + r ^ 2) * (t ^ 2 + u ^ 2) := by ring1
    _ = 1 := by rw [firstUnit, secondUnit]; ring1

/-- Exercise 13.5, reflection-reflection calculation:
`σ_{t,u} σ_{q,r} = ρ_{qt+ru,qu-rt}`. -/
theorem centralReflectionPoint_comp (q r t u : K) (point : Point K) :
    centralReflectionPoint t u (centralReflectionPoint q r point) =
      centralRotationPoint (q * t + r * u) (q * u - r * t) point := by
  apply Point.ext <;>
    simp only [centralReflectionPoint, centralRotationPoint] <;>
    ring1

/-- The output parameters for a composition of central rotations are again a
unit pair. -/
theorem centralRotationComposition_unit
    (q r t u : K) (firstUnit : q ^ 2 + r ^ 2 = 1)
    (secondUnit : t ^ 2 + u ^ 2 = 1) :
    (q * t - r * u) ^ 2 + (q * u + r * t) ^ 2 = 1 := by
  calc
    (q * t - r * u) ^ 2 + (q * u + r * t) ^ 2 =
        (q ^ 2 + r ^ 2) * (t ^ 2 + u ^ 2) := by ring1
    _ = 1 := by rw [firstUnit, secondUnit]; ring1

/-- Exercise 13.5, rotation-rotation calculation in both orders. -/
theorem centralRotationPoint_comp (q r t u : K) (point : Point K) :
    centralRotationPoint q r (centralRotationPoint t u point) =
        centralRotationPoint (q * t - r * u) (q * u + r * t) point ∧
      centralRotationPoint t u (centralRotationPoint q r point) =
        centralRotationPoint (q * t - r * u) (q * u + r * t) point := by
  constructor <;>
    apply Point.ext <;>
    simp only [centralRotationPoint] <;>
    ring1

/-- Exercise 13.5, collecting the two composition laws together with the
unit-pair calculations that make every displayed map an isometry. -/
theorem exercise_13_5 (q r t u : K)
    (firstUnit : q ^ 2 + r ^ 2 = 1)
    (secondUnit : t ^ 2 + u ^ 2 = 1) (point : Point K) :
    ((q * t + r * u) ^ 2 + (q * u - r * t) ^ 2 = 1) ∧
      centralReflectionPoint t u (centralReflectionPoint q r point) =
        centralRotationPoint (q * t + r * u) (q * u - r * t) point ∧
      ((q * t - r * u) ^ 2 + (q * u + r * t) ^ 2 = 1) ∧
      centralRotationPoint q r (centralRotationPoint t u point) =
        centralRotationPoint (q * t - r * u) (q * u + r * t) point ∧
      centralRotationPoint t u (centralRotationPoint q r point) =
        centralRotationPoint (q * t - r * u) (q * u + r * t) point := by
  exact ⟨centralReflectionComposition_unit q r t u firstUnit secondUnit,
    centralReflectionPoint_comp q r t u point,
    centralRotationComposition_unit q r t u firstUnit secondUnit,
    (centralRotationPoint_comp q r t u point).1,
    (centralRotationPoint_comp q r t u point).2⟩

end DivineProportions
