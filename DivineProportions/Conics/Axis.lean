import DivineProportions.Conics.Center

/-!
# Divine Proportions, conic axes

An axis is retained as an explicit non-null mirror together with the finite
equation-preservation identity from Exercise 15.8.  The elementary reflection
lemmas below construct the two mirrors used for quadrolas without selecting
any roots or completed geometric object.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- The source definition of an axis: reflection in a non-null line preserves
the displayed conic equation pointwise. -/
def IsAxis (conic : Conic K) (axis : Line K) : Prop :=
  ∃ nonNull : ¬ axis.IsNull,
    ∀ point : Point K,
      conic.evaluate (reflectPoint axis nonNull point) = conic.evaluate point

end Conic

/-- A point on a non-null mirror is fixed by the executable reflection map. -/
theorem reflectPoint_fixed_of_contains (line : Line K)
    (nonNull : ¬ line.IsNull) (point : Point K)
    (contains : line.Contains point) :
    reflectPoint line nonNull point = point := by
  have pointIsFoot : point = altitudeFoot point line nonNull :=
    altitudeFoot_unique point line nonNull point contains
      (altitudeThrough_contains point line)
  unfold reflectPoint
  rw [← pointIsFoot]
  apply Point.ext <;> unfold rotateInPoint <;> ring1

private theorem midpoint_twice_x (first second : Point K)
    (twoNonzero : (2 : K) ≠ 0) :
    2 * (midpoint first second).x = first.x + second.x := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  change 2 * ((first.x + second.x) / 2) = first.x + second.x
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    2 * ((first.x + second.x) * (2 : K)⁻¹) =
        (first.x + second.x) * (2 * (2 : K)⁻¹) := by ring1
    _ = first.x + second.x := by rw [twoCancel]; ring1

private theorem midpoint_twice_y (first second : Point K)
    (twoNonzero : (2 : K) ≠ 0) :
    2 * (midpoint first second).y = first.y + second.y := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  change 2 * ((first.y + second.y) / 2) = first.y + second.y
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    2 * ((first.y + second.y) * (2 : K)⁻¹) =
        (first.y + second.y) * (2 * (2 : K)⁻¹) := by ring1
    _ = first.y + second.y := by rw [twoCancel]; ring1

private theorem midpoint_on_perpendicularBisector_altitude [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    (altitudeThrough first (perpendicularBisector first second distinct)).Contains
      (midpoint first second) := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  unfold altitudeThrough perpendicularBisector midpoint Line.Contains
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    -(first.y - second.y) *
            ((first.x + second.x) * (2 : K)⁻¹) +
          (first.x - second.x) *
            ((first.y + second.y) * (2 : K)⁻¹) +
          ((first.y - second.y) * first.x -
            (first.x - second.x) * first.y) =
        (1 - 2 * (2 : K)⁻¹) *
          ((first.y - second.y) * first.x -
            (first.x - second.x) * first.y) := by ring1
    _ = 0 := by rw [twoCancel]; ring1

/-- Reflection in the perpendicular bisector exchanges its first endpoint
with the second. -/
theorem reflectPoint_perpendicularBisector_first [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0)
    (bisectorNonNull :
      ¬ (perpendicularBisector first second distinct).IsNull) :
    reflectPoint (perpendicularBisector first second distinct)
      bisectorNonNull first = second := by
  let bisector := perpendicularBisector first second distinct
  have midpointIsFoot :
      midpoint first second = altitudeFoot first bisector bisectorNonNull := by
    apply altitudeFoot_unique first bisector bisectorNonNull
    · exact perpendicularBisector_contains_midpoint first second distinct
    · exact midpoint_on_perpendicularBisector_altitude first second distinct
        twoNonzero
  have twiceX := midpoint_twice_x first second twoNonzero
  have twiceY := midpoint_twice_y first second twoNonzero
  unfold reflectPoint
  rw [← midpointIsFoot]
  apply Point.ext
  · change 2 * (midpoint first second).x - first.x = second.x
    rw [twiceX]
    ring1
  · change 2 * (midpoint first second).y - first.y = second.y
    rw [twiceY]
    ring1

/-- The reverse endpoint exchange follows from involutivity of reflection. -/
theorem reflectPoint_perpendicularBisector_second [DecidableEq K]
    (first second : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0)
    (bisectorNonNull :
      ¬ (perpendicularBisector first second distinct).IsNull) :
    reflectPoint (perpendicularBisector first second distinct)
      bisectorNonNull second = first := by
  let bisector := perpendicularBisector first second distinct
  have firstToSecond := reflectPoint_perpendicularBisector_first first second
    distinct twoNonzero bisectorNonNull
  calc
    reflectPoint bisector bisectorNonNull second =
        reflectPoint bisector bisectorNonNull
          (reflectPoint bisector bisectorNonNull first) := by
            rw [firstToSecond]
    _ = first := reflectPoint_involutive bisector bisectorNonNull first

end DivineProportions
