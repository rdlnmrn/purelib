import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Plane.Incidence

/-!
# Divine Proportions, §3.4: the foot of an altitude

The construction is the exact rational formula printed in Theorem 8.  Its only
denominator is the direction quadrance `a² + b²`, so the source's non-null-line
hypothesis is exposed as the precise executable cancellation certificate.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Direction quadrance of a displayed line. -/
def lineNorm (line : Line K) : K := line.a ^ 2 + line.b ^ 2

theorem line_isNull_iff_norm_eq_zero (line : Line K) :
    line.IsNull ↔ lineNorm line = 0 := Iff.rfl

/-- The exact coordinate formula in Theorem 8. -/
def altitudeFoot (point : Point K) (line : Line K)
    (_nonNull : ¬ line.IsNull) : Point K :=
  { x := (line.b ^ 2 * point.x - line.a * line.b * point.y -
      line.a * line.c) / lineNorm line
    y := (-line.a * line.b * point.x + line.a ^ 2 * point.y -
      line.b * line.c) / lineNorm line }

private theorem lineNorm_ne_zero {line : Line K} (nonNull : ¬ line.IsNull) :
    lineNorm line ≠ 0 := nonNull

/-- The foot given by Theorem 8 lies on the target line. -/
theorem altitudeFoot_on_line (point : Point K) (line : Line K)
    (nonNull : ¬ line.IsNull) :
    line.Contains (altitudeFoot point line nonNull) := by
  have normNonzero : lineNorm line ≠ 0 := lineNorm_ne_zero nonNull
  have normCancel : lineNorm line * (lineNorm line)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ normNonzero
  unfold Line.Contains altitudeFoot
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    line.a *
          ((line.b ^ 2 * point.x - line.a * line.b * point.y -
              line.a * line.c) * (lineNorm line)⁻¹) +
        line.b *
          ((-line.a * line.b * point.x + line.a ^ 2 * point.y -
              line.b * line.c) * (lineNorm line)⁻¹) +
        line.c = -line.c * (lineNorm line * (lineNorm line)⁻¹) + line.c := by
      unfold lineNorm
      ring1
    _ = 0 := by rw [normCancel]; ring1

/-- The foot given by Theorem 8 also lies on the altitude through the point. -/
theorem altitudeFoot_on_altitude (point : Point K) (line : Line K)
    (nonNull : ¬ line.IsNull) :
    (altitudeThrough point line).Contains (altitudeFoot point line nonNull) := by
  have normNonzero : lineNorm line ≠ 0 := lineNorm_ne_zero nonNull
  have normCancel : lineNorm line * (lineNorm line)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ normNonzero
  unfold Line.Contains altitudeThrough altitudeFoot
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    -line.b *
          ((line.b ^ 2 * point.x - line.a * line.b * point.y -
              line.a * line.c) * (lineNorm line)⁻¹) +
        line.a *
          ((-line.a * line.b * point.x + line.a ^ 2 * point.y -
              line.b * line.c) * (lineNorm line)⁻¹) +
        (line.b * point.x - line.a * point.y) =
      (-line.b * point.x + line.a * point.y) *
          (lineNorm line * (lineNorm line)⁻¹) +
        (line.b * point.x - line.a * point.y) := by
      unfold lineNorm
      ring1
    _ = 0 := by rw [normCancel]; ring1

/-- A non-null line and its altitude are not parallel. -/
theorem altitude_not_parallel (point : Point K) (line : Line K)
    (nonNull : ¬ line.IsNull) :
    ¬ (altitudeThrough point line).Parallel line := by
  intro parallel
  apply nonNull
  unfold Line.Parallel altitudeThrough at parallel
  unfold Line.IsNull
  calc
    line.a ^ 2 + line.b ^ 2 =
        -((-line.b) * line.b - line.a * line.a) := by ring1
    _ = 0 := by rw [parallel]; exact neg_zero

/-- Theorem 8 (Foot of an altitude): the displayed point is the unique
intersection of the target line and the altitude. -/
theorem altitudeFoot_unique (point : Point K) (line : Line K)
    (nonNull : ¬ line.IsNull) (candidate : Point K)
    (onLine : line.Contains candidate)
    (onAltitude : (altitudeThrough point line).Contains candidate) :
    candidate = altitudeFoot point line nonNull := by
  let nonparallel := altitude_not_parallel point line nonNull
  have candidateIntersection :=
    lineIntersection_unique (altitudeThrough point line) line nonparallel
      candidate onAltitude onLine
  have footIntersection :=
    lineIntersection_unique (altitudeThrough point line) line nonparallel
      (altitudeFoot point line nonNull)
      (altitudeFoot_on_altitude point line nonNull)
      (altitudeFoot_on_line point line nonNull)
  exact candidateIntersection.trans footIntersection.symm

namespace ExampleThreeFive

open FieldEleven

def sourcePoint : Point Element := ⟨7, 6⟩

def sourceLine : Line Element where
  a := 10
  b := 5
  c := 1
  direction_nonzero := Or.inl (by decide)

def displayedAltitude : Line Element where
  a := 9
  b := 4
  c := 1
  direction_nonzero := Or.inl (by decide)

theorem sourceLine_nonNull : ¬ sourceLine.IsNull := by
  unfold Line.IsNull sourceLine
  decide

/-- Example 3.5: the book's displayed altitude is a proportional
representative of the constructed altitude. -/
theorem altitude_equivalent :
    (altitudeThrough sourcePoint sourceLine).Equivalent displayedAltitude := by
  unfold Line.Equivalent altitudeThrough sourcePoint sourceLine displayedAltitude
  decide

/-- Example 3.5: the exact foot is `[2,9]` in `F₁₁`. -/
theorem foot_eq :
    altitudeFoot sourcePoint sourceLine sourceLine_nonNull = (⟨2, 9⟩ : Point Element) := by
  decide

end ExampleThreeFive

end DivineProportions
