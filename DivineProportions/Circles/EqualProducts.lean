import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Conics.Circle
import DivineProportions.Conics.LineIntersection

/-!
# Divine Proportions, §16.2: equal products

The source derives Theorem 106 from subtended spreads and the Spread law.  The
finite algebra underneath that proof is stronger: along any displayed chord,
the product of the two endpoint quadrances is the square of the intersection
point's circle-power.  This form needs no non-null hypotheses or division.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

/-- The finite four-point determinant which vanishes when the points lie on
one circle, written relative to the fourth point. -/
def fourPointCircleDeterminant
    (first second third fourth : Point K) : K :=
  quadrance first fourth * pointDeterminant fourth second third -
    quadrance second fourth * pointDeterminant fourth first third +
    quadrance third fourth * pointDeterminant fourth first second

/-- Equal circle radii express a chord quadrance as twice a displayed dot
product based at one endpoint. -/
private theorem chordQuadrance_eq_twice_dot
    (center first second : Point K) (circleQuadrance : K)
    (firstRadius : quadrance first center = circleQuadrance)
    (secondRadius : quadrance second center = circleQuadrance) :
    quadrance first second =
      2 * ((first.x - second.x) * (center.x - second.x) +
        (first.y - second.y) * (center.y - second.y)) := by
  calc
    quadrance first second =
        quadrance first second + quadrance second center -
          circleQuadrance := by
      rw [secondRadius]
      ring1
    _ = quadrance first second + quadrance second center -
        quadrance first center := by rw [firstRadius]
    _ = 2 * ((first.x - second.x) * (center.x - second.x) +
        (first.y - second.y) * (center.y - second.y)) := by
      unfold quadrance
      ring1

/-- Four displayed points on one circle make the finite circle determinant
vanish.  No distinctness, non-nullness, or division is needed. -/
theorem fourPointCircleDeterminant_eq_zero
    (circle : Conic K) (center : Point K) (circleQuadrance : K)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (first second third fourth : Point K)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (thirdOnCircle : circle.Contains third)
    (fourthOnCircle : circle.Contains fourth) :
    fourPointCircleDeterminant first second third fourth = 0 := by
  have firstRadius : quadrance first center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstOnCircle
  have secondRadius : quadrance second center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondOnCircle
  have thirdRadius : quadrance third center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center third circleQuadrance
      presentation).1 thirdOnCircle
  have fourthRadius : quadrance fourth center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center fourth circleQuadrance
      presentation).1 fourthOnCircle
  have firstChord := chordQuadrance_eq_twice_dot center first fourth
    circleQuadrance firstRadius fourthRadius
  have secondChord := chordQuadrance_eq_twice_dot center second fourth
    circleQuadrance secondRadius fourthRadius
  have thirdChord := chordQuadrance_eq_twice_dot center third fourth
    circleQuadrance thirdRadius fourthRadius
  unfold fourPointCircleDeterminant pointDeterminant
  rw [firstChord, secondChord, thirdChord]
  ring1

/-- The quadrance from the first endpoint to a Thales point on its line. -/
private theorem quadrance_first_thalesPoint
    (first second : Point K) (scale : K) :
    quadrance first (thalesPoint scale first second) =
      scale ^ 2 * quadrance first second := by
  unfold quadrance thalesPoint affineCombination
  ring1

/-- The quadrance from a Thales point to the second endpoint. -/
private theorem quadrance_thalesPoint_second
    (first second : Point K) (scale : K) :
    quadrance (thalesPoint scale first second) second =
      (1 - scale) ^ 2 * quadrance first second := by
  unfold quadrance thalesPoint affineCombination
  ring1

/-- Equal endpoint radii turn the circle-power of a point on their line into
the displayed, denominator-free chord parameter product. -/
private theorem thalesPoint_circle_power
    (first second center : Point K) (circleQuadrance scale : K)
    (firstRadius : quadrance first center = circleQuadrance)
    (secondRadius : quadrance second center = circleQuadrance) :
    quadrance (thalesPoint scale first second) center - circleQuadrance =
      -(scale * (1 - scale) * quadrance first second) := by
  calc
    quadrance (thalesPoint scale first second) center - circleQuadrance =
        (1 - scale) * quadrance first center +
          scale * quadrance second center -
          scale * (1 - scale) * quadrance first second -
          circleQuadrance := by
      unfold quadrance thalesPoint affineCombination
      ring1
    _ = -(scale * (1 - scale) * quadrance first second) := by
      rw [firstRadius, secondRadius]
      ring1

/-- The signed, denominator-free circle-power formula along a chord.  Keeping
the Thales parameter retains the sign information that is lost after squaring
in the Equal products theorem. -/
theorem thalesPoint_circle_power_of_circle
    (circle : Conic K) (center first second : Point K)
    (circleQuadrance scale : K)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second) :
    quadrance (thalesPoint scale first second) center - circleQuadrance =
      -(scale * (1 - scale) * quadrance first second) := by
  have firstRadius : quadrance first center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstOnCircle
  have secondRadius : quadrance second center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondOnCircle
  exact thalesPoint_circle_power first second center circleQuadrance scale
    firstRadius secondRadius

/-- The denominator-free chord-power identity.  It strengthens the algebraic
core of Theorem 106 by allowing any circle quadrance and any displayed chord,
including a null chord. -/
theorem chord_quadrance_product_eq_circle_power [DecidableEq K]
    (circle : Conic K) (center : Point K) (circleQuadrance : K)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (first second point : Point K) (distinct : first ≠ second)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (pointOnLine :
      (lineThrough first second distinct).Contains point) :
    quadrance first point * quadrance point second =
      (quadrance point center - circleQuadrance) ^ 2 := by
  have firstRadius : quadrance first center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstOnCircle
  have secondRadius : quadrance second center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondOnCircle
  rcases thalesPoint_exists_of_on_line first second point distinct pointOnLine with
    ⟨scale, pointFormula⟩
  subst point
  rw [quadrance_first_thalesPoint, quadrance_thalesPoint_second,
    thalesPoint_circle_power first second center circleQuadrance scale
      firstRadius secondRadius]
  ring1

/-- Theorem 106 (Equal products): the products cut out by two intersecting
chords of a circle are equal. -/
theorem equal_products [DecidableEq K]
    (circle : Conic K) (center : Point K) (circleQuadrance : K)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (first second third fourth intersection : Point K)
    (distinct :
      first ≠ second ∧ first ≠ third ∧ first ≠ fourth ∧
        second ≠ third ∧ second ≠ fourth ∧ third ≠ fourth)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (thirdOnCircle : circle.Contains third)
    (fourthOnCircle : circle.Contains fourth)
    (intersectionOnFirstFourth :
      (lineThrough first fourth distinct.2.2.1).Contains intersection)
    (intersectionOnSecondThird :
      (lineThrough second third distinct.2.2.2.1).Contains intersection) :
    quadrance first intersection * quadrance intersection fourth =
      quadrance second intersection * quadrance intersection third := by
  calc
    quadrance first intersection * quadrance intersection fourth =
        (quadrance intersection center - circleQuadrance) ^ 2 :=
      chord_quadrance_product_eq_circle_power circle center circleQuadrance
        presentation first fourth intersection distinct.2.2.1
        firstOnCircle fourthOnCircle intersectionOnFirstFourth
    _ = quadrance second intersection * quadrance intersection third :=
      (chord_quadrance_product_eq_circle_power circle center circleQuadrance
        presentation second third intersection distinct.2.2.2.1
        secondOnCircle thirdOnCircle intersectionOnSecondThird).symm

end Conic

end DivineProportions
