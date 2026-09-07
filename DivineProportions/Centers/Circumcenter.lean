import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Proportions.MenelausCeva

/-!
# Divine Proportions, Chapter 12: circumcenters

The circumcenter is an explicit finite line intersection.  Noncollinearity
proves its denominator nonzero; equal-quadrance transitivity then supplies the
third perpendicular-bisector incidence.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- Two side perpendicular bisectors used to construct the circumcenter are
nonparallel precisely because the three vertices are noncollinear. -/
theorem circumcenter_bisectors_not_parallel
    [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third) :
    ¬ (perpendicularBisector second third secondThirdDistinct).Parallel
      (perpendicularBisector first third firstThirdDistinct) := by
  intro parallel
  apply notCollinear
  apply (collinear_iff_pointDeterminant_eq_zero first second third).2
  unfold Line.Parallel perpendicularBisector at parallel
  calc
    pointDeterminant first second third =
        -((second.x - third.x) * (first.y - third.y) -
          (first.x - third.x) * (second.y - third.y)) := by
      unfold pointDeterminant
      ring1
    _ = 0 := by rw [parallel]; ring1

/-- The displayed circumcenter: the explicit intersection of the
perpendicular bisectors of `A₂A₃` and `A₁A₃`. -/
def circumcenterPoint [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third) : Point K :=
  lineIntersection
    (perpendicularBisector second third secondThirdDistinct)
    (perpendicularBisector first third firstThirdDistinct)
    (circumcenter_bisectors_not_parallel first second third
      firstThirdDistinct secondThirdDistinct notCollinear)

/-- The circumquadrance belonging to the displayed circumcenter. -/
def circumquadrance [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third) : K :=
  quadrance
    (circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear)
    first

/-- Theorem 81 (Circumcenter).  The final two equalities also justify the
book's subsequent definition of the common circumquadrance. -/
theorem circumcenter [Nontrivial K] [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (notCollinear : ¬ Collinear first second third)
    (twoNonzero : (2 : K) ≠ 0) :
    let center := circumcenterPoint first second third firstThirdDistinct
      secondThirdDistinct notCollinear
    (perpendicularBisector second third secondThirdDistinct).Contains center ∧
      (perpendicularBisector first third firstThirdDistinct).Contains center ∧
      (perpendicularBisector first second firstSecondDistinct).Contains center ∧
      quadrance center first = quadrance center second ∧
      quadrance center second = quadrance center third := by
  dsimp only
  let nonparallel := circumcenter_bisectors_not_parallel first second third
    firstThirdDistinct secondThirdDistinct notCollinear
  have onSecondThird :
      (perpendicularBisector second third secondThirdDistinct).Contains
        (circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear) := by
    unfold circumcenterPoint
    exact lineIntersection_on_first
      (perpendicularBisector second third secondThirdDistinct)
      (perpendicularBisector first third firstThirdDistinct) nonparallel
  have onFirstThird :
      (perpendicularBisector first third firstThirdDistinct).Contains
        (circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear) := by
    unfold circumcenterPoint
    exact lineIntersection_on_second
      (perpendicularBisector second third secondThirdDistinct)
      (perpendicularBisector first third firstThirdDistinct) nonparallel
  have equalSecondThird :
      quadrance
          (circumcenterPoint first second third firstThirdDistinct
            secondThirdDistinct notCollinear) second =
        quadrance
          (circumcenterPoint first second third firstThirdDistinct
            secondThirdDistinct notCollinear) third :=
    (equal_quadrance_iff_perpendicularBisector_contains second third
      (circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear)
      secondThirdDistinct twoNonzero).2 onSecondThird
  have equalFirstThird :
      quadrance
          (circumcenterPoint first second third firstThirdDistinct
            secondThirdDistinct notCollinear) first =
        quadrance
          (circumcenterPoint first second third firstThirdDistinct
            secondThirdDistinct notCollinear) third :=
    (equal_quadrance_iff_perpendicularBisector_contains first third
      (circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear)
      firstThirdDistinct twoNonzero).2 onFirstThird
  have equalFirstSecond :
      quadrance
          (circumcenterPoint first second third firstThirdDistinct
            secondThirdDistinct notCollinear) first =
        quadrance
          (circumcenterPoint first second third firstThirdDistinct
            secondThirdDistinct notCollinear) second :=
    equalFirstThird.trans equalSecondThird.symm
  have onFirstSecond :
      (perpendicularBisector first second firstSecondDistinct).Contains
        (circumcenterPoint first second third firstThirdDistinct
          secondThirdDistinct notCollinear) :=
    (equal_quadrance_iff_perpendicularBisector_contains first second
      (circumcenterPoint first second third firstThirdDistinct
        secondThirdDistinct notCollinear)
      firstSecondDistinct twoNonzero).1 equalFirstSecond
  exact ⟨onSecondThird, onFirstThird, onFirstSecond, equalFirstSecond,
    equalSecondThird⟩

end DivineProportions
