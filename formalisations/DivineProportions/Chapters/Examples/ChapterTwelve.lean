module
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Fraction.Construction
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Line.PerpendicularBisector
public import Purelib.Geometry.Plane.Line.Quadrance
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Quadrea.Basic
public import Purelib.Algebra.Field.Finite.Thirteen

public import Purelib.Geometry.Triangles.Circumcenter.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Gaussian.Field

open Purelib.Data.Gaussian.Fraction
open Purelib.Geometry.Trigonometry.Spread.Triple.TripleSpread

open Purelib.Algebra.Field

open Purelib.Data

open Purelib.Geometry.Plane

open Purelib.Geometry.Triangles

open Purelib

section
@[expose] public section

/-!
# Divine Proportions, Chapter 12 examples

Example 12.1 is a closed computation in the executable thirteen-element
field.  Example 12.2 uses exact Gaussian pairs over the project-owned
constructive rationals.  Only the literal points, lines, intersections, and
metric values printed by the source are evaluated; no field carrier is
enumerated.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterTwelve

namespace ChapterTwelveExamples

namespace ExampleTwelveOne

/-- The first vertex (3, 7) over the field with thirteen elements. -/
def first : Point Finite.Thirteen.Element := ⟨3, 7⟩
/-- The second vertex (−2, −4) over the field with thirteen elements. -/
def second : Point Finite.Thirteen.Element := ⟨-2, -4⟩
/-- The third vertex (5, 7) over the field with thirteen elements. -/
def third : Point Finite.Thirteen.Element := ⟨5, 7⟩
/-- The origin, the displayed incenter over the field with thirteen elements. -/
def incenterPoint : Point Finite.Thirteen.Element := ⟨0, 0⟩

/-- The three triangle vertices and the displayed incenter are pairwise distinct. -/
theorem point_distinctness :
    first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      first ≠ incenterPoint ∧ second ≠ incenterPoint ∧
      third ≠ incenterPoint := by
  decide

/-- The displayed triangle over the field with thirteen elements is noncollinear. -/
theorem triangle_noncollinear : ¬ Line.Incidence.Collinear first second third := by
  apply (Line.Incidence.collinear_iff_pointDeterminant_eq_zero first second third).not.mpr
  decide

/-- The line joining the first vertex to the displayed incenter. -/
def firstBisector : Line Finite.Thirteen.Element :=
  Line.Incidence.lineThrough first incenterPoint (by decide)

/-- The line joining the second vertex to the displayed incenter. -/
def secondBisector : Line Finite.Thirteen.Element :=
  Line.Incidence.lineThrough second incenterPoint (by decide)

/-- The line joining the third vertex to the displayed incenter. -/
def thirdBisector : Line Finite.Thirteen.Element :=
  Line.Incidence.lineThrough third incenterPoint (by decide)

/-- The side joining the first and second vertices. -/
def firstSide : Line Finite.Thirteen.Element := Line.Incidence.lineThrough first second (by decide)
/-- The side joining the second and third vertices. -/
def secondSide : Line Finite.Thirteen.Element := Line.Incidence.lineThrough second third (by decide)
/-- The side joining the third and first vertices. -/
def thirdSide : Line Finite.Thirteen.Element := Line.Incidence.lineThrough third first (by decide)

/-- All three displayed bisectors and all three triangle sides have nonzero norm. -/
theorem lines_nonNull :
    ¬ firstBisector.IsNull ∧ ¬ secondBisector.IsNull ∧
      ¬ thirdBisector.IsNull ∧ ¬ firstSide.IsNull ∧
      ¬ secondSide.IsNull ∧ ¬ thirdSide.IsNull := by
  unfold Line.IsNull firstBisector secondBisector thirdBisector firstSide
    secondSide thirdSide Line.Incidence.lineThrough first second third incenterPoint
  decide

/-- The first incenter bisector has nonzero norm. -/
private theorem firstBisector_nonNull : ¬ firstBisector.IsNull :=
  lines_nonNull.1

/-- The second incenter bisector has nonzero norm. -/
private theorem secondBisector_nonNull : ¬ secondBisector.IsNull :=
  lines_nonNull.2.1

/-- The third incenter bisector has nonzero norm. -/
private theorem thirdBisector_nonNull : ¬ thirdBisector.IsNull :=
  lines_nonNull.2.2.1

/-- The first triangle side has nonzero norm. -/
private theorem firstSide_nonNull : ¬ firstSide.IsNull :=
  lines_nonNull.2.2.2.1

/-- The second triangle side has nonzero norm. -/
private theorem secondSide_nonNull : ¬ secondSide.IsNull :=
  lines_nonNull.2.2.2.2.1

/-- The third triangle side has nonzero norm. -/
private theorem thirdSide_nonNull : ¬ thirdSide.IsNull :=
  lines_nonNull.2.2.2.2.2

/-- The three spreads `u₁=6`, `u₂=7`, and `u₃=4`. -/
theorem incenter_spread_values :
    Line.Spread.spread firstBisector firstSide lines_nonNull.1
        lines_nonNull.2.2.2.1 = 6 ∧
      Line.Spread.spread secondBisector secondSide lines_nonNull.2.1
          lines_nonNull.2.2.2.2.1 = 7 ∧
      Line.Spread.spread thirdBisector thirdSide lines_nonNull.2.2.1
          lines_nonNull.2.2.2.2.2 = 4 := by
  decide

/-- The three literal Triple-spread checks requested by the example. -/
theorem displayed_spread_triples :
    SpreadTriple (6 : Finite.Thirteen.Element) 7 (-3) ∧
      SpreadTriple (-5 : Finite.Thirteen.Element) 7 4 ∧
      SpreadTriple (6 : Finite.Thirteen.Element) (-6) 4 := by
  unfold SpreadTriple
    Geometry.Trigonometry.Spread.Triple.TripleSpread.tripleSpreadFunction
  decide

/-- The two displayed lines used to calculate `r₁`. -/
def displayedFirstBisector : Line Finite.Thirteen.Element where
  a := 2
  b := 1
  c := 0
  direction_nonzero := Or.inl (by decide)

/-- The opposite-side representative with coefficients (4, 1, −1). -/
def displayedOppositeSide : Line Finite.Thirteen.Element where
  a := 4
  b := 1
  c := -1
  direction_nonzero := Or.inl (by decide)

/-- The printed bisector and opposite-side representatives are equivalent to their geometric constructions. -/
theorem displayed_lines_match_geometry :
    displayedFirstBisector.Equivalent firstBisector ∧
      displayedOppositeSide.Equivalent secondSide := by
  unfold Line.Equivalent displayedFirstBisector displayedOppositeSide
    firstBisector secondSide Line.Incidence.lineThrough first second third incenterPoint
  decide

/-- The printed first bisector has nonzero norm. -/
private theorem displayedFirstBisector_nonNull :
    ¬ displayedFirstBisector.IsNull := by
  unfold Line.IsNull displayedFirstBisector
  decide

/-- The printed opposite side has nonzero norm. -/
private theorem displayedOppositeSide_nonNull :
    ¬ displayedOppositeSide.IsNull := by
  unfold Line.IsNull displayedOppositeSide
  decide

/-- The printed spread `r₁=8`, together with the quotient from Exercise
12.7 evaluated on `u₁=6,u₂=7,u₃=4`. -/
theorem first_opposite_spread :
    Line.Spread.spread displayedFirstBisector displayedOppositeSide
        (by unfold Line.IsNull displayedFirstBisector; decide)
        (by unfold Line.IsNull displayedOppositeSide; decide) = 8 ∧
      ((6 : Finite.Thirteen.Element) - 2 * 7 - 2 * 4 + 2 * 7 ^ 2 + 2 * 4 ^ 2) /
          (2 * 6 - 1) = 8 := by
  decide

end ExampleTwelveOne

namespace ExampleTwelveTwo

/-- The first Gaussian vertex (1, 1 + i). -/
def first : Point Gaussian.Basic.Canonical :=
  ⟨Construction.displayedGaussian 1 0 0 0, Construction.displayedGaussian 1 0 1 0⟩

/-- The second Gaussian vertex (1 − i, −2i). -/
def second : Point Gaussian.Basic.Canonical :=
  ⟨Construction.displayedGaussian 1 0 (-1) 0, Construction.displayedGaussian 0 0
    (-2) 0⟩

/-- The third Gaussian vertex with the retained displayed rational real and imaginary coordinates. -/
def third : Point Gaussian.Basic.Canonical :=
  ⟨Construction.displayedGaussian (-16) 38 20 116, Construction.displayedGaussian 46
    116 (-10) 38⟩

/-- The Gaussian origin, the displayed incenter. -/
def incenterPoint : Point Gaussian.Basic.Canonical :=
  ⟨Construction.displayedGaussian 0 0 0 0, Construction.displayedGaussian 0 0 0 0⟩

/-- The three Gaussian vertices and the displayed incenter are pairwise distinct. -/
theorem point_distinctness :
    first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      first ≠ incenterPoint ∧ second ≠ incenterPoint ∧
      third ≠ incenterPoint := by
  decide

/-- The displayed Gaussian triangle is noncollinear. -/
theorem triangle_noncollinear : ¬ Line.Incidence.Collinear first second third := by
  apply (Line.Incidence.collinear_iff_pointDeterminant_eq_zero first second third).not.mpr
  unfold Line.Incidence.pointDeterminant first second third
  decide

/-- The first and second Gaussian vertices are distinct. -/
private theorem firstSecondDistinct : first ≠ second :=
  point_distinctness.1

/-- The first and third Gaussian vertices are distinct. -/
private theorem firstThirdDistinct : first ≠ third :=
  point_distinctness.2.1

/-- The second and third Gaussian vertices are distinct. -/
private theorem secondThirdDistinct : second ≠ third :=
  point_distinctness.2.2.1

/-- The Gaussian side joining the first and second vertices. -/
def firstSide : Line Gaussian.Basic.Canonical :=
  Line.Incidence.lineThrough first second point_distinctness.1

/-- The Gaussian side joining the second and third vertices. -/
def secondSide : Line Gaussian.Basic.Canonical :=
  Line.Incidence.lineThrough second third point_distinctness.2.2.1

/-- The Gaussian side joining the third and first vertices. -/
def thirdSide : Line Gaussian.Basic.Canonical :=
  Line.Incidence.lineThrough third first point_distinctness.2.1.symm

/-- All three Gaussian triangle sides have nonzero norm. -/
theorem sides_nonNull :
    ¬ firstSide.IsNull ∧ ¬ secondSide.IsNull ∧
      ¬ thirdSide.IsNull := by
  unfold Line.IsNull firstSide secondSide thirdSide Line.Incidence.lineThrough first second
    third
  decide

/-- The first Gaussian triangle side has nonzero norm. -/
private theorem firstSide_nonNull : ¬ firstSide.IsNull :=
  sides_nonNull.1

/-- The second Gaussian triangle side has nonzero norm. -/
private theorem secondSide_nonNull : ¬ secondSide.IsNull :=
  sides_nonNull.2.1

/-- The third Gaussian triangle side has nonzero norm. -/
private theorem thirdSide_nonNull : ¬ thirdSide.IsNull :=
  sides_nonNull.2.2

/-- The Gaussian line joining the first vertex to the origin. -/
def firstBisector : Line Gaussian.Basic.Canonical :=
  Line.Incidence.lineThrough first incenterPoint point_distinctness.2.2.2.1

/-- The Gaussian line joining the second vertex to the origin. -/
def secondBisector : Line Gaussian.Basic.Canonical :=
  Line.Incidence.lineThrough second incenterPoint point_distinctness.2.2.2.2.1

/-- The Gaussian line joining the third vertex to the origin. -/
def thirdBisector : Line Gaussian.Basic.Canonical :=
  Line.Incidence.lineThrough third incenterPoint point_distinctness.2.2.2.2.2

/-- All three Gaussian origin bisectors have nonzero norm. -/
theorem bisectors_nonNull :
    ¬ firstBisector.IsNull ∧ ¬ secondBisector.IsNull ∧
      ¬ thirdBisector.IsNull := by
  unfold Line.IsNull firstBisector secondBisector thirdBisector Line.Incidence.lineThrough
    first second third incenterPoint
  decide

/-- The first Gaussian origin bisector has nonzero norm. -/
private theorem firstBisector_nonNull : ¬ firstBisector.IsNull :=
  bisectors_nonNull.1

/-- The second Gaussian origin bisector has nonzero norm. -/
private theorem secondBisector_nonNull : ¬ secondBisector.IsNull :=
  bisectors_nonNull.2.1

/-- The third Gaussian origin bisector has nonzero norm. -/
private theorem thirdBisector_nonNull : ¬ thirdBisector.IsNull :=
  bisectors_nonNull.2.2

/-- The three displayed bisector representatives meeting at the origin. -/
def displayedFirstBisector : Line Gaussian.Basic.Canonical where
  a := Construction.displayedGaussian 1 0 1 0
  b := Construction.displayedGaussian (-1) 0 0 0
  c := Construction.displayedGaussian 0 0 0 0
  direction_nonzero := Or.inl (by decide)

/-- The second displayed origin bisector with coefficients (2i, 1 − i, 0). -/
def displayedSecondBisector : Line Gaussian.Basic.Canonical where
  a := Construction.displayedGaussian 0 0 2 0
  b := Construction.displayedGaussian 1 0 (-1) 0
  c := Construction.displayedGaussian 0 0 0 0
  direction_nonzero := Or.inl (by decide)

/-- The third displayed origin bisector with coefficients (46 − 30i, 48 − 20i, 0). -/
def displayedThirdBisector : Line Gaussian.Basic.Canonical where
  a := Construction.displayedGaussian 46 0 (-30) 0
  b := Construction.displayedGaussian 48 0 (-20) 0
  c := Construction.displayedGaussian 0 0 0 0
  direction_nonzero := Or.inl (by decide)

/-- The three other displayed vertex bisectors, perpendicular to the first
three respectively. -/
def displayedFirstOtherBisector : Line Gaussian.Basic.Canonical where
  a := Construction.displayedGaussian 1 0 0 0
  b := Construction.displayedGaussian 1 0 1 0
  c := Construction.displayedGaussian (-1) 0 (-2) 0
  direction_nonzero := Or.inl (by decide)

/-- The second perpendicular bisector representative with coefficients (1 − i, −2i, 4 + 2i). -/
def displayedSecondOtherBisector : Line Gaussian.Basic.Canonical where
  a := Construction.displayedGaussian 1 0 (-1) 0
  b := Construction.displayedGaussian 0 0 (-2) 0
  c := Construction.displayedGaussian 4 0 2 0
  direction_nonzero := Or.inl (by decide)

/-- The third perpendicular bisector representative with coefficients (72 − 30i, −69 + 45i, 40 − 60i). -/
def displayedThirdOtherBisector : Line Gaussian.Basic.Canonical where
  a := Construction.displayedGaussian 72 0 (-30) 0
  b := Construction.displayedGaussian (-69) 0 45 0
  c := Construction.displayedGaussian 40 0 (-60) 0
  direction_nonzero := Or.inl (by decide)

/-- The displayed `hᵢ` representatives agree with the lines from the three
vertices to the origin. -/
theorem displayed_bisectors_match_geometry :
    displayedFirstBisector.Equivalent firstBisector ∧
      displayedSecondBisector.Equivalent secondBisector ∧
      displayedThirdBisector.Equivalent thirdBisector := by
  unfold Line.Equivalent displayedFirstBisector displayedSecondBisector
    displayedThirdBisector firstBisector secondBisector thirdBisector
    Line.Incidence.lineThrough first second third incenterPoint
  constructor
  · constructor
    · apply Gaussian.Basic.ext <;> decide
    · constructor
      · apply Gaussian.Basic.ext <;> decide
      · apply Gaussian.Basic.ext <;> decide
  · constructor
    · constructor
      · apply Gaussian.Basic.ext <;> decide
      · constructor
        · apply Gaussian.Basic.ext <;> decide
        · apply Gaussian.Basic.ext <;> decide
    · constructor
      · apply Gaussian.Basic.ext <;> decide
      · constructor
        · apply Gaussian.Basic.ext <;> decide
        · apply Gaussian.Basic.ext <;> decide

/-- The three printed `jᵢ` lines contain the appropriate vertices and are
perpendicular to their corresponding `hᵢ` lines. -/
theorem other_bisectors_geometry :
    displayedFirstOtherBisector.Contains first ∧
      displayedSecondOtherBisector.Contains second ∧
      displayedThirdOtherBisector.Contains third ∧
      displayedFirstBisector.Perpendicular displayedFirstOtherBisector ∧
      displayedSecondBisector.Perpendicular displayedSecondOtherBisector ∧
      displayedThirdBisector.Perpendicular displayedThirdOtherBisector := by
  unfold Line.Contains Line.Perpendicular displayedFirstBisector
    displayedSecondBisector displayedThirdBisector
    displayedFirstOtherBisector displayedSecondOtherBisector
    displayedThirdOtherBisector first second third
  constructor
  · apply Gaussian.Basic.ext <;> decide
  · constructor
    · apply Gaussian.Basic.ext <;> decide
    · constructor
      · apply Gaussian.Basic.ext <;> decide
      · constructor
        · apply Gaussian.Basic.ext <;> decide
        · constructor
          · apply Gaussian.Basic.ext <;> decide
          · apply Gaussian.Basic.ext <;> decide

/-- The first other Gaussian incenter with its exact displayed rational coordinates. -/
def firstOtherIncenter : Point Gaussian.Basic.Canonical :=
  ⟨Construction.displayedGaussian (-1) 2 (-1) 0, Construction.displayedGaussian 2 2
    (-4) 2⟩

/-- The second other Gaussian incenter with its exact displayed rational coordinates. -/
def secondOtherIncenter : Point Gaussian.Basic.Canonical :=
  ⟨Construction.displayedGaussian 1 2 2 2, Construction.displayedGaussian 1 0 1 2⟩

/-- The third other Gaussian incenter with its exact displayed rational coordinates. -/
def thirdOtherIncenter : Point Gaussian.Basic.Canonical :=
  ⟨Construction.displayedGaussian (-5) 1 1 1, Construction.displayedGaussian 5 1
    (-1) 0⟩

/-- The first origin bisector and second other bisector are not parallel. -/
private theorem first_secondOther_nonparallel :
    ¬ displayedFirstBisector.Parallel displayedSecondOtherBisector := by
  unfold Line.Parallel displayedFirstBisector displayedSecondOtherBisector
  decide

/-- The first origin bisector and third other bisector are not parallel. -/
private theorem first_thirdOther_nonparallel :
    ¬ displayedFirstBisector.Parallel displayedThirdOtherBisector := by
  unfold Line.Parallel displayedFirstBisector displayedThirdOtherBisector
  decide

/-- The second origin bisector and first other bisector are not parallel. -/
private theorem second_firstOther_nonparallel :
    ¬ displayedSecondBisector.Parallel displayedFirstOtherBisector := by
  unfold Line.Parallel displayedSecondBisector
      displayedFirstOtherBisector
  decide

/-- The second origin bisector and third other bisector are not parallel. -/
private theorem second_thirdOther_nonparallel :
    ¬ displayedSecondBisector.Parallel displayedThirdOtherBisector := by
  unfold Line.Parallel displayedSecondBisector
      displayedThirdOtherBisector
  decide

/-- The third origin bisector and first other bisector are not parallel. -/
private theorem third_firstOther_nonparallel :
    ¬ displayedThirdBisector.Parallel displayedFirstOtherBisector := by
  unfold Line.Parallel displayedThirdBisector
      displayedFirstOtherBisector
  decide

/-- The third origin bisector and second other bisector are not parallel. -/
private theorem third_secondOther_nonparallel :
    ¬ displayedThirdBisector.Parallel displayedSecondOtherBisector := by
  unfold Line.Parallel displayedThirdBisector
      displayedSecondOtherBisector
  decide

/-- All six line intersections printed for the three other incenters. -/
theorem displayed_other_incenter_intersections :
    Line.Intersection.lineIntersection displayedFirstBisector displayedSecondOtherBisector
        (by
          unfold Line.Parallel displayedFirstBisector displayedSecondOtherBisector
          decide) = firstOtherIncenter ∧
      Line.Intersection.lineIntersection displayedFirstBisector displayedThirdOtherBisector
          (by
            unfold Line.Parallel displayedFirstBisector displayedThirdOtherBisector
            decide) = firstOtherIncenter ∧
      Line.Intersection.lineIntersection displayedSecondBisector
        displayedFirstOtherBisector
          (by
            unfold Line.Parallel displayedSecondBisector
              displayedFirstOtherBisector
            decide) = secondOtherIncenter ∧
      Line.Intersection.lineIntersection displayedSecondBisector
        displayedThirdOtherBisector
          (by
            unfold Line.Parallel displayedSecondBisector
              displayedThirdOtherBisector
            decide) = secondOtherIncenter ∧
      Line.Intersection.lineIntersection displayedThirdBisector
        displayedFirstOtherBisector
          (by
            unfold Line.Parallel displayedThirdBisector
              displayedFirstOtherBisector
            decide) = thirdOtherIncenter ∧
      Line.Intersection.lineIntersection displayedThirdBisector
        displayedSecondOtherBisector
          (by
            unfold Line.Parallel displayedThirdBisector
              displayedSecondOtherBisector
            decide) = thirdOtherIncenter := by
  constructor
  · apply Geometry.Plane.Point.ext <;>
      apply Gaussian.Basic.ext <;> decide
  · constructor
    · apply Geometry.Plane.Point.ext <;>
        apply Gaussian.Basic.ext <;> decide
    · constructor
      · apply Geometry.Plane.Point.ext <;>
          apply Gaussian.Basic.ext <;> decide
      · constructor
        · apply Geometry.Plane.Point.ext <;>
            apply Gaussian.Basic.ext <;> decide
        · constructor
          · apply Geometry.Plane.Point.ext <;>
              apply Gaussian.Basic.ext <;> decide
          · apply Geometry.Plane.Point.ext <;>
              apply Gaussian.Basic.ext <;> decide

/-- The displayed common side quadrance at the Gaussian origin. -/
def firstInquadrance : Gaussian.Basic.Canonical := Construction.displayedGaussian 16 38 (-8) 12
/-- The displayed common side quadrance at the first other Gaussian incenter. -/
def secondInquadrance : Gaussian.Basic.Canonical := Construction.displayedGaussian 688 350 8 12
/-- The displayed common side quadrance at the second other Gaussian incenter. -/
def thirdInquadrance : Gaussian.Basic.Canonical := Construction.displayedGaussian (-92) 350 (-136) 116
/-- The displayed common side quadrance at the third other Gaussian incenter. -/
def fourthInquadrance : Gaussian.Basic.Canonical := Construction.displayedGaussian 2287 155 (-211) 25

/-- A displayed point has a common inquadrance value when its quadrance to
each of the three triangle sides is that value. -/
def HasCommonInquadrance (point : Point Gaussian.Basic.Canonical) (value : Gaussian.Basic.Canonical) :
    Prop
  :=
  Line.Quadrance.pointLineQuadrance point firstSide sides_nonNull.1 = value ∧
    Line.Quadrance.pointLineQuadrance point secondSide sides_nonNull.2.1 = value ∧
    Line.Quadrance.pointLineQuadrance point thirdSide sides_nonNull.2.2 = value

/-- The four common inquadrances printed at the end of Example 12.2. -/
theorem displayed_inquadrance_values :
    HasCommonInquadrance incenterPoint firstInquadrance ∧
      HasCommonInquadrance firstOtherIncenter secondInquadrance ∧
      HasCommonInquadrance secondOtherIncenter thirdInquadrance ∧
      HasCommonInquadrance thirdOtherIncenter fourthInquadrance := by
  unfold HasCommonInquadrance
  repeat' apply And.intro
  all_goals rw [Line.Quadrance.pointLineQuadrance_formula]
  all_goals apply Gaussian.Basic.ext <;> decide

/-- The displayed Gaussian quadrea of the triangle, with exact rational components. -/
def printedQuadrea : Gaussian.Basic.Canonical :=
  Construction.displayedGaussian (-99328) 13688 400768 4562

/-- The displayed Gaussian circumquadrance of the triangle, with exact rational components. -/
def printedCircumquadrance : Gaussian.Basic.Canonical :=
  Construction.displayedGaussian 25 63 (-25) 95

/-- The displayed value is the circumquadrance of the explicit finite
circumcenter construction, not merely a solution of the cleared identity. -/
theorem circumquadrance_value :
    Circumcenter.Basic.circumquadrance first second third point_distinctness.2.1
        point_distinctness.2.2.1
        triangle_noncollinear = printedCircumquadrance := by
  unfold Circumcenter.Basic.circumquadrance Circumcenter.Basic.circumcenterPoint
    Line.PerpendicularBisector.perpendicularBisector
    Line.Intersection.lineIntersection Point.Quadrance.quadrance printedCircumquadrance
  apply Gaussian.Basic.ext <;> decide

/-- The first displayed incenter spread, with real part −32/194 and imaginary part −56/194. -/
def firstSpread : Gaussian.Basic.Canonical := Construction.displayedGaussian (-32) 194 (-56) 194
/-- The second displayed incenter spread, with real part −4/194 and imaginary part 32/194. -/
def secondSpread : Gaussian.Basic.Canonical := Construction.displayedGaussian (-4) 194 32 194
/-- The third displayed incenter spread, equal to 9/4. -/
def thirdSpread : Gaussian.Basic.Canonical := Construction.displayedGaussian 9 4 0 0

/-- The three displayed spreads are the actual spreads made by the origin
bisectors with the cyclic triangle sides. -/
theorem incenter_spread_values :
    Line.Spread.spread firstBisector firstSide bisectors_nonNull.1 sides_nonNull.1 =
        firstSpread ∧
      Line.Spread.spread secondBisector secondSide bisectors_nonNull.2.1
          sides_nonNull.2.1 = secondSpread ∧
      Line.Spread.spread thirdBisector thirdSide bisectors_nonNull.2.2
          sides_nonNull.2.2 = thirdSpread := by
  constructor
  · apply Gaussian.Basic.ext <;> decide
  · constructor
    · apply Gaussian.Basic.ext <;> decide
    · apply Gaussian.Basic.ext <;> decide

/-- The source's two main scalar checks for Example 12.2. -/
theorem quadrea_and_circumquadrea_values :
    Quadrea.Basic.quadrea first second third = printedQuadrea ∧
      Quadrea.Basic.quadrea first second third * printedCircumquadrance =
        Point.Quadrance.quadrance second third * Point.Quadrance.quadrance first third *
          Point.Quadrance.quadrance first second := by
  constructor
  · apply Gaussian.Basic.ext <;> decide
  · apply Gaussian.Basic.ext <;> decide +kernel

/-- The literal values check both the Inquadrance theorem and Exercise
12.8's four-incenter product formula. -/
theorem displayed_inquadrance_formula_checks :
    firstInquadrance =
        16 * printedCircumquadrance * firstSpread * secondSpread *
          thirdSpread ∧
      firstInquadrance * secondInquadrance * thirdInquadrance *
          fourthInquadrance = (printedQuadrea / 16) ^ 2 := by
  constructor
  · apply Gaussian.Basic.ext <;> decide
  · apply Gaussian.Basic.ext <;> decide +kernel

/-- The three printed half-angle spreads satisfy exactly the three
complemented Triple-spread equations used in the Incenter-spread proof. -/
theorem spread_triples :
    SpreadTriple firstSpread
      secondSpread (1 - thirdSpread) ∧
      SpreadTriple firstSpread (1 -
        secondSpread) thirdSpread ∧
      SpreadTriple (1 - firstSpread)
        secondSpread thirdSpread := by
  unfold SpreadTriple
    Geometry.Trigonometry.Spread.Triple.TripleSpread.tripleSpreadFunction firstSpread
    secondSpread
    thirdSpread Construction.displayedGaussian
  constructor
  · apply Gaussian.Basic.ext <;> decide
  · constructor
    · apply Gaussian.Basic.ext <;> decide
    · apply Gaussian.Basic.ext <;> decide

end ExampleTwelveTwo

end ChapterTwelveExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterTwelve

end
