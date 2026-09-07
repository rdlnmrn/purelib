import DivineProportions.Algebra.FieldEleven
import DivineProportions.Algebra.FieldThirteen
import DivineProportions.Conics.Circle
import mathlib.Data.ConstructiveList

/-!
# Divine Proportions, Example 15.2 and Exercise 15.3

The two source figures are retained as literal finite coordinate grids.  Their
entries are checked against central quadrance, and filtering the displayed
points by a quadrance label gives the printed circle counts.  These are finite
display certificates: they do not assert that either coordinate list globally
enumerates an ambient field carrier.
-/

namespace DivineProportions

namespace ChapterFifteenCentralCircles

variable {K : Type*} [RFAP.ExplicitField K]

/-- The row of displayed points with a fixed second coordinate. -/
def pointRow (xCoordinates : List K) (yCoordinate : K) : List (Point K) :=
  xCoordinates.map fun xCoordinate => ⟨xCoordinate, yCoordinate⟩

/-- The literal Cartesian grid obtained from the displayed coordinate labels. -/
def pointRows (xCoordinates yCoordinates : List K) : List (List (Point K)) :=
  yCoordinates.map fun yCoordinate => pointRow xCoordinates yCoordinate

omit [RFAP.ExplicitField K] in
/-- Distinct horizontal and vertical labels produce distinct displayed grid
points, without a carrier enumeration. -/
theorem pointRows_flatten_nodup [DecidableEq K]
    {xCoordinates yCoordinates : List K}
    (xNodup : xCoordinates.Nodup) (yNodup : yCoordinates.Nodup) :
    (pointRows xCoordinates yCoordinates).flatten.Nodup := by
  change
    (yCoordinates.flatMap fun yCoordinate =>
      pointRow xCoordinates yCoordinate).Nodup
  induction yCoordinates with
  | nil => exact List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      rcases List.pairwise_cons.mp yNodup with
        ⟨headFresh, tailNodup⟩
      change
        (pointRow xCoordinates head ++
          tail.flatMap fun yCoordinate =>
            pointRow xCoordinates yCoordinate).Nodup
      apply QuotientFreeList.nodup_append
      · unfold pointRow
        exact QuotientFreeList.nodup_map_of_injective
          (fun _ _ pointsEqual => congrArg Point.x pointsEqual) xNodup
      · exact inductionHypothesis tailNodup
      · intro firstPoint firstMembership secondPoint secondMembership pointsEqual
        rcases QuotientFreeList.mem_map.mp firstMembership with
          ⟨_, _, firstPointEqual⟩
        rcases QuotientFreeList.mem_flatMap.mp secondMembership with
          ⟨otherY, otherYMembership, secondRowMembership⟩
        rcases QuotientFreeList.mem_map.mp secondRowMembership with
          ⟨_, _, secondPointEqual⟩
        apply headFresh otherY otherYMembership
        calc
          head = firstPoint.y := congrArg Point.y firstPointEqual
          _ = secondPoint.y := congrArg Point.y pointsEqual
          _ = otherY := (congrArg Point.y secondPointEqual).symm

/-- Evaluate central quadrance on every row of a displayed point grid. -/
def centralQuadranceRows (center : Point K)
    (rows : List (List (Point K))) : List (List K) :=
  rows.map fun row => row.map fun point => quadrance point center

/-- The points in one displayed row carrying a requested central-circle label. -/
def displayedCirclePoints [DecidableEq K] (center : Point K)
    (row : List (Point K)) (circleQuadrance : K) : List (Point K) :=
  row.filter fun point =>
    decide (quadrance point center = circleQuadrance)

/-- Filter every displayed row by one requested central-circle label. -/
def displayedCirclePointRows [DecidableEq K] (center : Point K)
    (rows : List (List (Point K)))
    (circleQuadrance : K) : List (List (Point K)) :=
  rows.map fun row => displayedCirclePoints center row circleQuadrance

/-- Sum the finitely many row lengths in one displayed circle. -/
def displayedCircleCount [DecidableEq K] (center : Point K)
    (rows : List (List (Point K))) (circleQuadrance : K) : Nat :=
  (displayedCirclePointRows center rows circleQuadrance).foldl
    (fun count row => count + row.length) 0

/-- The finite point counts attached to a list of displayed circle labels. -/
def displayedCircleCounts [DecidableEq K] (center : Point K)
    (rows : List (List (Point K))) (circleQuadrances : List K) : List Nat :=
  circleQuadrances.map fun circleQuadrance =>
    displayedCircleCount center rows circleQuadrance

/-- A source figure is certified by its exact quadrance table, a duplicate-free
point grid and label list, and the requested finite count for every label. -/
def CentralCircleDisplayCertified [DecidableEq K]
    (center : Point K) (rows : List (List (Point K)))
    (valueRows : List (List K)) (circleQuadrances : List K)
    (counts : List Nat) : Prop :=
  centralQuadranceRows center rows = valueRows ∧
    rows.flatten.Nodup ∧
    circleQuadrances.Nodup ∧
    displayedCircleCounts center rows circleQuadrances = counts

/-- Every filtered point is incident with the normalized circle carrying its
filter label. -/
theorem displayedCirclePoint_contains [DecidableEq K] [Nontrivial K]
    (center point : Point K) (row : List (Point K))
    (circleQuadrance : K)
    (membership : point ∈ displayedCirclePoints center row circleQuadrance) :
    (Conic.circleConic center circleQuadrance).Contains point := by
  apply (Conic.contains_iff_quadrance_eq
    (Conic.circleConic center circleQuadrance) center point
    circleQuadrance
    (Conic.circleConic_isCirclePresentation center circleQuadrance)).2
  unfold displayedCirclePoints at membership
  exact of_decide_eq_true ((List.mem_filter.mp membership).2)

/-- Every normalized circle centered at the origin is central in the source's
coefficient sense. -/
theorem circleConic_origin_isCentral [Nontrivial K] (circleQuadrance : K) :
    (Conic.circleConic (⟨0, 0⟩ : Point K) circleQuadrance).IsCentral := by
  unfold Conic.IsCentral Conic.IsCenter Conic.circleConic
  constructor <;> ring1

namespace ExampleFifteenTwo

/-- The executable coefficient field used in Figure 15.1. -/
abbrev F₁₁ := FieldEleven.Element

/-- The displayed origin. -/
def origin : Point F₁₁ := ⟨0, 0⟩

/-- Figure 15.1's horizontal coordinate labels, from `-5` through `5`. -/
def xCoordinates : List F₁₁ :=
  [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]

/-- Figure 15.1's vertical coordinate labels, from `5` through `-5`. -/
def yCoordinates : List F₁₁ :=
  [5, 4, 3, 2, 1, 0, -1, -2, -3, -4, -5]

/-- The 121 literal point positions in Figure 15.1, retained row by row. -/
def displayedPointRows : List (List (Point F₁₁)) :=
  pointRows xCoordinates yCoordinates

/-- The eleven rows of central quadrances printed in Figure 15.1. -/
def displayedValueRows : List (List F₁₁) :=
  [ [6, 8, 1, 7, 4, 3, 4, 7, 1, 8, 6],
    [8, 10, 3, 9, 6, 5, 6, 9, 3, 10, 8],
    [1, 3, 7, 2, 10, 9, 10, 2, 7, 3, 1],
    [7, 9, 2, 8, 5, 4, 5, 8, 2, 9, 7],
    [4, 6, 10, 5, 2, 1, 2, 5, 10, 6, 4],
    [3, 5, 9, 4, 1, 0, 1, 4, 9, 5, 3],
    [4, 6, 10, 5, 2, 1, 2, 5, 10, 6, 4],
    [7, 9, 2, 8, 5, 4, 5, 8, 2, 9, 7],
    [1, 3, 7, 2, 10, 9, 10, 2, 7, 3, 1],
    [8, 10, 3, 9, 6, 5, 6, 9, 3, 10, 8],
    [6, 8, 1, 7, 4, 3, 4, 7, 1, 8, 6] ]

/-- The eleven central-circle labels in Figure 15.1. -/
def circleQuadrances : List F₁₁ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- The point count printed for the null circle followed by the ten non-null
circles. -/
def circlePointCounts : List Nat :=
  [1, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12]

/-- Example 15.2: Figure 15.1 is the exact central-quadrance table over the
displayed `F₁₁` labels, its 121 positions are duplicate-free, and the
null/non-null circle filters have respectively one and twelve points. -/
theorem example_15_2 :
    CentralCircleDisplayCertified origin displayedPointRows
      displayedValueRows circleQuadrances circlePointCounts := by
  unfold CentralCircleDisplayCertified
  constructor
  · unfold centralQuadranceRows displayedPointRows pointRows pointRow origin
      xCoordinates yCoordinates displayedValueRows quadrance
    decide
  constructor
  · unfold displayedPointRows
    apply pointRows_flatten_nodup
    · unfold xCoordinates
      decide
    · unfold yCoordinates
      decide
  constructor
  · unfold circleQuadrances
    decide
  · unfold displayedCircleCounts displayedCircleCount
      displayedCirclePointRows displayedCirclePoints displayedPointRows
      pointRows pointRow origin xCoordinates yCoordinates circleQuadrances
      circlePointCounts quadrance
    decide

end ExampleFifteenTwo

namespace ExerciseFifteenThree

/-- The executable coefficient field used in Figure 15.3. -/
abbrev F₁₃ := FieldThirteen.Element

/-- The displayed origin. -/
def origin : Point F₁₃ := ⟨0, 0⟩

/-- Figure 15.3's horizontal coordinate labels, from `-6` through `6`. -/
def xCoordinates : List F₁₃ :=
  [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6]

/-- Figure 15.3's vertical coordinate labels, from `6` through `-6`. -/
def yCoordinates : List F₁₃ :=
  [6, 5, 4, 3, 2, 1, 0, -1, -2, -3, -4, -5, -6]

/-- The 169 literal point positions in Figure 15.3, retained row by row. -/
def displayedPointRows : List (List (Point F₁₃)) :=
  pointRows xCoordinates yCoordinates

/-- The thirteen rows of central quadrances printed in Figure 15.3. -/
def displayedValueRows : List (List F₁₃) :=
  [ [7, 9, 0, 6, 1, 11, 10, 11, 1, 6, 0, 9, 7],
    [9, 11, 2, 8, 3, 0, 12, 0, 3, 8, 2, 11, 9],
    [0, 2, 6, 12, 7, 4, 3, 4, 7, 12, 6, 2, 0],
    [6, 8, 12, 5, 0, 10, 9, 10, 0, 5, 12, 8, 6],
    [1, 3, 7, 0, 8, 5, 4, 5, 8, 0, 7, 3, 1],
    [11, 0, 4, 10, 5, 2, 1, 2, 5, 10, 4, 0, 11],
    [10, 12, 3, 9, 4, 1, 0, 1, 4, 9, 3, 12, 10],
    [11, 0, 4, 10, 5, 2, 1, 2, 5, 10, 4, 0, 11],
    [1, 3, 7, 0, 8, 5, 4, 5, 8, 0, 7, 3, 1],
    [6, 8, 12, 5, 0, 10, 9, 10, 0, 5, 12, 8, 6],
    [0, 2, 6, 12, 7, 4, 3, 4, 7, 12, 6, 2, 0],
    [9, 11, 2, 8, 3, 0, 12, 0, 3, 8, 2, 11, 9],
    [7, 9, 0, 6, 1, 11, 10, 11, 1, 6, 0, 9, 7] ]

/-- The thirteen central-circle labels in Figure 15.3. -/
def circleQuadrances : List F₁₃ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- The point count printed for the null circle followed by the twelve
non-null circles. -/
def circlePointCounts : List Nat :=
  [25, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12]

/-- Exercise 15.3: Figure 15.3 is the exact central-quadrance table over the
displayed `F₁₃` labels, its 169 positions are duplicate-free, and the
null/non-null circle filters have respectively twenty-five and twelve points. -/
theorem exercise_15_3 :
    CentralCircleDisplayCertified origin displayedPointRows
      displayedValueRows circleQuadrances circlePointCounts := by
  unfold CentralCircleDisplayCertified
  constructor
  · unfold centralQuadranceRows displayedPointRows pointRows pointRow origin
      xCoordinates yCoordinates displayedValueRows quadrance
    decide
  constructor
  · unfold displayedPointRows
    apply pointRows_flatten_nodup
    · unfold xCoordinates
      decide
    · unfold yCoordinates
      decide
  constructor
  · unfold circleQuadrances
    decide
  · unfold displayedCircleCounts displayedCircleCount
      displayedCirclePointRows displayedCirclePoints displayedPointRows
      pointRows pointRow origin xCoordinates yCoordinates circleQuadrances
      circlePointCounts quadrance
    decide

end ExerciseFifteenThree

end ChapterFifteenCentralCircles

end DivineProportions
