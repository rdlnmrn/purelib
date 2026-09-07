import DivineProportions.Centers.ChapterTwelveExercises
import DivineProportions.Algebra.FieldThirteen
import mathlib.RFAP.ConstructiveGaussian

/-!
# Divine Proportions, Chapter 12 examples

Example 12.1 is a closed computation in the executable thirteen-element
field.  Example 12.2 uses exact Gaussian pairs over the project-owned
constructive rationals.  Only the literal points, lines, intersections, and
metric values printed by the source are evaluated; no field carrier is
enumerated.
-/

namespace DivineProportions

namespace ChapterTwelveExamples

namespace ExampleTwelveOne

abbrev F₁₃ := FieldThirteen.Element

def first : Point F₁₃ := ⟨3, 7⟩
def second : Point F₁₃ := ⟨-2, -4⟩
def third : Point F₁₃ := ⟨5, 7⟩
def incenterPoint : Point F₁₃ := ⟨0, 0⟩

theorem point_distinctness :
    first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      first ≠ incenterPoint ∧ second ≠ incenterPoint ∧
      third ≠ incenterPoint := by
  decide

theorem triangle_noncollinear : ¬ Collinear first second third := by
  apply (collinear_iff_pointDeterminant_eq_zero first second third).not.mpr
  decide

def firstBisector : Line F₁₃ :=
  lineThrough first incenterPoint (by decide)

def secondBisector : Line F₁₃ :=
  lineThrough second incenterPoint (by decide)

def thirdBisector : Line F₁₃ :=
  lineThrough third incenterPoint (by decide)

def firstSide : Line F₁₃ := lineThrough first second (by decide)
def secondSide : Line F₁₃ := lineThrough second third (by decide)
def thirdSide : Line F₁₃ := lineThrough third first (by decide)

theorem lines_nonNull :
    ¬ firstBisector.IsNull ∧ ¬ secondBisector.IsNull ∧
      ¬ thirdBisector.IsNull ∧ ¬ firstSide.IsNull ∧
      ¬ secondSide.IsNull ∧ ¬ thirdSide.IsNull := by
  unfold Line.IsNull firstBisector secondBisector thirdBisector firstSide
    secondSide thirdSide lineThrough first second third incenterPoint
  decide

private theorem firstBisector_nonNull : ¬ firstBisector.IsNull :=
  lines_nonNull.1

private theorem secondBisector_nonNull : ¬ secondBisector.IsNull :=
  lines_nonNull.2.1

private theorem thirdBisector_nonNull : ¬ thirdBisector.IsNull :=
  lines_nonNull.2.2.1

private theorem firstSide_nonNull : ¬ firstSide.IsNull :=
  lines_nonNull.2.2.2.1

private theorem secondSide_nonNull : ¬ secondSide.IsNull :=
  lines_nonNull.2.2.2.2.1

private theorem thirdSide_nonNull : ¬ thirdSide.IsNull :=
  lines_nonNull.2.2.2.2.2

/-- The three spreads `u₁=6`, `u₂=7`, and `u₃=4`. -/
theorem incenter_spread_values :
    spread firstBisector firstSide firstBisector_nonNull firstSide_nonNull = 6 ∧
      spread secondBisector secondSide secondBisector_nonNull
          secondSide_nonNull = 7 ∧
      spread thirdBisector thirdSide thirdBisector_nonNull
          thirdSide_nonNull = 4 := by
  decide

/-- The three literal Triple-spread checks requested by the example. -/
theorem displayed_spread_triples :
    SpreadTriple (6 : F₁₃) 7 (-3) ∧
      SpreadTriple (-5 : F₁₃) 7 4 ∧
      SpreadTriple (6 : F₁₃) (-6) 4 := by
  unfold SpreadTriple tripleSpreadFunction
  decide

/-- The two displayed lines used to calculate `r₁`. -/
def displayedFirstBisector : Line F₁₃ where
  a := 2
  b := 1
  c := 0
  direction_nonzero := Or.inl (by decide)

def displayedOppositeSide : Line F₁₃ where
  a := 4
  b := 1
  c := -1
  direction_nonzero := Or.inl (by decide)

theorem displayed_lines_match_geometry :
    displayedFirstBisector.Equivalent firstBisector ∧
      displayedOppositeSide.Equivalent secondSide := by
  unfold Line.Equivalent displayedFirstBisector displayedOppositeSide
    firstBisector secondSide lineThrough first second third incenterPoint
  decide

private theorem displayedFirstBisector_nonNull :
    ¬ displayedFirstBisector.IsNull := by
  unfold Line.IsNull displayedFirstBisector
  decide

private theorem displayedOppositeSide_nonNull :
    ¬ displayedOppositeSide.IsNull := by
  unfold Line.IsNull displayedOppositeSide
  decide

/-- The printed spread `r₁=8`, together with the quotient from Exercise
12.7 evaluated on `u₁=6,u₂=7,u₃=4`. -/
theorem first_opposite_spread :
    spread displayedFirstBisector displayedOppositeSide
        displayedFirstBisector_nonNull displayedOppositeSide_nonNull = 8 ∧
      ((6 : F₁₃) - 2 * 7 - 2 * 4 + 2 * 7 ^ 2 + 2 * 4 ^ 2) /
          (2 * 6 - 1) = 8 := by
  decide

end ExampleTwelveOne

namespace ExampleTwelveTwo

abbrev Rational := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

private def rational
    (numerator : Int) (denominatorMinusOne : Nat) : Rational :=
  RFAP.ConstructiveFraction.ofFraction
    ⟨numerator, Int.ofNat (denominatorMinusOne + 1),
      Int.natCast_pos.mpr (Nat.zero_lt_succ denominatorMinusOne)⟩

private def gaussian
    (realNumerator : Int) (realDenominator : Nat)
    (imaginaryNumerator : Int) (imaginaryDenominator : Nat) : Gaussian :=
  ⟨rational realNumerator realDenominator,
    rational imaginaryNumerator imaginaryDenominator⟩

def first : Point Gaussian :=
  ⟨gaussian 1 0 0 0, gaussian 1 0 1 0⟩

def second : Point Gaussian :=
  ⟨gaussian 1 0 (-1) 0, gaussian 0 0 (-2) 0⟩

def third : Point Gaussian :=
  ⟨gaussian (-16) 38 20 116, gaussian 46 116 (-10) 38⟩

def incenterPoint : Point Gaussian :=
  ⟨gaussian 0 0 0 0, gaussian 0 0 0 0⟩

theorem point_distinctness :
    first ≠ second ∧ first ≠ third ∧ second ≠ third ∧
      first ≠ incenterPoint ∧ second ≠ incenterPoint ∧
      third ≠ incenterPoint := by
  decide

theorem triangle_noncollinear : ¬ Collinear first second third := by
  apply (collinear_iff_pointDeterminant_eq_zero first second third).not.mpr
  unfold pointDeterminant first second third
  decide

private theorem firstSecondDistinct : first ≠ second :=
  point_distinctness.1

private theorem firstThirdDistinct : first ≠ third :=
  point_distinctness.2.1

private theorem secondThirdDistinct : second ≠ third :=
  point_distinctness.2.2.1

def firstSide : Line Gaussian :=
  lineThrough first second firstSecondDistinct

def secondSide : Line Gaussian :=
  lineThrough second third secondThirdDistinct

def thirdSide : Line Gaussian :=
  lineThrough third first firstThirdDistinct.symm

theorem sides_nonNull :
    ¬ firstSide.IsNull ∧ ¬ secondSide.IsNull ∧
      ¬ thirdSide.IsNull := by
  unfold Line.IsNull firstSide secondSide thirdSide lineThrough first second
    third
  decide

private theorem firstSide_nonNull : ¬ firstSide.IsNull :=
  sides_nonNull.1

private theorem secondSide_nonNull : ¬ secondSide.IsNull :=
  sides_nonNull.2.1

private theorem thirdSide_nonNull : ¬ thirdSide.IsNull :=
  sides_nonNull.2.2

def firstBisector : Line Gaussian :=
  lineThrough first incenterPoint point_distinctness.2.2.2.1

def secondBisector : Line Gaussian :=
  lineThrough second incenterPoint point_distinctness.2.2.2.2.1

def thirdBisector : Line Gaussian :=
  lineThrough third incenterPoint point_distinctness.2.2.2.2.2

theorem bisectors_nonNull :
    ¬ firstBisector.IsNull ∧ ¬ secondBisector.IsNull ∧
      ¬ thirdBisector.IsNull := by
  unfold Line.IsNull firstBisector secondBisector thirdBisector lineThrough
    first second third incenterPoint
  decide

private theorem firstBisector_nonNull : ¬ firstBisector.IsNull :=
  bisectors_nonNull.1

private theorem secondBisector_nonNull : ¬ secondBisector.IsNull :=
  bisectors_nonNull.2.1

private theorem thirdBisector_nonNull : ¬ thirdBisector.IsNull :=
  bisectors_nonNull.2.2

/-- The three displayed bisector representatives meeting at the origin. -/
def displayedFirstBisector : Line Gaussian where
  a := gaussian 1 0 1 0
  b := gaussian (-1) 0 0 0
  c := gaussian 0 0 0 0
  direction_nonzero := Or.inl (by decide)

def displayedSecondBisector : Line Gaussian where
  a := gaussian 0 0 2 0
  b := gaussian 1 0 (-1) 0
  c := gaussian 0 0 0 0
  direction_nonzero := Or.inl (by decide)

def displayedThirdBisector : Line Gaussian where
  a := gaussian 46 0 (-30) 0
  b := gaussian 48 0 (-20) 0
  c := gaussian 0 0 0 0
  direction_nonzero := Or.inl (by decide)

/-- The three other displayed vertex bisectors, perpendicular to the first
three respectively. -/
def displayedFirstOtherBisector : Line Gaussian where
  a := gaussian 1 0 0 0
  b := gaussian 1 0 1 0
  c := gaussian (-1) 0 (-2) 0
  direction_nonzero := Or.inl (by decide)

def displayedSecondOtherBisector : Line Gaussian where
  a := gaussian 1 0 (-1) 0
  b := gaussian 0 0 (-2) 0
  c := gaussian 4 0 2 0
  direction_nonzero := Or.inl (by decide)

def displayedThirdOtherBisector : Line Gaussian where
  a := gaussian 72 0 (-30) 0
  b := gaussian (-69) 0 45 0
  c := gaussian 40 0 (-60) 0
  direction_nonzero := Or.inl (by decide)

/-- The displayed `hᵢ` representatives agree with the lines from the three
vertices to the origin. -/
theorem displayed_bisectors_match_geometry :
    displayedFirstBisector.Equivalent firstBisector ∧
      displayedSecondBisector.Equivalent secondBisector ∧
      displayedThirdBisector.Equivalent thirdBisector := by
  unfold Line.Equivalent displayedFirstBisector displayedSecondBisector
    displayedThirdBisector firstBisector secondBisector thirdBisector
    lineThrough first second third incenterPoint
  constructor
  · constructor
    · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
    · constructor
      · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
      · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
  · constructor
    · constructor
      · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
      · constructor
        · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
        · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
    · constructor
      · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
      · constructor
        · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
        · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

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
  · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
  · constructor
    · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
    · constructor
      · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
      · constructor
        · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
        · constructor
          · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
          · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

def firstOtherIncenter : Point Gaussian :=
  ⟨gaussian (-1) 2 (-1) 0, gaussian 2 2 (-4) 2⟩

def secondOtherIncenter : Point Gaussian :=
  ⟨gaussian 1 2 2 2, gaussian 1 0 1 2⟩

def thirdOtherIncenter : Point Gaussian :=
  ⟨gaussian (-5) 1 1 1, gaussian 5 1 (-1) 0⟩

private theorem first_secondOther_nonparallel :
    ¬ displayedFirstBisector.Parallel displayedSecondOtherBisector := by
  unfold Line.Parallel displayedFirstBisector displayedSecondOtherBisector
  decide

private theorem first_thirdOther_nonparallel :
    ¬ displayedFirstBisector.Parallel displayedThirdOtherBisector := by
  unfold Line.Parallel displayedFirstBisector displayedThirdOtherBisector
  decide

private theorem second_firstOther_nonparallel :
    ¬ displayedSecondBisector.Parallel displayedFirstOtherBisector := by
  unfold Line.Parallel displayedSecondBisector displayedFirstOtherBisector
  decide

private theorem second_thirdOther_nonparallel :
    ¬ displayedSecondBisector.Parallel displayedThirdOtherBisector := by
  unfold Line.Parallel displayedSecondBisector displayedThirdOtherBisector
  decide

private theorem third_firstOther_nonparallel :
    ¬ displayedThirdBisector.Parallel displayedFirstOtherBisector := by
  unfold Line.Parallel displayedThirdBisector displayedFirstOtherBisector
  decide

private theorem third_secondOther_nonparallel :
    ¬ displayedThirdBisector.Parallel displayedSecondOtherBisector := by
  unfold Line.Parallel displayedThirdBisector displayedSecondOtherBisector
  decide

/-- All six line intersections printed for the three other incenters. -/
theorem displayed_other_incenter_intersections :
    lineIntersection displayedFirstBisector displayedSecondOtherBisector
        first_secondOther_nonparallel = firstOtherIncenter ∧
      lineIntersection displayedFirstBisector displayedThirdOtherBisector
          first_thirdOther_nonparallel = firstOtherIncenter ∧
      lineIntersection displayedSecondBisector displayedFirstOtherBisector
          second_firstOther_nonparallel = secondOtherIncenter ∧
      lineIntersection displayedSecondBisector displayedThirdOtherBisector
          second_thirdOther_nonparallel = secondOtherIncenter ∧
      lineIntersection displayedThirdBisector displayedFirstOtherBisector
          third_firstOther_nonparallel = thirdOtherIncenter ∧
      lineIntersection displayedThirdBisector displayedSecondOtherBisector
          third_secondOther_nonparallel = thirdOtherIncenter := by
  constructor
  · apply Point.ext <;>
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
  · constructor
    · apply Point.ext <;>
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
    · constructor
      · apply Point.ext <;>
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
      · constructor
        · apply Point.ext <;>
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
        · constructor
          · apply Point.ext <;>
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
          · apply Point.ext <;>
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

def firstInquadrance : Gaussian := gaussian 16 38 (-8) 12
def secondInquadrance : Gaussian := gaussian 688 350 8 12
def thirdInquadrance : Gaussian := gaussian (-92) 350 (-136) 116
def fourthInquadrance : Gaussian := gaussian 2287 155 (-211) 25

/-- A displayed point has a common inquadrance value when its quadrance to
each of the three triangle sides is that value. -/
def HasCommonInquadrance (point : Point Gaussian) (value : Gaussian) : Prop :=
  pointLineQuadrance point firstSide firstSide_nonNull = value ∧
    pointLineQuadrance point secondSide secondSide_nonNull = value ∧
    pointLineQuadrance point thirdSide thirdSide_nonNull = value

/-- The four common inquadrances printed at the end of Example 12.2. -/
theorem displayed_inquadrance_values :
    HasCommonInquadrance incenterPoint firstInquadrance ∧
      HasCommonInquadrance firstOtherIncenter secondInquadrance ∧
      HasCommonInquadrance secondOtherIncenter thirdInquadrance ∧
      HasCommonInquadrance thirdOtherIncenter fourthInquadrance := by
  unfold HasCommonInquadrance
  repeat' apply And.intro
  all_goals rw [pointLineQuadrance_formula]
  all_goals apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

def printedQuadrea : Gaussian :=
  gaussian (-99328) 13688 400768 4562

def printedCircumquadrance : Gaussian :=
  gaussian 25 63 (-25) 95

/-- The displayed value is the circumquadrance of the explicit finite
circumcenter construction, not merely a solution of the cleared identity. -/
theorem circumquadrance_value :
    circumquadrance first second third firstThirdDistinct secondThirdDistinct
        triangle_noncollinear = printedCircumquadrance := by
  unfold circumquadrance circumcenterPoint perpendicularBisector
    lineIntersection quadrance printedCircumquadrance
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

def firstSpread : Gaussian := gaussian (-32) 194 (-56) 194
def secondSpread : Gaussian := gaussian (-4) 194 32 194
def thirdSpread : Gaussian := gaussian 9 4 0 0

/-- The three displayed spreads are the actual spreads made by the origin
bisectors with the cyclic triangle sides. -/
theorem incenter_spread_values :
    spread firstBisector firstSide firstBisector_nonNull firstSide_nonNull =
        firstSpread ∧
      spread secondBisector secondSide secondBisector_nonNull
          secondSide_nonNull = secondSpread ∧
      spread thirdBisector thirdSide thirdBisector_nonNull
          thirdSide_nonNull = thirdSpread := by
  constructor
  · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
  · constructor
    · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
    · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

/-- The source's two main scalar checks for Example 12.2. -/
theorem quadrea_and_circumquadrea_values :
    quadrea first second third = printedQuadrea ∧
      quadrea first second third * printedCircumquadrance =
        quadrance second third * quadrance first third *
          quadrance first second := by
  constructor
  · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
  · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

/-- The literal values check both the Inquadrance theorem and Exercise
12.8's four-incenter product formula. -/
theorem displayed_inquadrance_formula_checks :
    firstInquadrance =
        16 * printedCircumquadrance * firstSpread * secondSpread *
          thirdSpread ∧
      firstInquadrance * secondInquadrance * thirdInquadrance *
          fourthInquadrance = (printedQuadrea / 16) ^ 2 := by
  constructor
  · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
  · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

/-- The three printed half-angle spreads satisfy exactly the three
complemented Triple-spread equations used in the Incenter-spread proof. -/
theorem spread_triples :
    SpreadTriple firstSpread secondSpread (1 - thirdSpread) ∧
      SpreadTriple firstSpread (1 - secondSpread) thirdSpread ∧
      SpreadTriple (1 - firstSpread) secondSpread thirdSpread := by
  unfold SpreadTriple tripleSpreadFunction firstSpread secondSpread
    thirdSpread gaussian rational
  constructor
  · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
  · constructor
    · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide
    · apply RFAP.ConstructiveGaussian.Gaussian.ext <;> decide

end ExampleTwelveTwo

end ChapterTwelveExamples

end DivineProportions
