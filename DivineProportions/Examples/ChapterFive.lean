import DivineProportions.Trigonometry.QuadTripleExercises
import DivineProportions.Algebra.FieldEleven

/-!
# Divine Proportions, Example 5.2

Every point, line, incidence, perpendicularity, and quadrance printed in the
source is checked by kernel computation in the project's executable
eleven-element field.
-/

namespace DivineProportions

namespace ChapterFiveExamples

abbrev Element := FieldEleven.Element

def firstPoint : Point Element := ⟨3, 7⟩
def secondPoint : Point Element := ⟨10, 3⟩
def thirdPoint : Point Element := ⟨6, 1⟩

/-- The printed side `A₁A₂=⟨3:8:1⟩`. -/
def firstSecondLine : Line Element where
  a := 3
  b := 8
  c := 1
  direction_nonzero := by decide

/-- The printed side `A₂A₃=⟨8:6:1⟩`. -/
def secondThirdLine : Line Element where
  a := 8
  b := 6
  c := 1
  direction_nonzero := by decide

/-- The printed side `A₁A₃=⟨10:5:1⟩`. -/
def firstThirdLine : Line Element where
  a := 10
  b := 5
  c := 1
  direction_nonzero := by decide

/-- Example 5.2: the complete closed certificate for Figure 5.3 and its
following quadrance calculation. -/
theorem example_5_2 :
    firstSecondLine.Contains firstPoint ∧
      firstSecondLine.Contains secondPoint ∧
      secondThirdLine.Contains secondPoint ∧
      secondThirdLine.Contains thirdPoint ∧
      firstThirdLine.Contains firstPoint ∧
      firstThirdLine.Contains thirdPoint ∧
      firstThirdLine.Perpendicular secondThirdLine ∧
      quadrance secondPoint thirdPoint = 9 ∧
      quadrance firstPoint thirdPoint = 1 ∧
      quadrance firstPoint secondPoint = 10 ∧
      quadrance secondPoint thirdPoint +
          quadrance firstPoint thirdPoint =
        quadrance firstPoint secondPoint := by
  unfold Line.Contains Line.Perpendicular quadrance firstSecondLine
    secondThirdLine firstThirdLine firstPoint secondPoint thirdPoint
  decide

end ChapterFiveExamples

end DivineProportions
