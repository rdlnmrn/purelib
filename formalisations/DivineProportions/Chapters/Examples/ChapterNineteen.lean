module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Finite.Eleven
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Curves.Plane.Conic.Tangent
import Purelib.Curves.Plane.Conic.Translation
public import Purelib.Geometry.Circles.Conic.Basic
public import Purelib.Geometry.Conics.Parabola.Standard
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Divine Proportions, Chapter 19 worked examples

This module begins with the translated-conic and tangent-line calculations in
Examples 19.1--19.4, then records the exact two-tangent identity and its
eleven-element-field instance from Exercise 19.2.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterNineteen

namespace ChapterNineteenExamples

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace ExampleNineteenOne

open Purelib.Curves.Plane in
/-- The unit circle `⟨1:0:1:0:0:-1⟩` from Example 19.1. -/
def circle [Nontrivial K] : Conic K :=
  Conic.circleConic ⟨0, 0⟩ 1

open Purelib.Geometry.Plane.Point in
/-- The displayed translation vector `[2,3]`. -/
def offset : Purelib.Geometry.Plane.Point K := ⟨2, 3⟩

open Purelib.Curves.Plane in
open Purelib.Geometry.Plane.Point in
open formalisations.DivineProportions.Chapters.Examples.ChapterNineteen.ChapterNineteenExamples in
/-- Example 19.1: translating the unit circle by `[2,3]` gives the expanded
equation `(x-2)²+(y-3)²-1=0`. -/
theorem example_19_1 [Nontrivial K] :
    let translated := Conic.translateConic (ExampleNineteenOne.circle (K := K)) (ExampleNineteenOne.offset (K := K))
    translated.d = 1 ∧ translated.e = 0 ∧ translated.f = 1 ∧
      translated.a = -4 ∧ translated.b = -6 ∧ translated.c = 12 ∧
      ∀ point : Purelib.Geometry.Plane.Point K,
        translated.evaluate point =
          (point.x - 2) ^ 2 + (point.y - 3) ^ 2 - 1 := by
  dsimp only [ExampleNineteenOne.circle, ExampleNineteenOne.offset, Conic.circleConic, Conic.translateConic]
  refine ⟨by ring1, by ring1, by ring1, by ring1, by ring1, by ring1, ?_⟩
  intro point
  unfold Conic.evaluate
  ring1

end ExampleNineteenOne

namespace ExampleNineteenTwo

open Purelib.Curves.Plane in
/-- The conic `⟨1:-2:-1:1:0:-5⟩` in Examples 19.2 and 19.3. -/
def conic [Nontrivial K] : Conic K where
  d := 1
  e := -2
  f := -1
  a := 1
  b := 0
  c := -5
  quadratic_nonzero := Or.inl one_ne_zero

open Purelib.Geometry.Plane.Point in
/-- The displayed point `[3,1]`. -/
def point : Purelib.Geometry.Plane.Point K := ⟨3, 1⟩

open Purelib.Curves.Plane
open formalisations.DivineProportions.Chapters.Examples.ChapterNineteen.ChapterNineteenExamples
/-- Example 19.2: `[3,1]` lies on the conic and its Taylor conic is
`⟨1:-2:-1:5:-8:0⟩`. -/
theorem example_19_2 [Nontrivial K] :
    let source := conic (K := K)
    let basePoint := ExampleNineteenTwo.point (K := K)
    let taylor := Conic.taylorConic source basePoint
    source.Contains basePoint ∧
      taylor.d = 1 ∧ taylor.e = -2 ∧ taylor.f = -1 ∧
      taylor.a = 5 ∧ taylor.b = -8 ∧ taylor.c = 0 := by
  dsimp only [conic, point, Conic.taylorConic, Conic.translateConic,
    Conic.Contains, Conic.evaluate]
  exact ⟨by ring1, by ring1, by ring1, by ring1, by ring1, by ring1,
    by ring1⟩

/-- Example 19.3: the printed tangent representative at `[3,1]` is
`⟨5:-8:-7⟩`.  Its required non-singularity is supplied as the exact
disjunction between the two displayed linear coefficients. -/
theorem example_19_3 [Nontrivial K]
    (linearNonzero : (5 : K) ≠ 0 ∨ (-8 : K) ≠ 0) :
    let source := conic (K := K)
    let basePoint := ExampleNineteenTwo.point (K := K)
    let nonSingular : source.IsNonSingularAt basePoint := by
      unfold Conic.IsNonSingularAt source basePoint conic point
      have firstValue : (1 + 2 * 1 * 3 + -2 * 1 : K) = 5 := by ring1
      have secondValue : (0 + -2 * 3 + 2 * -1 * 1 : K) = -8 := by ring1
      rw [firstValue, secondValue]
      exact linearNonzero
    let tangent := Conic.tangentLine source basePoint nonSingular
    tangent.a = 5 ∧ tangent.b = -8 ∧ tangent.c = -7 ∧
      tangent.Contains basePoint := by
  dsimp only
  let source := conic (K := K)
  let basePoint := ExampleNineteenTwo.point (K := K)
  have onConic : source.Contains basePoint := by
    unfold source basePoint conic point Conic.Contains Conic.evaluate
    ring1
  have nonSingular : source.IsNonSingularAt basePoint := by
    unfold source basePoint conic point Conic.IsNonSingularAt
    simpa only [show (1 + 2 * 1 * 3 + -2 * 1 : K) = 5 by ring1,
      show (0 + -2 * 3 + 2 * -1 * 1 : K) = -8 by ring1] using
      linearNonzero
  refine ⟨?_, ?_, ?_, Conic.tangentLine_contains source basePoint onConic
    nonSingular⟩
  · change (1 : K) + 2 * 1 * 3 + -2 * 1 = 5
    ring1
  · change (0 : K) + -2 * 3 + 2 * -1 * 1 = -8
    ring1
  · change (1 : K) * 3 + 0 * 1 + 2 * -5 = -7
    ring1

end ExampleNineteenTwo

namespace ExerciseNineteenTwo
namespace FieldElevenCheck

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Conics.Parabola.Standard in
open Purelib.Geometry.Plane.Point in
/-- The book's exact `F₁₁` data: `A₁=[1,2]`, `A₂=[4,-4]`,
`B=[-2,-1]`, and both ratios normalize to `5`. -/
theorem field_eleven_example :
    ExerciseNineteenTwo.point (K := Eleven.Element) 1 = ⟨1, 2⟩ ∧
      ExerciseNineteenTwo.point (K := Eleven.Element) 9 = ⟨4, 7⟩ ∧
      ExerciseNineteenTwo.tangentIntersection (K := Eleven.Element) 1 9 = ⟨9, 10⟩ ∧
      Quadrance.quadrance (ExerciseNineteenTwo.point (K := Eleven.Element) 1)
          (ExerciseNineteenTwo.tangentIntersection (K := Eleven.Element) 1 9) = 7 ∧
      Quadrance.quadrance (ExerciseNineteenTwo.point (K := Eleven.Element) 9)
          (ExerciseNineteenTwo.tangentIntersection (K := Eleven.Element) 1 9) = 1 ∧
      Quadrance.quadrance (ExerciseNineteenTwo.point (K := Eleven.Element) 1) (ExerciseNineteenTwo.focus (K :=
        Eleven.Element)) = 4 ∧
      Quadrance.quadrance (ExerciseNineteenTwo.point (K := Eleven.Element) 9) (ExerciseNineteenTwo.focus (K :=
        Eleven.Element)) = 3 ∧
      Quadrance.quadrance (ExerciseNineteenTwo.point (K := Eleven.Element) 1)
          (ExerciseNineteenTwo.tangentIntersection (K := Eleven.Element) 1 9) ^ 2 /
          Quadrance.quadrance (ExerciseNineteenTwo.point (K := Eleven.Element) 9)
            (ExerciseNineteenTwo.tangentIntersection (K := Eleven.Element) 1 9) ^ 2 = 5 ∧
      Quadrance.quadrance (ExerciseNineteenTwo.point (K := Eleven.Element) 1) (ExerciseNineteenTwo.focus (K :=
        Eleven.Element)) /
          Quadrance.quadrance (ExerciseNineteenTwo.point (K := Eleven.Element) 9) (ExerciseNineteenTwo.focus (K :=
            Eleven.Element)) = 5 := by
  unfold ExerciseNineteenTwo.point ExerciseNineteenTwo.tangentIntersection ExerciseNineteenTwo.focus Quadrance.quadrance
  decide

end FieldElevenCheck

end ExerciseNineteenTwo

end ChapterNineteenExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterNineteen

end
