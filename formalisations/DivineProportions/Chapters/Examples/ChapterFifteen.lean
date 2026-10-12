module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Conics.Parabola.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Curves.Plane.Conic.Center
import Purelib.Curves.Plane.Conic.Scale
public import Purelib.Geometry.Circles.Conic.Basic
import Purelib.Geometry.Conics.CoefficientScale.Locus
public import Purelib.Geometry.Conics.Grammola.Basic
public import Purelib.Geometry.Conics.Quadrola.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
public import Purelib.Algebra.Field.Finite.Eleven
import Purelib.Data.Rat.Fraction.Compatibility
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry
open Purelib.Geometry.Plane

section
@[expose] public section

/-!
# Divine Proportions, §15.1: conics and their centers

A conic is kept as its six displayed coefficients.  Its quadratic part is
required to be nonzero, exactly as in the source.  Center calculations use only
the two finite linear equations obtained by expanding rotation invariance.
-/

namespace Purelib.Curves.Plane

variable {K : Type*} [ExplicitField K]
namespace Conic

/-- Example 15.1's conic `⟨1 : 2 : -1 : -6 : 2 : 1⟩`. -/
def example15OneConic [Nontrivial K] : Curves.Plane.Conic K
  where
  d := 1
  e := 2
  f := -1
  a := -6
  b := 2
  c := 1
  quadratic_nonzero := Or.inl one_ne_zero

/-- Example 15.1: `[1,2]` satisfies the two center equations. -/
theorem example_15_1 [Nontrivial K] :
    (example15OneConic (K := K)).IsCenter ⟨1, 2⟩ := by
  constructor <;> unfold example15OneConic <;> ring1

/-- Example 15.1 in the source's original rotation-invariance form. -/
theorem example_15_1_rotationInvariant [Nontrivial K]
    (twoNonzero : (2 : K) ≠ 0) :
    (example15OneConic (K := K)).RotationInvariant ⟨1, 2⟩ :=
  (Curves.Plane.Conic.isCenter_iff_rotationInvariant _ _ twoNonzero).1
    example_15_1

/-- The first conic in Exercise 15.1, `(x+y)² = 0`. -/
def exercise15OneFirstConic [Nontrivial K] :
  Curves.Plane.Conic K where
  d := 1
  e := 2
  f := 1
  a := 0
  b := 0
  c := 0
  quadratic_nonzero := Or.inl one_ne_zero

/-- The second conic in Exercise 15.1, `(x+y)²+x = 0`. -/
def exercise15OneSecondConic [Nontrivial K] :
  Curves.Plane.Conic K where
  d := 1
  e := 2
  f := 1
  a := 1
  b := 0
  c := 0
  quadratic_nonzero := Or.inl one_ne_zero

/-- Exercise 15.1: the first conic has exactly the centers `[u,-u]`. -/
theorem exercise_15_1_first [Nontrivial K] (twoNonzero : (2 : K) ≠ 0)
    (point : Plane.Point K) :
    (exercise15OneFirstConic (K := K)).IsCenter point ↔
      point.y = -point.x := by
  constructor
  · rintro ⟨firstEquation, _⟩
    have productZero : (2 : K) * (point.x + point.y) = 0 := by
      calc
        (2 : K) * (point.x + point.y) =
            2 * (exercise15OneFirstConic (K := K)).d * point.x +
              (exercise15OneFirstConic (K := K)).e * point.y +
              (exercise15OneFirstConic (K := K)).a := by
                unfold exercise15OneFirstConic
                ring1
        _ = 0 := firstEquation
    have sumZero :=
      ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero productZero
    calc
      point.y = (point.x + point.y) - point.x := by ring1
      _ = -point.x := by rw [sumZero]; ring1
  · intro yFormula
    constructor <;>
      unfold exercise15OneFirstConic <;>
      rw [yFormula] <;>
      ring1

/-- Exercise 15.1: the second conic has no center. -/
theorem exercise_15_1_second [Nontrivial K] :
    ¬ ∃ point : Plane.Point K,
      (exercise15OneSecondConic (K := K)).IsCenter point := by
  rintro ⟨point, firstEquation, secondEquation⟩
  have oneZero : (1 : K) = 0 := by
    calc
      (1 : K) =
          (2 * (exercise15OneSecondConic (K := K)).d * point.x +
              (exercise15OneSecondConic (K := K)).e * point.y +
              (exercise15OneSecondConic (K := K)).a) -
            ((exercise15OneSecondConic (K := K)).e * point.x +
              2 * (exercise15OneSecondConic (K := K)).f * point.y +
              (exercise15OneSecondConic (K := K)).b) := by
                unfold exercise15OneSecondConic
                ring1
      _ = 0 := by rw [firstEquation, secondEquation]; ring1
  exact one_ne_zero oneZero
end Conic

end Purelib.Curves.Plane

end

section
@[expose] public section

/-!
# Divine Proportions, §15.2: circles

Circle presentations retain the arbitrary nonzero common scale of the source's
six-coefficient conic notation.  Thus Theorem 100 proves genuine recovery of a
center and quadrance from a displayed conic rather than storing them as data.
-/

namespace Purelib.Curves.Plane

variable {K : Type*} [ExplicitField K]

namespace Conic

/-- The first line in Exercise 15.5. -/
def exercise15FiveFirstLine (twoNonzero : (2 : K) ≠ 0) : Plane.Line K
  where
  a := 2
  b := 3
  c := 0
  direction_nonzero := Or.inl twoNonzero

/-- The second line in Exercise 15.5. -/
def exercise15FiveSecondLine (threeNonzero : (3 : K) ≠ 0) :
  Plane.Line K where
  a := 3
  b := 2
  c := 0
  direction_nonzero := Or.inl threeNonzero

/-- Exercise 15.5, including its requested generalization: in any constructive
field of characteristic thirteen, the central null circle is exactly the union
of the two displayed null lines. -/
theorem exercise_15_5 [DecidableEq K] [Nontrivial K]
    (twoNonzero : (2 : K) ≠ 0) (threeNonzero : (3 : K) ≠ 0)
    (thirteenZero : (13 : K) = 0) (point : Plane.Point K) :
    (Curves.Plane.Conic.circleConic (⟨0, 0⟩ : Plane.Point K) 0).Contains point ↔
      (exercise15FiveFirstLine twoNonzero).Contains point ∨
        (exercise15FiveSecondLine threeNonzero).Contains point := by
  have subtractZero (value : K) : value - 0 = value := by ring1
  have sixNonzero : (6 : K) ≠ 0 := by
    have twoTimesThreeNonzero : (2 : K) * 3 ≠ 0 :=
      ExplicitField.mul_ne_zero twoNonzero threeNonzero
    intro sixZero
    apply twoTimesThreeNonzero
    calc
      (2 : K) * 3 = 6 := by ring1
      _ = 0 := sixZero
  have factorization :
      ((2 : K) * point.x + 3 * point.y) *
          (3 * point.x + 2 * point.y) =
        6 * (point.x ^ 2 + point.y ^ 2) := by
    calc
      ((2 : K) * point.x + 3 * point.y) *
          (3 * point.x + 2 * point.y) =
        6 * (point.x ^ 2 + point.y ^ 2) +
          13 * point.x * point.y := by ring1
      _ = 6 * (point.x ^ 2 + point.y ^ 2) := by
        rw [thirteenZero]
        ring1
  simp only [Curves.Plane.Conic.Contains, Curves.Plane.Conic.circleConic,
    Curves.Plane.Conic.evaluate, exercise15FiveFirstLine,
    exercise15FiveSecondLine, Plane.Line.Contains, one_mul, zero_mul, add_zero,
    mul_zero, subtractZero, zero_pow (by decide : 2 ≠ 0)]
  change point.x ^ 2 + point.y ^ 2 = 0 ↔
    (2 : K) * point.x + 3 * point.y = 0 ∨
      3 * point.x + 2 * point.y = 0
  constructor
  · intro circleEquation
    have productZero :
        ((2 : K) * point.x + 3 * point.y) *
          (3 * point.x + 2 * point.y) = 0 := by
      rw [factorization, circleEquation]
      ring1
    by_cases firstFactorZero : (2 : K) * point.x + 3 * point.y = 0
    · exact Or.inl firstFactorZero
    · exact Or.inr
        (ExplicitField.eq_zero_of_mul_eq_zero_left firstFactorZero productZero)
  · intro onLine
    have productZero :
        ((2 : K) * point.x + 3 * point.y) *
          (3 * point.x + 2 * point.y) = 0 := by
      rcases onLine with firstFactorZero | secondFactorZero
      · rw [firstFactorZero]
        ring1
      · rw [secondFactorZero]
        ring1
    apply ExplicitField.eq_zero_of_mul_eq_zero_left sixNonzero
    calc
      6 * (point.x ^ 2 + point.y ^ 2) =
          ((2 : K) * point.x + 3 * point.y) *
            (3 * point.x + 2 * point.y) := factorization.symm
      _ = 0 := productZero

end Conic

end Purelib.Curves.Plane

end

section
@[expose] public section

/-!
# Divine Proportions, §15.5: grammolas

A grammola is retained through its two explicit non-null diagonal lines and
associated quadrance.  Multiplying by the two line norms clears exactly the
two finite divisions and produces an executable conic.  The intersection of
the diagonals is then an explicit center.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterFifteen

namespace Grammola

variable {K : Type*} [ExplicitField K]

/-- The first diagonal `⟨a:-1:0⟩` in Example 15.7. -/
def example15SevenFirstDiagonal
  [Nontrivial K] (a : K) : Plane.Line K where
  a := a
  b := -1
  c := 0
  direction_nonzero := Or.inr (by
    intro negativeOneZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [negativeOneZero]; ring1)

/-- The second diagonal `⟨a:1:0⟩` in Example 15.7. -/
def example15SevenSecondDiagonal
  [Nontrivial K] (a : K) : Plane.Line K where
  a := a
  b := 1
  c := 0
  direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0)

open formalisations.DivineProportions.Chapters.Examples
/-- The diagonal with coefficients (a, −1, 0) is non-null when a² + 1 is nonzero. -/
theorem example15SevenFirst_nonNull
  [Nontrivial K] (a : K)
    (normNonzero : a ^ 2 + 1 ≠ 0) :
    ¬ (example15SevenFirstDiagonal a).IsNull := by
  intro null
  apply normNonzero
  calc
    a ^ 2 + 1 =
        (example15SevenFirstDiagonal a).a ^ 2 +
          (example15SevenFirstDiagonal a).b ^ 2 := by
      unfold example15SevenFirstDiagonal
      ring1
    _ = 0 := null

/-- The diagonal with coefficients (a, 1, 0) is non-null when a² + 1 is nonzero. -/
theorem example15SevenSecond_nonNull
  [Nontrivial K] (a : K)
    (normNonzero : a ^ 2 + 1 ≠ 0) :
    ¬ (example15SevenSecondDiagonal a).IsNull := by
  intro null
  apply normNonzero
  calc
    a ^ 2 + 1 =
        (example15SevenSecondDiagonal a).a ^ 2 +
          (example15SevenSecondDiagonal a).b ^ 2 := by
      unfold example15SevenSecondDiagonal
      ring1
    _ = 0 := null

/-- Example 15.7's diagonal data form a grammola presentation.  Besides the
printed `a ≠ ±1`, the definition also requires `a ≠ 0` (otherwise the
two displayed lines coincide) and `a²+1 ≠ 0` (otherwise they are null).
These necessary source hypotheses are explicit here. -/
theorem example_15_7_presentation
  [Nontrivial K]
    (a associatedQuadrance : K) (aNonzero : a ≠ 0)
    (normNonzero : a ^ 2 + 1 ≠ 0) (notSquareOne : a ^ 2 ≠ 1)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Conics.Grammola.Presentation (example15SevenFirstDiagonal a)
      (example15SevenSecondDiagonal a) associatedQuadrance := by
  have firstNonNull := example15SevenFirst_nonNull a normNonzero
  have secondNonNull := example15SevenSecond_nonNull a normNonzero
  refine ⟨firstNonNull, secondNonNull, ?_, ?_, associatedNonzero⟩
  · intro parallel
    have twiceANonzero : (2 : K) * a ≠ 0 :=
      ExplicitField.mul_ne_zero twoNonzero aNonzero
    apply twiceANonzero
    calc
      (2 : K) * a =
          (example15SevenFirstDiagonal a).a *
              (example15SevenSecondDiagonal a).b -
            (example15SevenSecondDiagonal a).a *
              (example15SevenFirstDiagonal a).b := by
        unfold example15SevenFirstDiagonal example15SevenSecondDiagonal
        ring1
      _ = 0 := parallel
  · intro perpendicular
    apply notSquareOne
    calc
      a ^ 2 =
          ((example15SevenFirstDiagonal a).a *
              (example15SevenSecondDiagonal a).a +
            (example15SevenFirstDiagonal a).b *
              (example15SevenSecondDiagonal a).b) + 1 := by
        unfold example15SevenFirstDiagonal example15SevenSecondDiagonal
        ring1
      _ = 1 := by rw [perpendicular]; ring1

/-- Example 15.7: clearing the common nonzero line norm gives exactly
`2a²x²+2y²=K(a²+1)`. -/
theorem example_15_7_equation
  [Nontrivial K] [DecidableEq K]
    (a associatedQuadrance : K) (normNonzero : a ^ 2 + 1 ≠ 0)
    (point : Plane.Point K) :
    Conics.Grammola.Contains (example15SevenFirstDiagonal a)
        (example15SevenSecondDiagonal a)
        (example15SevenFirst_nonNull a normNonzero)
        (example15SevenSecond_nonNull a normNonzero)
        associatedQuadrance point ↔
      2 * a ^ 2 * point.x ^ 2 + 2 * point.y ^ 2 =
        associatedQuadrance * (a ^ 2 + 1) := by
  have normCancel : (a ^ 2 + 1) * (a ^ 2 + 1)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ normNonzero
  unfold Conics.Grammola.Contains
  rw [Line.Quadrance.pointLineQuadrance_formula, Line.Quadrance.pointLineQuadrance_formula]
  unfold example15SevenFirstDiagonal example15SevenSecondDiagonal
    Line.Basic.lineNorm
  have firstValue : a * point.x + -1 * point.y + 0 =
      a * point.x - point.y := by ring1
  have secondValue : a * point.x + 1 * point.y + 0 =
      a * point.x + point.y := by ring1
  have firstNorm : a ^ 2 + (-1 : K) ^ 2 = a ^ 2 + 1 := by ring1
  have secondNorm : a ^ 2 + (1 : K) ^ 2 = a ^ 2 + 1 := by ring1
  rw [firstValue, secondValue, firstNorm, secondNorm]
  simp only [ExplicitField.div_eq_mul_inv]
  constructor
  · intro metricEquation
    calc
      2 * a ^ 2 * point.x ^ 2 + 2 * point.y ^ 2 =
          (a * point.x - point.y) ^ 2 +
            (a * point.x + point.y) ^ 2 := by ring1
      _ = ((a * point.x - point.y) ^ 2 +
            (a * point.x + point.y) ^ 2) *
          ((a ^ 2 + 1) * (a ^ 2 + 1)⁻¹) := by
        rw [normCancel]
        ring1
      _ = (a ^ 2 + 1) *
          ((a * point.x - point.y) ^ 2 * (a ^ 2 + 1)⁻¹ +
            (a * point.x + point.y) ^ 2 * (a ^ 2 + 1)⁻¹) := by
        ring1
      _ = (a ^ 2 + 1) * associatedQuadrance := by
        rw [metricEquation]
      _ = associatedQuadrance * (a ^ 2 + 1) := by ring1
  · intro clearedEquation
    have productZero :
        (a ^ 2 + 1) *
          ((a * point.x - point.y) ^ 2 * (a ^ 2 + 1)⁻¹ +
            (a * point.x + point.y) ^ 2 * (a ^ 2 + 1)⁻¹ -
            associatedQuadrance) = 0 := by
      calc
        (a ^ 2 + 1) *
              ((a * point.x - point.y) ^ 2 * (a ^ 2 + 1)⁻¹ +
                (a * point.x + point.y) ^ 2 * (a ^ 2 + 1)⁻¹ -
                associatedQuadrance) =
            2 * a ^ 2 * point.x ^ 2 + 2 * point.y ^ 2 -
              associatedQuadrance * (a ^ 2 + 1) := by
          calc
            (a ^ 2 + 1) *
                  ((a * point.x - point.y) ^ 2 * (a ^ 2 + 1)⁻¹ +
                    (a * point.x + point.y) ^ 2 * (a ^ 2 + 1)⁻¹ -
                    associatedQuadrance) =
                ((a * point.x - point.y) ^ 2 +
                  (a * point.x + point.y) ^ 2) *
                    ((a ^ 2 + 1) * (a ^ 2 + 1)⁻¹) -
                  associatedQuadrance * (a ^ 2 + 1) := by ring1
            _ = 2 * a ^ 2 * point.x ^ 2 + 2 * point.y ^ 2 -
                associatedQuadrance * (a ^ 2 + 1) := by
              rw [normCancel]
              ring1
        _ = 0 := by rw [clearedEquation]; ring1
    have differenceZero :=
      ExplicitField.eq_zero_of_mul_eq_zero_left normNonzero productZero
    calc
      (a * point.x - point.y) ^ 2 * (a ^ 2 + 1)⁻¹ +
          (a * point.x + point.y) ^ 2 * (a ^ 2 + 1)⁻¹ =
        ((a * point.x - point.y) ^ 2 * (a ^ 2 + 1)⁻¹ +
          (a * point.x + point.y) ^ 2 * (a ^ 2 + 1)⁻¹ -
          associatedQuadrance) + associatedQuadrance := by ring1
      _ = associatedQuadrance := by rw [differenceZero]; ring1

end Grammola

end formalisations.DivineProportions.Chapters.Examples.ChapterFifteen

end

section
@[expose] public section

/-!
# Divine Proportions, §15.3: parabolas

The six coefficient equations below are the denominator-cleared expansion of
`Q(X,F) = Q(X,l)`.  An explicit nonzero scale retains the source's proportional
conic notation without a quotient or a selected representative.
-/

namespace Purelib.Curves.Plane

variable {K : Type*} [ExplicitField K]

namespace Conic

/-- The directrix `⟨1:0:a⟩` used in Example 15.3. -/
def example15ThreeDirectrix [Nontrivial K] (parameter : K) :
  Plane.Line K where
  a := 1
  b := 0
  c := parameter
  direction_nonzero := Or.inl one_ne_zero

/-- The displayed conic `⟨0:0:1:-4a:0:0⟩` in Example 15.3. -/
def example15ThreeConic [Nontrivial K] (parameter : K) :
  Curves.Plane.Conic K where
  d := 0
  e := 0
  f := 1
  a := -4 * parameter
  b := 0
  c := 0
  quadratic_nonzero := Or.inr (Or.inr one_ne_zero)

/-- Example 15.3: the displayed conic is presented by focus `[a,0]` and
directrix `⟨1:0:a⟩`. -/
theorem example_15_3 [Nontrivial K] (twoNonzero : (2 : K) ≠ 0)
    (parameter : K) (parameterNonzero : parameter ≠ 0) :
    (example15ThreeConic parameter).IsParabolaPresentation
      ⟨parameter, 0⟩ (example15ThreeDirectrix parameter) := by
  have twoParameterNonzero : 2 * parameter ≠ 0 :=
    ExplicitField.mul_ne_zero twoNonzero parameterNonzero
  refine ⟨
    { directrixNonNull := ?_
      focusNotOnDirectrix := ?_
      scale := 1
      scaleNonzero := one_ne_zero
      dEquation := ?_
      eEquation := ?_
      fEquation := ?_
      aEquation := ?_
      bEquation := ?_
      cEquation := ?_ }⟩
  · unfold Plane.Line.IsNull example15ThreeDirectrix
    intro oneZero
    exact one_ne_zero (by simpa only [one_pow, zero_pow (by decide : 2 ≠ 0),
      add_zero] using oneZero)
  · unfold Plane.Line.Contains example15ThreeDirectrix
    intro incidence
    apply twoParameterNonzero
    calc
      2 * parameter =
          (1 : K) * parameter + 0 * 0 + parameter := by ring1
      _ = 0 := incidence
  all_goals dsimp only [example15ThreeConic,
    example15ThreeDirectrix]
  all_goals try unfold Line.Basic.lineNorm
  all_goals ring1

/-- Example 15.3's equation is exactly `y² = 4ax`. -/
theorem example_15_3_equation [Nontrivial K]
    (parameter : K) (point : Plane.Point K) :
    (example15ThreeConic parameter).Contains point ↔
      point.y ^ 2 = 4 * parameter * point.x := by
  unfold Curves.Plane.Conic.Contains Curves.Plane.Conic.evaluate
    example15ThreeConic
  constructor <;> intro equation
  · calc
      point.y ^ 2 =
          (0 : K) * point.x ^ 2 + 0 * point.x * point.y +
            1 * point.y ^ 2 + (-4 * parameter) * point.x +
            0 * point.y + 0 + 4 * parameter * point.x := by ring1
      _ = 4 * parameter * point.x := by rw [equation]; ring1
  · calc
      (0 : K) * point.x ^ 2 + 0 * point.x * point.y +
          1 * point.y ^ 2 + (-4 * parameter) * point.x +
          0 * point.y + 0 =
        point.y ^ 2 - 4 * parameter * point.x := by ring1
      _ = 0 := by rw [equation]; ring1

/-- Example 15.4: over the executable eleven-element field, the focus `[1,0]`
and directrix `⟨1:0:1⟩` present the displayed parabola. -/
theorem example_15_4 :
    (example15ThreeConic (K := Finite.Eleven.Element) 1).IsParabolaPresentation
      ⟨1, 0⟩ (example15ThreeDirectrix 1) :=
  example_15_3 (K := Finite.Eleven.Element) (by decide) 1 (by decide)

/-- Example 15.4's plotted finite-field conic has equation `y² = 4x`. -/
theorem example_15_4_equation (point : Plane.Point
  Finite.Eleven.Element) :
    (example15ThreeConic (K := Finite.Eleven.Element) 1).Contains point ↔
      point.y ^ 2 = 4 * point.x := by
  have coefficient :
      (4 : Finite.Eleven.Element) * (1 : Finite.Eleven.Element) = 4 := by decide
  constructor
  · intro onConic
    have equation :=
      (example_15_3_equation (K := Finite.Eleven.Element) 1 point).1 onConic
    calc
      point.y ^ 2 = 4 * (1 : Finite.Eleven.Element) * point.x := equation
      _ = 4 * point.x := by rw [coefficient]
  · intro equation
    apply (example_15_3_equation (K := Finite.Eleven.Element) 1 point).2
    calc
      point.y ^ 2 = 4 * point.x := equation
      _ = 4 * (1 : Finite.Eleven.Element) * point.x := by rw [coefficient]

end Conic

end Purelib.Curves.Plane

end

section
@[expose] public section

/-!
# Divine Proportions, §15.4 and Exercise 19.3: quadrolas

A quadrola is given by one finite Archimedes polynomial in the two focal
quadrances and its associated quadrance.  The apparent quartic terms cancel
to an explicit conic.  Its gradient tangent satisfies the equal-spread
reflection property by a denominator-cleared polynomial identity.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterFifteen

namespace Quadrola

variable {K : Type*} [ExplicitField K]

/-- The first symmetric focus used in Examples 15.5 and 15.6. -/
def symmetricFirstFocus (a : K) :
  Plane.Point K := ⟨a, 0⟩

/-- The second symmetric focus used in Examples 15.5 and 15.6. -/
def symmetricSecondFocus (a : K) :
  Plane.Point K := ⟨-a, 0⟩

open formalisations.DivineProportions.Chapters.Examples
/-- Example 15.5: the quadrance between the displayed symmetric foci is
`4a²`. -/
theorem example_15_5_focus_quadrance
  (a : K) :
    Point.Quadrance.quadrance (symmetricFirstFocus a)
      (symmetricSecondFocus a) =
      4 * a ^ 2 := by
  unfold symmetricFirstFocus symmetricSecondFocus
    Point.Quadrance.quadrance
  ring1

/-- Example 15.5: expansion of the symmetric-focus quadrola gives exactly
the displayed diagonal conic equation. -/
theorem example_15_5_equation
  [DecidableEq K]
    (a associatedQuadrance : K)
    (associatedNonzero : associatedQuadrance ≠ 0)
    (eightNonzero : (8 : K) ≠ 0) (point : Plane.Point K) :
    (Conics.Quadrola.conic (symmetricFirstFocus a)
      (symmetricSecondFocus a)
      associatedQuadrance associatedNonzero eightNonzero).evaluate point =
        4 * (associatedQuadrance - 4 * a ^ 2) * point.x ^ 2 +
          4 * associatedQuadrance * point.y ^ 2 -
          associatedQuadrance * (associatedQuadrance - 4 * a ^ 2) := by
  unfold Conics.Quadrola.conic Curves.Plane.Conic.evaluate
    Conics.Quadrola.conicD Conics.Quadrola.conicE
    Conics.Quadrola.conicF Conics.Quadrola.conicA
    Conics.Quadrola.conicB Conics.Quadrola.conicC
    symmetricFirstFocus symmetricSecondFocus
  ring1

/-- Example 15.5: when `i²=-1`, exchanging the horizontal foci for the
displayed vertical foci and replacing `K` by `K-4a²` leaves the finite
Archimedes equation unchanged. -/
theorem example_15_5_alternate_foci
    (a associatedQuadrance i : K) (iSquare : i ^ 2 = -1)
    (point : Plane.Point K) :
    Conics.Quadrola.evaluate (symmetricFirstFocus a)
      (symmetricSecondFocus a)
        associatedQuadrance point =
      Conics.Quadrola.evaluate ⟨0, i * a⟩ ⟨0, -(i * a)⟩
        (associatedQuadrance - 4 * a ^ 2) point := by
  unfold Conics.Quadrola.evaluate
  simp only [Geometry.Trigonometry.QuadTriple.Basic.Quadrola.archimedes_difference_identity]
  calc
    -(Point.Quadrance.quadrance point (symmetricFirstFocus a) -
            Point.Quadrance.quadrance point (symmetricSecondFocus a)) ^ 2 +
          2 * associatedQuadrance *
            (Point.Quadrance.quadrance point (symmetricFirstFocus a) +
              Point.Quadrance.quadrance point (symmetricSecondFocus a)) -
          associatedQuadrance ^ 2 =
        -16 * a ^ 2 * point.x ^ 2 +
          4 * associatedQuadrance *
            (point.x ^ 2 + point.y ^ 2 + a ^ 2) -
          associatedQuadrance ^ 2 := by
            unfold Point.Quadrance.quadrance symmetricFirstFocus
              symmetricSecondFocus
            ring1
    _ = -16 * i ^ 2 * a ^ 2 * point.y ^ 2 +
          4 * (associatedQuadrance - 4 * a ^ 2) *
            (point.x ^ 2 + point.y ^ 2 + i ^ 2 * a ^ 2) -
          (associatedQuadrance - 4 * a ^ 2) ^ 2 := by
            rw [iSquare]
            ring1
    _ = -(Point.Quadrance.quadrance point ⟨0, i * a⟩ -
            Point.Quadrance.quadrance point ⟨0, -(i * a)⟩) ^ 2 +
          2 * (associatedQuadrance - 4 * a ^ 2) *
            (Point.Quadrance.quadrance point ⟨0, i * a⟩ +
              Point.Quadrance.quadrance point ⟨0, -(i * a)⟩) -
          (associatedQuadrance - 4 * a ^ 2) ^ 2 := by
            unfold Point.Quadrance.quadrance
            ring1

/-- Example 15.5's alternate data satisfy all four quadrola nondegeneracy
clauses whenever the original symmetric data do. -/
theorem
  example_15_5_alternate_presentation
    (a associatedQuadrance i : K)
    (original :
      Conics.Quadrola.Presentation (symmetricFirstFocus a)
        (symmetricSecondFocus a)
        associatedQuadrance)
    (iSquare : i ^ 2 = -1) (eightNonzero : (8 : K) ≠ 0) :
    Conics.Quadrola.Presentation ⟨0, i * a⟩ ⟨0, -(i * a)⟩
      (associatedQuadrance - 4 * a ^ 2) := by
  have twoNonzero : (2 : K) ≠ 0 := by
    intro twoZero
    apply eightNonzero
    calc
      (8 : K) = 4 * 2 := by ring1
      _ = 0 := by rw [twoZero]; ring1
  have oneNonzero : (1 : K) ≠ 0 := by
    intro oneZero
    apply original.associatedNonzero
    calc
      associatedQuadrance = 1 * associatedQuadrance := by ring1
      _ = 0 := by rw [oneZero]; ring1
  have negativeOneNonzero : (-1 : K) ≠ 0 := by
    intro negativeOneZero
    apply oneNonzero
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [negativeOneZero]; ring1
  have iNonzero : i ≠ 0 := by
    intro iZero
    apply negativeOneNonzero
    calc
      (-1 : K) = i ^ 2 := iSquare.symm
      _ = 0 := by rw [iZero]; ring1
  have aNonzero : a ≠ 0 := by
    intro aZero
    apply original.focusQuadranceNonzero
    rw [example_15_5_focus_quadrance, aZero]
    ring1
  have iaNonzero : i * a ≠ 0 :=
    ExplicitField.mul_ne_zero iNonzero aNonzero
  have alternateFocusQuadrance :
      Point.Quadrance.quadrance (⟨0, i * a⟩ : Plane.Point K) ⟨0, -(i * a)⟩ =
        -4 * a ^ 2 := by
    calc
      Point.Quadrance.quadrance (⟨0, i * a⟩ : Plane.Point K) ⟨0, -(i * a)⟩ =
          4 * i ^ 2 * a ^ 2 := by
        unfold Point.Quadrance.quadrance
        ring1
      _ = -4 * a ^ 2 := by rw [iSquare]; ring1
  constructor
  · intro equal
    have yEqual := congrArg Plane.Point.y equal
    change i * a = -(i * a) at yEqual
    have addedEqual := congrArg (fun value : K => value + i * a) yEqual
    have twiceIaZero : (2 : K) * (i * a) = 0 := by
      calc
        (2 : K) * (i * a) = i * a + i * a := by ring1
        _ = -(i * a) + i * a := addedEqual
        _ = 0 := by ring1
    exact (ExplicitField.mul_ne_zero twoNonzero iaNonzero) twiceIaZero
  · intro associatedDifferenceZero
    apply original.focusQuadranceDifferent
    rw [example_15_5_focus_quadrance]
    calc
      4 * a ^ 2 = associatedQuadrance -
          (associatedQuadrance - 4 * a ^ 2) := by ring1
      _ = associatedQuadrance := by rw [associatedDifferenceZero]; ring1
  · intro alternateQuadranceZero
    apply original.focusQuadranceNonzero
    rw [example_15_5_focus_quadrance]
    calc
      4 * a ^ 2 = -(-4 * a ^ 2) := by ring1
      _ = -Point.Quadrance.quadrance (⟨0, i * a⟩ : Plane.Point K) ⟨0, -(i * a)⟩ := by
        rw [alternateFocusQuadrance]
      _ = 0 := by rw [alternateQuadranceZero]; ring1
  · intro sameQuadrance
    apply original.associatedNonzero
    calc
      associatedQuadrance =
          (associatedQuadrance - 4 * a ^ 2) - (-4 * a ^ 2) := by ring1
      _ = Point.Quadrance.quadrance (⟨0, i * a⟩ : Plane.Point K) ⟨0, -(i * a)⟩ -
          Point.Quadrance.quadrance (⟨0, i * a⟩ : Plane.Point K) ⟨0, -(i * a)⟩ := by
        rw [← sameQuadrance, alternateFocusQuadrance]
      _ = 0 := by ring1
end Quadrola

end formalisations.DivineProportions.Chapters.Examples.ChapterFifteen

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 15 worked examples

This module records the book's concrete finite-field conics separately from
the generic constructive proofs.  In particular, Example 15.6 is checked in
the executable eleven-element field without enumerating that field globally.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterFifteen

namespace ChapterFifteenExamples

variable {K : Type*} [ExplicitField K]
namespace ExampleFifteenSix

/-- The two displayed foci `[1,0]` and `[-1,0]`. -/
def firstFocus : Geometry.Plane.Point Finite.Eleven.Element := ⟨1, 0⟩

/-- The second symmetric focus (−1, 0) over the field with eleven elements. -/
def secondFocus : Geometry.Plane.Point Finite.Eleven.Element := ⟨-1, 0⟩

/-- The associated quadrance one is nonzero over the field with eleven elements. -/
theorem associated_nonzero : (1 : Finite.Eleven.Element) ≠ 0 := by decide

/-- Eight is nonzero over the field with eleven elements. -/
theorem eight_nonzero : (8 : Finite.Eleven.Element) ≠ 0 := by decide

/-- The displayed data satisfy all four clauses in the definition of a
quadrola. -/
theorem presentation : Geometry.Conics.Quadrola.Presentation firstFocus secondFocus 1 := by
  constructor
  · intro equal
    have xEqual := congrArg Geometry.Plane.Point.x equal
    change (1 : Finite.Eleven.Element) = -1 at xEqual
    exact (by decide : (1 : Finite.Eleven.Element) ≠ -1) xEqual
  · exact associated_nonzero
  · unfold Point.Quadrance.quadrance firstFocus secondFocus
    decide
  · unfold Point.Quadrance.quadrance firstFocus secondFocus
    decide

/-- The executable conic obtained directly from the Archimedes equation. -/
def quadrolaConic : Curves.Plane.Conic Finite.Eleven.Element :=
  Geometry.Conics.Quadrola.conic firstFocus secondFocus 1 associated_nonzero eight_nonzero

/-- The representative `⟨7:0:5:0:0:1⟩` printed in Example 15.6. -/
def printedConic : Curves.Plane.Conic Finite.Eleven.Element where
  d := 7
  e := 0
  f := 5
  a := 0
  b := 0
  c := 1
  quadratic_nonzero := Or.inl (by decide)

/-- The constructed coefficients are three times the printed representative.
This is the exact finite meaning of equality of the two conic proportions. -/
theorem coefficient_scale :
    quadrolaConic.d = 3 * printedConic.d ∧
      quadrolaConic.e = 3 * printedConic.e ∧
      quadrolaConic.f = 3 * printedConic.f ∧
      quadrolaConic.a = 3 * printedConic.a ∧
      quadrolaConic.b = 3 * printedConic.b ∧
      quadrolaConic.c = 3 * printedConic.c := by
  unfold quadrolaConic printedConic Geometry.Conics.Quadrola.conic
    Geometry.Conics.Quadrola.conicD
    Geometry.Conics.Quadrola.conicE Geometry.Conics.Quadrola.conicF
      Geometry.Conics.Quadrola.conicA Geometry.Conics.Quadrola.conicB
    Geometry.Conics.Quadrola.conicC firstFocus secondFocus
  decide

/-- Example 15.6: the quadrola locus is exactly the printed conic
`7x²+5y²+1=0` in `F₁₁`. -/
theorem example_15_6 (point : Geometry.Plane.Point Finite.Eleven.Element) :
    Geometry.Conics.Quadrola.Contains firstFocus secondFocus 1 point ↔
      printedConic.Contains point := by
  have definingEquation :
      Geometry.Conics.Quadrola.Contains firstFocus secondFocus 1 point ↔
        quadrolaConic.Contains point := by
    unfold Geometry.Conics.Quadrola.Contains Curves.Plane.Conic.Contains quadrolaConic
    rw [Geometry.Conics.Quadrola.conic_evaluate]
  rcases coefficient_scale with ⟨dScale, eScale, fScale, aScale, bScale,
    cScale⟩
  have sameLocus := Geometry.Conics.CoefficientScale.Locus.conic_contains_iff_of_coefficient_scale
    quadrolaConic printedConic 3 (by decide) dScale eScale fScale aScale
      bScale cScale point
  exact definingEquation.trans sameLocus

end ExampleFifteenSix

/-- The normalized first diagonal with coefficients (1/2, −1, 0), retaining the nonzero-two certificate. -/
private def halfFirstDiagonal (twoNonzero : (2 : K) ≠ 0) : Geometry.Plane.Line K where
  a := 1 / 2
  b := -1
  c := 0
  direction_nonzero := Or.inr (by
    intro negativeOneZero
    apply (fun {K : Type _} [ExplicitField K] (twoNonzero : (2 : K) ≠ 0) =>
      (Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero (K := K) twoNonzero : (1 : K) ≠ 0))
      twoNonzero
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [negativeOneZero]; ring1)

/-- The normalized second diagonal with coefficients (1/2, 1, 0), retaining the nonzero-two certificate. -/
private def halfSecondDiagonal (twoNonzero : (2 : K) ≠ 0) : Geometry.Plane.Line K where
  a := 1 / 2
  b := 1
  c := 0
  direction_nonzero := Or.inr ((fun {K : Type _} [ExplicitField K] (twoNonzero : (2 : K) ≠ 0) =>
    (Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero (K := K) twoNonzero : (1 : K) ≠ 0))
    twoNonzero)

/-- The integral first diagonal with coefficients (1, −2, 0). -/
private def integerFirstDiagonal (twoNonzero : (2 : K) ≠ 0) : Geometry.Plane.Line K where
  a := 1
  b := -2
  c := 0
  direction_nonzero := Or.inl ((fun {K : Type _} [ExplicitField K] (twoNonzero : (2 : K) ≠ 0) =>
    (Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero (K := K) twoNonzero : (1 : K) ≠ 0))
    twoNonzero)

/-- The integral second diagonal with coefficients (1, 2, 0). -/
private def integerSecondDiagonal (twoNonzero : (2 : K) ≠ 0) : Geometry.Plane.Line K where
  a := 1
  b := 2
  c := 0
  direction_nonzero := Or.inl ((fun {K : Type _} [ExplicitField K] (twoNonzero : (2 : K) ≠ 0) =>
    (Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero (K := K) twoNonzero : (1 : K) ≠ 0))
    twoNonzero)

/-- The normalized half-coefficient diagonals are equivalent to their integral representatives when two is nonzero. -/
private theorem half_diagonals_equivalent
    (twoNonzero : (2 : K) ≠ 0) :
    (halfFirstDiagonal twoNonzero).Equivalent
        (integerFirstDiagonal twoNonzero) ∧
      (halfSecondDiagonal twoNonzero).Equivalent
        (integerSecondDiagonal twoNonzero) := by
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
  unfold halfFirstDiagonal halfSecondDiagonal integerFirstDiagonal
    integerSecondDiagonal Geometry.Plane.Line.Equivalent
  simp only [ExplicitField.div_eq_mul_inv]
  refine ⟨⟨?_, by ring1, by ring1⟩, ⟨?_, by ring1, by ring1⟩⟩
  · calc
      ((1 : K) * (2 : K)⁻¹) * -2 =
          -(2 * (2 : K)⁻¹) := by ring1
      _ = -1 := by rw [twoCancel]
      _ = 1 * -1 := by ring1
  · calc
      ((1 : K) * (2 : K)⁻¹) * 2 =
          2 * (2 : K)⁻¹ := by ring1
      _ = 1 := twoCancel
      _ = 1 * 1 := by ring1

namespace ExampleFifteenEight

/-- The printed diagonal `x-2y=0`. -/
def firstDiagonal : Geometry.Plane.Line Fraction.Rational where
  a := 1
  b := -2
  c := 0
  direction_nonzero := Or.inl (by decide)

/-- The printed diagonal `x+2y=0`. -/
def secondDiagonal : Geometry.Plane.Line Fraction.Rational where
  a := 1
  b := 2
  c := 0
  direction_nonzero := Or.inl (by decide)

/-- The rational diagonal x − 2y = 0 has nonzero norm. -/
theorem first_nonNull : ¬ firstDiagonal.IsNull := by
  rw [firstDiagonal.eq_1]
  unfold Geometry.Plane.Line.IsNull
  decide

/-- The rational diagonal x + 2y = 0 has nonzero norm. -/
theorem second_nonNull : ¬ secondDiagonal.IsNull := by
  rw [secondDiagonal.eq_1]
  unfold Geometry.Plane.Line.IsNull
  decide

/-- Two is nonzero in the rational coefficient field. -/
theorem two_nonzero : (2 : Fraction.Rational) ≠ 0 := by decide

/-- The exact `a=1/2` normalization of the first Example 15.7 diagonal. -/
def normalizedFirstDiagonal : Geometry.Plane.Line Fraction.Rational where
  a := 1 / 2
  b := -1
  c := 0
  direction_nonzero := Or.inr (by
    intro negativeOneZero
    have oneNonzero : (1 : Fraction.Rational) ≠ 0 := by
      intro oneZero
      apply two_nonzero
      calc
        (2 : Fraction.Rational) = 2 * 1 := by ring1
        _ = 0 := by rw [oneZero]; ring1
    apply oneNonzero
    calc
      (1 : Fraction.Rational) = -(-1) := by ring1
      _ = 0 := by rw [negativeOneZero]; ring1)

/-- The exact `a=1/2` normalization of the second Example 15.7 diagonal. -/
def normalizedSecondDiagonal : Geometry.Plane.Line Fraction.Rational where
  a := 1 / 2
  b := 1
  c := 0
  direction_nonzero := Or.inr (by
    intro oneZero
    apply two_nonzero
    calc
      (2 : Fraction.Rational) = 2 * 1 := by ring1
      _ = 0 := by rw [oneZero]; ring1)

/-- The exact rational data satisfy the grammola definition. -/
theorem presentation : Geometry.Conics.Grammola.Presentation firstDiagonal secondDiagonal 1 := by
  refine ⟨first_nonNull, second_nonNull, ?_, ?_, by decide⟩
  · unfold Geometry.Plane.Line.Parallel firstDiagonal secondDiagonal
    decide
  · unfold Geometry.Plane.Line.Perpendicular firstDiagonal secondDiagonal
    decide

/-- The cleared metric construction before rescaling its six coefficients. -/
def constructedConic : Curves.Plane.Conic Fraction.Rational :=
  Geometry.Conics.Grammola.conic firstDiagonal secondDiagonal first_nonNull second_nonNull 1
    two_nonzero

/-- Example 15.8's conic `2x²+8y²=5`. -/
def printedConic : Curves.Plane.Conic Fraction.Rational where
  d := 2
  e := 0
  f := 8
  a := 0
  b := 0
  c := -5
  quadratic_nonzero := Or.inl (by decide)

/-- Clearing the two line norms produces five times the printed conic. -/
theorem coefficient_scale :
    constructedConic.d = 5 * printedConic.d ∧
      constructedConic.e = 5 * printedConic.e ∧
      constructedConic.f = 5 * printedConic.f ∧
      constructedConic.a = 5 * printedConic.a ∧
      constructedConic.b = 5 * printedConic.b ∧
      constructedConic.c = 5 * printedConic.c := by
  unfold constructedConic printedConic Geometry.Conics.Grammola.conic
    Geometry.Conics.Grammola.conicD
    Geometry.Conics.Grammola.conicE Geometry.Conics.Grammola.conicF
      Geometry.Conics.Grammola.conicA Geometry.Conics.Grammola.conicB
    Geometry.Conics.Grammola.conicC Line.Basic.lineNorm firstDiagonal secondDiagonal
  decide

/-- The `a=1/2` representatives in Example 15.7 are the same two lines as
the integer representatives printed in Example 15.8. -/
theorem normalized_diagonals :
    normalizedFirstDiagonal.Equivalent firstDiagonal ∧
      normalizedSecondDiagonal.Equivalent secondDiagonal := by
  have twoCancel : (2 : Fraction.Rational) * (2 : Fraction.Rational)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 two_nonzero
  rw [normalizedFirstDiagonal.eq_1, normalizedSecondDiagonal.eq_1]
  unfold Geometry.Plane.Line.Equivalent firstDiagonal secondDiagonal
  simp only [ExplicitField.div_eq_mul_inv]
  refine ⟨⟨?_, by ring1, by ring1⟩, ⟨?_, by ring1, by ring1⟩⟩
  · calc
      ((1 : Fraction.Rational) * (2 : Fraction.Rational)⁻¹) * -2 =
          -(2 * (2 : Fraction.Rational)⁻¹) := by ring1
      _ = -1 := by rw [twoCancel]
      _ = 1 * -1 := by ring1
  · calc
      ((1 : Fraction.Rational) * (2 : Fraction.Rational)⁻¹) * 2 =
          2 * (2 : Fraction.Rational)⁻¹ := by ring1
      _ = 1 := twoCancel
      _ = 1 * 1 := by ring1

/-- Membership in the displayed rational conic is exactly the equation 2x² + 8y² = 5. -/
theorem printed_equation (point : Geometry.Plane.Point Fraction.Rational) :
    printedConic.Contains point ↔
      2 * point.x ^ 2 + 8 * point.y ^ 2 = 5 := by
  unfold Curves.Plane.Conic.Contains
  constructor
  · intro polynomialZero
    change
      2 * point.x ^ 2 + 0 * point.x * point.y + 8 * point.y ^ 2 +
        0 * point.x + 0 * point.y + (-5) = 0 at polynomialZero
    calc
      2 * point.x ^ 2 + 8 * point.y ^ 2 =
          (2 * point.x ^ 2 + 0 * point.x * point.y +
            8 * point.y ^ 2 + 0 * point.x + 0 * point.y + (-5)) + 5 := by
        ring1
      _ = 5 := by rw [polynomialZero]; ring1
  · intro equation
    change
      2 * point.x ^ 2 + 0 * point.x * point.y + 8 * point.y ^ 2 +
        0 * point.x + 0 * point.y + (-5) = 0
    calc
      2 * point.x ^ 2 + 0 * point.x * point.y +
          8 * point.y ^ 2 + 0 * point.x + 0 * point.y + (-5) =
        (2 * point.x ^ 2 + 8 * point.y ^ 2) - 5 := by ring1
      _ = 0 := by rw [equation]; ring1

/-- Example 15.8: the exact rational grammola equation is the displayed
conic `2x²+8y²=5`. -/
theorem example_15_8 (point : Geometry.Plane.Point Fraction.Rational) :
    Geometry.Conics.Grammola.Contains firstDiagonal secondDiagonal first_nonNull second_nonNull
        1 point ↔
      2 * point.x ^ 2 + 8 * point.y ^ 2 = 5 := by
  have metricToConstructed :=
    (Geometry.Conics.Grammola.conic_contains_iff firstDiagonal secondDiagonal first_nonNull
      second_nonNull 1 two_nonzero point).symm
  rcases coefficient_scale with ⟨dScale, eScale, fScale, aScale, bScale,
    cScale⟩
  have constructedToPrinted := Geometry.Conics.CoefficientScale.Locus.conic_contains_iff_of_coefficient_scale
    constructedConic printedConic 5 (by decide) dScale eScale fScale aScale
      bScale cScale point
  exact metricToConstructed.trans (constructedToPrinted.trans (printed_equation point))

end ExampleFifteenEight

/-- Example 15.8's four distinguished points, stated over any constructive
field in which a displayed square root of five is supplied. -/
theorem example_15_8_distinguished_points
    (root : K) (rootSquare : root ^ 2 = 5)
    (twoNonzero : (2 : K) ≠ 0) (fourNonzero : (4 : K) ≠ 0) :
    let x := root / 2
    let y := root / 4
    2 * x ^ 2 + 8 * y ^ 2 = 5 ∧
      2 * x ^ 2 + 8 * (-y) ^ 2 = 5 ∧
      2 * (-x) ^ 2 + 8 * y ^ 2 = 5 ∧
      2 * (-x) ^ 2 + 8 * (-y) ^ 2 = 5 := by
  dsimp only
  have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
  have fourCancel : (4 : K) * (4 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 4 fourNonzero
  have candidateFourCancel :
      (4 : K) * ((2 : K)⁻¹ * (2 : K)⁻¹) = 1 := by
    calc
      (4 : K) * ((2 : K)⁻¹ * (2 : K)⁻¹) =
          (2 * (2 : K)⁻¹) ^ 2 := by ring1
      _ = 1 := by rw [twoCancel]; ring1
  have inverseFour : (4 : K)⁻¹ = (2 : K)⁻¹ * (2 : K)⁻¹ := by
    calc
      (4 : K)⁻¹ = 1 * (4 : K)⁻¹ := by ring1
      _ = (4 * ((2 : K)⁻¹ * (2 : K)⁻¹)) * (4 : K)⁻¹ := by
        rw [candidateFourCancel]
      _ = ((2 : K)⁻¹ * (2 : K)⁻¹) * (4 * (4 : K)⁻¹) := by
        ring1
      _ = (2 : K)⁻¹ * (2 : K)⁻¹ := by rw [fourCancel]; ring1
  have positive :
      2 * (root / 2) ^ 2 + 8 * (root / 4) ^ 2 = 5 := by
    simp only [ExplicitField.div_eq_mul_inv, inverseFour]
    calc
      2 * (root * (2 : K)⁻¹) ^ 2 +
          8 * (root * ((2 : K)⁻¹ * (2 : K)⁻¹)) ^ 2 =
        root ^ 2 + root ^ 2 * (2 * (2 : K)⁻¹ - 1) *
          (4 * (2 : K)⁻¹ ^ 3 + 2 * (2 : K)⁻¹ ^ 2 +
            2 * (2 : K)⁻¹ + 1) := by ring1
      _ = root ^ 2 := by rw [twoCancel]; ring1
      _ = 5 := rootSquare
  have negativeX : (-(root / 2)) ^ 2 = (root / 2) ^ 2 := by ring1
  have negativeY : (-(root / 4)) ^ 2 = (root / 4) ^ 2 := by ring1
  exact ⟨positive, by rewrite [negativeY]; exact positive,
    by rewrite [negativeX]; exact positive,
    by rewrite [negativeX, negativeY]; exact positive⟩

namespace ExampleFifteenNine

/-- The diagonal x − 2y = 0 over the field with eleven elements. -/
def firstDiagonal : Geometry.Plane.Line Finite.Eleven.Element where
  a := 1
  b := -2
  c := 0
  direction_nonzero := Or.inl (by decide)

/-- The diagonal x + 2y = 0 over the field with eleven elements. -/
def secondDiagonal : Geometry.Plane.Line Finite.Eleven.Element where
  a := 1
  b := 2
  c := 0
  direction_nonzero := Or.inl (by decide)

/-- The first displayed characteristic-eleven diagonal has nonzero norm. -/
theorem first_nonNull : ¬ firstDiagonal.IsNull := by
  unfold Geometry.Plane.Line.IsNull firstDiagonal
  decide

/-- The second displayed characteristic-eleven diagonal has nonzero norm. -/
theorem second_nonNull : ¬ secondDiagonal.IsNull := by
  unfold Geometry.Plane.Line.IsNull secondDiagonal
  decide

/-- Two is nonzero over the field with eleven elements. -/
theorem two_nonzero : (2 : Finite.Eleven.Element) ≠ 0 := by decide

/-- The two displayed characteristic-eleven diagonals and associated quadrance one form a grammola presentation. -/
theorem presentation : Geometry.Conics.Grammola.Presentation firstDiagonal secondDiagonal 1 := by
  refine ⟨first_nonNull, second_nonNull, ?_, ?_, by decide⟩
  · unfold Geometry.Plane.Line.Parallel firstDiagonal secondDiagonal
    decide
  · unfold Geometry.Plane.Line.Perpendicular firstDiagonal secondDiagonal
    decide

/-- The characteristic-eleven conic obtained by clearing the two diagonal norms in the grammola equation. -/
def constructedConic : Curves.Plane.Conic Finite.Eleven.Element :=
  Geometry.Conics.Grammola.conic firstDiagonal secondDiagonal first_nonNull second_nonNull 1
    two_nonzero

/-- The `F₁₁` representative `2x²+8y²-5=0`. -/
def printedConic : Curves.Plane.Conic Finite.Eleven.Element where
  d := 2
  e := 0
  f := 8
  a := 0
  b := 0
  c := -5
  quadratic_nonzero := Or.inl (by decide)

/-- The constructed characteristic-eleven conic has coefficients five times those of the printed representative. -/
theorem coefficient_scale :
    constructedConic.d = 5 * printedConic.d ∧
      constructedConic.e = 5 * printedConic.e ∧
      constructedConic.f = 5 * printedConic.f ∧
      constructedConic.a = 5 * printedConic.a ∧
      constructedConic.b = 5 * printedConic.b ∧
      constructedConic.c = 5 * printedConic.c := by
  unfold constructedConic printedConic Geometry.Conics.Grammola.conic
    Geometry.Conics.Grammola.conicD
    Geometry.Conics.Grammola.conicE Geometry.Conics.Grammola.conicF
      Geometry.Conics.Grammola.conicA Geometry.Conics.Grammola.conicB
    Geometry.Conics.Grammola.conicC Line.Basic.lineNorm firstDiagonal secondDiagonal
  decide

/-- The point (2, 1) over the field with eleven elements. -/
def point21 : Geometry.Plane.Point Finite.Eleven.Element := ⟨2, 1⟩
/-- The point (2, −1) over the field with eleven elements. -/
def point2Neg1 : Geometry.Plane.Point Finite.Eleven.Element := ⟨2, -1⟩
/-- The point (−2, 1) over the field with eleven elements. -/
def pointNeg21 : Geometry.Plane.Point Finite.Eleven.Element := ⟨-2, 1⟩
/-- The point (−2, −1) over the field with eleven elements. -/
def pointNeg2Neg1 : Geometry.Plane.Point Finite.Eleven.Element := ⟨-2, -1⟩

/-- Example 15.9: the four displayed points lie on the grammola and split
between its two displayed diagonal lines exactly as in the figure. -/
theorem example_15_9 :
    printedConic.Contains point21 ∧ printedConic.Contains point2Neg1 ∧
      printedConic.Contains pointNeg21 ∧
      printedConic.Contains pointNeg2Neg1 ∧
      firstDiagonal.Contains point21 ∧
      firstDiagonal.Contains pointNeg2Neg1 ∧
      secondDiagonal.Contains point2Neg1 ∧
      secondDiagonal.Contains pointNeg21 := by
  unfold Curves.Plane.Conic.Contains Curves.Plane.Conic.evaluate Geometry.Plane.Line.Contains
    printedConic firstDiagonal
    secondDiagonal point21 point2Neg1 pointNeg21 pointNeg2Neg1
  decide

/-- The metrical `F₁₁` grammola and the printed conic have the same
locus. -/
theorem metric_locus (point : Geometry.Plane.Point Finite.Eleven.Element) :
    Geometry.Conics.Grammola.Contains firstDiagonal secondDiagonal first_nonNull second_nonNull
        1 point ↔
      printedConic.Contains point := by
  have metricToConstructed :=
    (Geometry.Conics.Grammola.conic_contains_iff firstDiagonal secondDiagonal first_nonNull
      second_nonNull 1 two_nonzero point).symm
  rcases coefficient_scale with ⟨dScale, eScale, fScale, aScale, bScale,
    cScale⟩
  have constructedToPrinted := Geometry.Conics.CoefficientScale.Locus.conic_contains_iff_of_coefficient_scale
    constructedConic printedConic 5 (by decide) dScale eScale fScale aScale
      bScale cScale point
  exact metricToConstructed.trans constructedToPrinted

end ExampleFifteenNine

namespace ExerciseFifteenSixteen

/-- A focal pair for the printed grammola: its vertical separation has
quadrance nine. -/
def firstFocus : Geometry.Plane.Point Finite.Eleven.Element := ⟨0, 4⟩

/-- The second vertical focus (0, 7) over the field with eleven elements. -/
def secondFocus : Geometry.Plane.Point Finite.Eleven.Element := ⟨0, 7⟩

/-- The associated quadrance eight is nonzero over the field with eleven elements. -/
theorem associated_nonzero : (8 : Finite.Eleven.Element) ≠ 0 := by decide

/-- Eight is nonzero over the field with eleven elements. -/
theorem eight_nonzero : (8 : Finite.Eleven.Element) ≠ 0 := by decide

/-- The counterexample's focal data satisfy every quadrola nondegeneracy
clause. -/
theorem presentation : Geometry.Conics.Quadrola.Presentation firstFocus secondFocus 8 := by
  constructor
  · intro equal
    have yEqual := congrArg Geometry.Plane.Point.y equal
    change (4 : Finite.Eleven.Element) = 7 at yEqual
    exact (by decide : (4 : Finite.Eleven.Element) ≠ 7) yEqual
  · exact associated_nonzero
  · unfold Point.Quadrance.quadrance firstFocus secondFocus
    decide
  · unfold Point.Quadrance.quadrance firstFocus secondFocus
    decide

/-- The characteristic-eleven quadrola conic with vertical foci (0, 4), (0, 7) and associated quadrance eight. -/
def quadrolaConic : Curves.Plane.Conic Finite.Eleven.Element :=
  Geometry.Conics.Quadrola.conic firstFocus secondFocus 8 associated_nonzero eight_nonzero

/-- The constructed quadrola coefficients are five times the very conic
which Exercise 15.16 claims is not a quadrola. -/
theorem coefficientScale :
    Curves.Plane.Conic.Scale.CoefficientScale quadrolaConic
      ExampleFifteenNine.printedConic 5 := by
  constructor <;>
    unfold quadrolaConic ExampleFifteenNine.printedConic Geometry.Conics.Quadrola.conic
      Geometry.Conics.Quadrola.conicD Geometry.Conics.Quadrola.conicE
        Geometry.Conics.Quadrola.conicF Geometry.Conics.Quadrola.conicA
      Geometry.Conics.Quadrola.conicB Geometry.Conics.Quadrola.conicC firstFocus
        secondFocus <;>
    decide

/-- Exercise 15.16 is false as printed: the displayed `F₁₁` grammola is the
same conic proportion as this valid quadrola with associated quadrance eight. -/
theorem exercise_15_16_printed_counterexample :
    Geometry.Conics.Quadrola.Presentation firstFocus secondFocus 8 ∧
      Curves.Plane.Conic.Scale.CoefficientScale quadrolaConic
        ExampleFifteenNine.printedConic 5 :=
  ⟨presentation, coefficientScale⟩

/-- The metric quadrola equation and the printed grammola equation therefore
have exactly the same finite locus. -/
theorem same_locus (point : Geometry.Plane.Point Finite.Eleven.Element) :
    Geometry.Conics.Quadrola.Contains firstFocus secondFocus 8 point ↔
      ExampleFifteenNine.printedConic.Contains point := by
  have definingEquation :
      Geometry.Conics.Quadrola.Contains firstFocus secondFocus 8 point ↔
        quadrolaConic.Contains point := by
    unfold Geometry.Conics.Quadrola.Contains Curves.Plane.Conic.Contains quadrolaConic
    rw [Geometry.Conics.Quadrola.conic_evaluate]
  have coefficientLocus := Geometry.Conics.CoefficientScale.Locus.conic_contains_iff_of_coefficient_scale
    quadrolaConic ExampleFifteenNine.printedConic 5 (by decide)
      coefficientScale.d coefficientScale.e coefficientScale.f
      coefficientScale.a coefficientScale.b coefficientScale.c point
  exact definingEquation.trans coefficientLocus

end ExerciseFifteenSixteen

namespace ExerciseFifteenSeventeen

/-- The two rationally displayed foci used for a quadrola whose quadratic
trace vanishes. -/
def firstFocus (K : Type*) [ExplicitField K] : Geometry.Plane.Point K := ⟨1, 0⟩

/-- The second focus (−1, 0) of the zero-trace quadrola. -/
def secondFocus (K : Type*) [ExplicitField K] : Geometry.Plane.Point K := ⟨-1, 0⟩

/-- The two symmetric foci have quadrance four. -/
theorem focus_quadrance :
    Point.Quadrance.quadrance (firstFocus K) (secondFocus K) = 4 := by
  unfold Point.Quadrance.quadrance firstFocus secondFocus
  ring1

/-- The example has nonzero associated quadrance two and focal quadrance
four, so it is a valid quadrola over every constructive field outside
characteristic two. -/
theorem presentation (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Conics.Quadrola.Presentation (firstFocus K) (secondFocus K) 2 := by
  constructor
  · intro equal
    have xEqual := congrArg Geometry.Plane.Point.x equal
    apply twoNonzero
    calc
      (2 : K) = 1 - (-1) := by ring1
      _ = (firstFocus K).x - (secondFocus K).x := by rfl
      _ = 0 := by rw [xEqual]; ring1
  · exact twoNonzero
  · rw [focus_quadrance]
    exact (fun {K : Type _} [ExplicitField K] (twoNonzero : (2 : K) ≠ 0) =>
      (Purelib.Algebra.Field.Characteristic.Nonzero.four_ne_zero (K := K) twoNonzero : (4 : K) ≠ 0)) twoNonzero
  · intro equalQuadrance
    apply twoNonzero
    calc
      (2 : K) = 4 - 2 := by ring1
      _ = Point.Quadrance.quadrance (firstFocus K) (secondFocus K) - 2 := by
        rw [focus_quadrance]
      _ = 0 := by rw [equalQuadrance]; ring1

/-- The quadrola conic with foci (1, 0), (−1, 0) and associated quadrance two.

Its construction retains the nonzero-two certificate, which also supplies the required nonzero-eight denominator
condition. -/
def exampleConic [DecidableEq K] (twoNonzero : (2 : K) ≠ 0) : Curves.Plane.Conic K :=
  Geometry.Conics.Quadrola.conic (firstFocus K) (secondFocus K) 2 twoNonzero
    (by
      have eightAsProduct : (8 : K) = (2 * 2) * 2 := by ring1
      rw [eightAsProduct]
      exact ExplicitField.mul_ne_zero
        (ExplicitField.mul_ne_zero twoNonzero twoNonzero)
        twoNonzero)

/-- The example's two square coefficients are opposites. -/
theorem example_trace_zero [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    (exampleConic twoNonzero).d + (exampleConic twoNonzero).f = 0 := by
  unfold exampleConic Geometry.Conics.Quadrola.conic Geometry.Conics.Quadrola.conicD
    Geometry.Conics.Quadrola.conicF
    firstFocus secondFocus
  ring1

/-- Exercise 15.17: the displayed quadrola cannot be proportional to any
grammola conic, in either coefficient-scale direction.  The proof uses only
the zero/nonzero quadratic-trace invariant. -/
theorem exercise_15_17 [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    Geometry.Conics.Quadrola.Presentation (firstFocus K) (secondFocus K) 2 ∧
      ∀ (firstDiagonal secondDiagonal : Geometry.Plane.Line K)
        (associatedQuadrance : K)
        (grammolaPresentation :
          Geometry.Conics.Grammola.Presentation firstDiagonal secondDiagonal
            associatedQuadrance)
        (scale : K), scale ≠ 0 →
          (¬ Curves.Plane.Conic.Scale.CoefficientScale (exampleConic twoNonzero)
            (Geometry.Conics.Grammola.conic firstDiagonal secondDiagonal
              grammolaPresentation.firstNonNull
              grammolaPresentation.secondNonNull associatedQuadrance
              twoNonzero) scale) ∧
          (¬ Curves.Plane.Conic.Scale.CoefficientScale
            (Geometry.Conics.Grammola.conic firstDiagonal secondDiagonal
              grammolaPresentation.firstNonNull
              grammolaPresentation.secondNonNull associatedQuadrance
              twoNonzero) (exampleConic twoNonzero) scale) := by
  refine ⟨presentation twoNonzero, ?_⟩
  intro firstDiagonal secondDiagonal associatedQuadrance
    grammolaPresentation scale scaleNonzero
  let grammolaConic :=
    Geometry.Conics.Grammola.conic firstDiagonal secondDiagonal
      grammolaPresentation.firstNonNull
      grammolaPresentation.secondNonNull associatedQuadrance twoNonzero
  have grammolaTraceNonzero : grammolaConic.d + grammolaConic.f ≠ 0 := by
    unfold grammolaConic
    exact Geometry.Conics.Grammola.conic_trace_nonzero firstDiagonal secondDiagonal
      grammolaPresentation.firstNonNull
      grammolaPresentation.secondNonNull associatedQuadrance twoNonzero
  constructor
  · intro exampleScaled
    have scaledTrace :
        (exampleConic twoNonzero).d + (exampleConic twoNonzero).f =
          scale * (grammolaConic.d + grammolaConic.f) := by
      rw [exampleScaled.d, exampleScaled.f]
      ring1
    have scaledTraceNonzero :
        scale * (grammolaConic.d + grammolaConic.f) ≠ 0 :=
      ExplicitField.mul_ne_zero scaleNonzero grammolaTraceNonzero
    apply scaledTraceNonzero
    calc
      scale * (grammolaConic.d + grammolaConic.f) =
          (exampleConic twoNonzero).d + (exampleConic twoNonzero).f :=
        scaledTrace.symm
      _ = 0 := example_trace_zero twoNonzero
  · intro grammolaScaled
    apply grammolaTraceNonzero
    calc
      grammolaConic.d + grammolaConic.f =
          scale *
            ((exampleConic twoNonzero).d + (exampleConic twoNonzero).f) := by
        rw [grammolaScaled.d, grammolaScaled.f]
        ring1
      _ = 0 := by rw [example_trace_zero]; ring1

end ExerciseFifteenSeventeen

end ChapterFifteenExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterFifteen

end
