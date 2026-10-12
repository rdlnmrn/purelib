module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Negation
public import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Polynomial.Quadratic.CommonRoot.Centered
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib

open Purelib.Geometry.Trigonometry.Spread

open Purelib.Geometry.Trigonometry.Spread.Triple

open Purelib.Polynomial.Quadratic.CommonRoot

section
@[expose] public section

/-!
# Divine Proportions, §7.7: quadruple spread and cross formulas

The scalar elimination is kept separate from the geometric specialization.
Two displayed spread triples give two explicit quadratic equations with a
common root; the finite quadratic-compatibility calculation then yields the
four-variable polynomial.
-/

namespace Purelib.Geometry.Trigonometry.Spread.Quadruple

variable {K : Type*} [ExplicitField K]

/-- The inner symmetric polynomial in the quadruple spread function.

The polynomial retains its four-variable square term, sum of individual
squares, cubic products and quartic product with their displayed coefficients. -/
def quadrupleSpreadCore (a b c d : K) : K :=
  (a + b + c + d) ^ 2 - 2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) -
    4 * (a * b * c + a * b * d + a * c * d + b * c * d) +
    8 * a * b * c * d

/-- The quadruple spread polynomial in four displayed scalars.

It subtracts the product of the four scalars and their complements, scaled
by `64`, from the square of the retained inner symmetric polynomial. -/
def quadrupleSpreadFunction (a b c d : K) : K :=
  quadrupleSpreadCore a b c d ^ 2 -
    64 * a * b * c * d * (1 - a) * (1 - b) * (1 - c) * (1 - d)

/-- Two spread triples with a common entry satisfy the quadruple-spread polynomial.

The two retained triples give centered quadratic equations for their shared
entry. Their common solution yields the displayed four-variable relation,
without requiring the centers to be distinct. -/
theorem two_spread_triples_compatibility
    (a b c d x : K)
    (firstTriple : TripleSpread.SpreadTriple a b x)
    (secondTriple : TripleSpread.SpreadTriple c d x) :
    quadrupleSpreadFunction a b c d = 0 := by
  let firstCenter := a + b - 2 * a * b
  let firstSquare := 4 * a * b * (1 - a) * (1 - b)
  let secondCenter := c + d - 2 * c * d
  let secondSquare := 4 * c * d * (1 - c) * (1 - d)
  have firstNormal := (Triple.exercise_7_6 firstTriple).2.2.2.2
  have secondNormal := (Triple.exercise_7_6 secondTriple).2.2.2.2
  change (x - firstCenter) ^ 2 = firstSquare at firstNormal
  change (x - secondCenter) ^ 2 = secondSquare at secondNormal
  have compatible : Centered.QuadraticsCompatible firstCenter firstSquare
      secondCenter secondSquare :=
    ⟨x, firstNormal, secondNormal⟩
  have identity := Centered.quadraticCompatibilityIdentity_of_compatible compatible
  unfold Centered.quadraticCompatibilityIdentity at identity
  unfold quadrupleSpreadFunction
  have coreIdentity :
      quadrupleSpreadCore a b c d ^ 2 =
        64 * a * b * c * d * (1 - a) * (1 - b) *
          (1 - c) * (1 - d) := by
    calc
      quadrupleSpreadCore a b c d ^ 2 =
          ((firstCenter - secondCenter) ^ 2 -
            (firstSquare + secondSquare)) ^ 2 := by
              unfold quadrupleSpreadCore firstCenter firstSquare
                secondCenter secondSquare
              ring1
      _ = 4 * firstSquare * secondSquare := identity
      _ = 64 * a * b * c * d * (1 - a) * (1 - b) *
          (1 - c) * (1 - d) := by
            unfold firstSquare secondSquare
            ring1
  rw [coreIdentity]
  ring1

/-- Distinct quadratic centers determine the common entry of two spread triples.

The supplied nonzero two and distinct centers certify the denominator. The
common entry equals the displayed quotient of the difference of two squares
by twice the difference of the two retained quadratic centers. -/
theorem two_spread_triples_common_value
    (a b c d x : K)
    (twoNonzero : (2 : K) ≠ 0)
    (firstTriple : TripleSpread.SpreadTriple a b x)
    (secondTriple : TripleSpread.SpreadTriple c d x)
    (centersDistinct :
      a + b - 2 * a * b ≠ c + d - 2 * c * d) :
    let denominator := 2 * (a + b - c - d - 2 * a * b + 2 * c * d)
    denominator ≠ 0 ∧
      x = ((a - b) ^ 2 - (c - d) ^ 2) / denominator := by
  dsimp only
  let firstCenter := a + b - 2 * a * b
  let firstSquare := 4 * a * b * (1 - a) * (1 - b)
  let secondCenter := c + d - 2 * c * d
  let secondSquare := 4 * c * d * (1 - c) * (1 - d)
  let denominator := 2 * (firstCenter - secondCenter)
  let numerator := (a - b) ^ 2 - (c - d) ^ 2
  have firstNormal := (Triple.exercise_7_6 firstTriple).2.2.2.2
  have secondNormal := (Triple.exercise_7_6 secondTriple).2.2.2.2
  change (x - firstCenter) ^ 2 = firstSquare at firstNormal
  change (x - secondCenter) ^ 2 = secondSquare at secondNormal
  have centerDifferenceNonzero : firstCenter - secondCenter ≠ 0 :=
    ExplicitField.sub_ne_zero_of_ne centersDistinct
  have denominatorNonzero : denominator ≠ 0 :=
    ExplicitField.mul_ne_zero twoNonzero centerDifferenceNonzero
  have clearedEquation : denominator * x = numerator := by
    calc
      denominator * x =
          firstCenter ^ 2 - secondCenter ^ 2 -
            (x - firstCenter) ^ 2 + (x - secondCenter) ^ 2 := by
              unfold denominator
              ring1
      _ = firstCenter ^ 2 - secondCenter ^ 2 -
          firstSquare + secondSquare := by rw [firstNormal, secondNormal]
      _ = numerator := by
        unfold firstCenter secondCenter firstSquare secondSquare numerator
        ring1
  have valueEquation : x = numerator / denominator := by
    have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
      ExplicitField.mul_inv_cancel denominator denominatorNonzero
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      x = x * 1 := by rw [mul_one]
      _ = x * (denominator * denominator⁻¹) := by rw [denominatorCancel]
      _ = (denominator * x) * denominator⁻¹ := by ring1
      _ = numerator * denominator⁻¹ := by rw [clearedEquation]
  have denominatorEquation :
      denominator =
        2 * (a + b - c - d - 2 * a * b + 2 * c * d) := by
    unfold denominator firstCenter secondCenter
    ring1
  have numeratorEquation :
      numerator = (a - b) ^ 2 - (c - d) ^ 2 := by
    rfl
  rw [← denominatorEquation, ← numeratorEquation]
  exact ⟨denominatorNonzero, valueEquation⟩

/-- Two spread triples give the quadruple relation and the conditional common-entry quotient.

The four-variable relation holds for every supplied pair of triples with a
common entry. When their quadratic centers differ, the nonzero-two witness
also supplies the denominator certificate and the common-entry identity. -/
theorem two_spread_triples
    (a b c d x : K)
    (twoNonzero : (2 : K) ≠ 0)
    (firstTriple : TripleSpread.SpreadTriple a b x)
    (secondTriple : TripleSpread.SpreadTriple c d x) :
    quadrupleSpreadFunction a b c d = 0 ∧
      (a + b - 2 * a * b ≠ c + d - 2 * c * d →
        let denominator :=
          2 * (a + b - c - d - 2 * a * b + 2 * c * d)
        denominator ≠ 0 ∧
          x = ((a - b) ^ 2 - (c - d) ^ 2) / denominator) := by
  exact ⟨two_spread_triples_compatibility a b c d x firstTriple secondTriple,
    fun centersDistinct => two_spread_triples_common_value a b c d x
      twoNonzero firstTriple secondTriple centersDistinct⟩

/-- Two adjacent spread triples determine their common entry by one explicit quotient.

The distinct outer entries and the middle entry's separation from one half
certify the displayed denominator is nonzero. The supplied `(2:K) ≠ 0`
witness excludes characteristic two and supports the division identity. -/
theorem exercise_7_13
    [DecidableEq K] (a b c x : K)
    (twoNonzero : (2 : K) ≠ 0)
    (firstTriple : TripleSpread.SpreadTriple a b x)
    (secondTriple : TripleSpread.SpreadTriple b c x)
    (outerDistinct : a ≠ c)
    (middleNotHalf : b ≠ (1 : K) / 2) :
    let denominator := 2 * (1 - 2 * b)
    denominator ≠ 0 ∧ x = (a + c - 2 * b) / denominator := by
  dsimp only
  have oneMinusTwiceMiddleNonzero : 1 - 2 * b ≠ 0 := by
    intro differenceZero
    apply middleNotHalf
    have twiceMiddle : 2 * b = 1 := by
      calc
        2 * b = 1 - (1 - 2 * b) := by ring1
        _ = 1 := by rw [differenceZero]; ring1
    have twoCancel : (2 : K) * 2⁻¹ = 1 :=
      ExplicitField.mul_inv_cancel 2 twoNonzero
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      b = b * 1 := by rw [mul_one]
      _ = b * (2 * 2⁻¹) := by rw [twoCancel]
      _ = (2 * b) * 2⁻¹ := by ring1
      _ = 1 * 2⁻¹ := by rw [twiceMiddle]
  have denominatorNonzero : 2 * (1 - 2 * b) ≠ 0 :=
    ExplicitField.mul_ne_zero twoNonzero oneMinusTwiceMiddleNonzero
  have productZero :
      (a - c) *
        (2 * (1 - 2 * b) * x - (a + c - 2 * b)) = 0 := by
    calc
      (a - c) *
          (2 * (1 - 2 * b) * x - (a + c - 2 * b)) =
        TripleSpread.tripleSpreadFunction a b x - TripleSpread.tripleSpreadFunction b c x := by
          unfold TripleSpread.tripleSpreadFunction
          ring1
      _ = 0 := by
        unfold TripleSpread.SpreadTriple at firstTriple secondTriple
        rw [firstTriple, secondTriple]
        ring1
  have outerDifferenceNonzero : a - c ≠ 0 := ExplicitField.sub_ne_zero_of_ne outerDistinct
  have remainingZero :
      2 * (1 - 2 * b) * x - (a + c - 2 * b) = 0 := by
    by_cases zero : 2 * (1 - 2 * b) * x - (a + c - 2 * b) = 0
    · exact zero
    · exact False.elim
        ((ExplicitField.mul_ne_zero outerDifferenceNonzero zero)
          productZero)
  have clearedEquation : 2 * (1 - 2 * b) * x = a + c - 2 * b := by
    calc
      2 * (1 - 2 * b) * x =
          (2 * (1 - 2 * b) * x - (a + c - 2 * b)) +
            (a + c - 2 * b) := by ring1
      _ = a + c - 2 * b := by rw [remainingZero]; ring1
  have denominatorCancel :
      (2 * (1 - 2 * b)) * (2 * (1 - 2 * b))⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ denominatorNonzero
  refine ⟨denominatorNonzero, ?_⟩
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    x = x * 1 := by rw [mul_one]
    _ = x * ((2 * (1 - 2 * b)) * (2 * (1 - 2 * b))⁻¹) := by
      rw [denominatorCancel]
    _ = (2 * (1 - 2 * b) * x) * (2 * (1 - 2 * b))⁻¹ := by ring1
    _ = (a + c - 2 * b) * (2 * (1 - 2 * b))⁻¹ := by
      rw [clearedEquation]

/-- Complementing all four arguments leaves the quadruple function fixed. -/
theorem quadrupleSpreadFunction_complement (a b c d : K) :
    quadrupleSpreadFunction (1 - a) (1 - b) (1 - c) (1 - d) =
      quadrupleSpreadFunction a b c d := by
  unfold quadrupleSpreadFunction quadrupleSpreadCore
  ring1
end Purelib.Geometry.Trigonometry.Spread.Quadruple

end
