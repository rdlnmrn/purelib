module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Cross
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Triple
import Purelib.Geometry.Plane.Line.Trigonometry.Conversion
import Purelib.Geometry.Trigonometry.Spread.Triple
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Trigonometry.Spread

open Purelib.Geometry.Trigonometry.Spread.Triple

section
@[expose] public section

/-!
# Divine Proportions, Chapter 7: the triple spread formula

The proof is performed directly on the six finite line coefficients.  A
single explicit common denominator replaces the book's auxiliary triangle,
and every cancellation is witnessed by the three non-null hypotheses.
-/

namespace Purelib.Geometry.Plane.Line.Cross.Triple

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Theorem 49 (Triple cross formula), obtained by the finite substitutions `cᵢ = 1 - sᵢ`. -/
theorem triple_cross_formula
    (first second third : Plane.Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (thirdNonNull : ¬ third.IsNull) :
    let c₁ := Cross.cross second third secondNonNull thirdNonNull
    let c₂ := Cross.cross first third firstNonNull thirdNonNull
    let c₃ := Cross.cross first second firstNonNull secondNonNull
    (c₁ + c₂ + c₃ - 1) ^ 2 = 4 * c₁ * c₂ * c₃ := by
  dsimp only
  let s₁ := Spread.spread second third secondNonNull thirdNonNull
  let s₂ := Spread.spread first third firstNonNull thirdNonNull
  let s₃ := Spread.spread first second firstNonNull secondNonNull
  have spreadTriple : TripleSpread.SpreadTriple s₁ s₂ s₃ :=
    Triple.three_lines_form_spreadTriple first second third firstNonNull secondNonNull
      thirdNonNull
  have complement := Triple.spreadTriple_complement_form spreadTriple
  have firstCross :
      Cross.cross second third secondNonNull thirdNonNull = 1 - s₁ := by
    have sum := Trigonometry.Conversion.spread_add_cross second third secondNonNull thirdNonNull
    unfold s₁
    calc
      Cross.cross second third secondNonNull thirdNonNull =
          (Spread.spread second third secondNonNull thirdNonNull +
            Cross.cross second third secondNonNull thirdNonNull) -
            Spread.spread second third secondNonNull thirdNonNull := by ring1
      _ = 1 - Spread.spread second third secondNonNull thirdNonNull := by rw [sum]
  have secondCross :
      Cross.cross first third firstNonNull thirdNonNull = 1 - s₂ := by
    have sum := Trigonometry.Conversion.spread_add_cross first third firstNonNull thirdNonNull
    unfold s₂
    calc
      Cross.cross first third firstNonNull thirdNonNull =
          (Spread.spread first third firstNonNull thirdNonNull +
            Cross.cross first third firstNonNull thirdNonNull) -
            Spread.spread first third firstNonNull thirdNonNull := by ring1
      _ = 1 - Spread.spread first third firstNonNull thirdNonNull := by rw [sum]
  have thirdCross :
      Cross.cross first second firstNonNull secondNonNull = 1 - s₃ := by
    have sum := Trigonometry.Conversion.spread_add_cross first second firstNonNull secondNonNull
    unfold s₃
    calc
      Cross.cross first second firstNonNull secondNonNull =
          (Spread.spread first second firstNonNull secondNonNull +
            Cross.cross first second firstNonNull secondNonNull) -
            Spread.spread first second firstNonNull secondNonNull := by ring1
      _ = 1 - Spread.spread first second firstNonNull secondNonNull := by rw [sum]
  rw [firstCross, secondCross, thirdCross]
  calc
    ((1 - s₁) + (1 - s₂) + (1 - s₃) - 1) ^ 2 =
        (s₁ + s₂ + s₃ - 2) ^ 2 := by ring1
    _ = 4 * (1 - s₁) * (1 - s₂) * (1 - s₃) := complement
end Purelib.Geometry.Plane.Line.Cross.Triple

end
