module
import Purelib.Data.Rat.Interval.Bisection
import Purelib.Polynomial.Clearance.Pair.Cover.Leaf
public import Purelib.Polynomial.Clearance.Pair.Cover.Prepare
import Purelib.Polynomial.Clearance.Pair.Sample
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Cover.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Data.Rat

open Purelib.Data.Rat.Interval

open Purelib.Polynomial.Clearance

open Purelib.Polynomial.Clearance.Pair.Cover

open Purelib.Polynomial.Clearance.Pair.Cover.Leaf
open _root_.Purelib.Polynomial.Clearance.Pair.Cover renaming Leaf -> Leaf

section
@[expose] public section

/-! # Kernel regressions of the bound constructor, without integration runs -/

namespace Purelib.Polynomial.Geometry.PolynomialClearanceCoverTests

end Purelib.Polynomial.Geometry.PolynomialClearanceCoverTests

section
namespace Test.Polynomial.ClearanceCover

open _root_.Purelib.Polynomial.Geometry.PolynomialClearanceCoverTests
/-- The closed rational interval from zero to one. -/
private def unit : Bounds := ⟨0,
  1, by decide⟩
/-- The closed rational interval from negative one to one. -/
private def symmetric : Bounds :=
  ⟨-1, 1, by decide⟩
/-- The prepared real quadratic sixteen t squared minus sixteen t plus five, with zero imaginary component. -/
private def quadratic := Source.prepare ⟨[16, -16,
  5]⟩ ⟨[]⟩
/-- The prepared real quartic t to the fourth minus t squared plus one, with zero imaginary component. -/
private def quartic := Source.prepare ⟨[1, 0, -1,
  0, 1]⟩ ⟨[]⟩
/-- The prepared Gaussian line t plus imaginary one minus t. -/
private def switching := Source.prepare ⟨[1, 0]⟩
  ⟨[-1, 1]⟩
end Test.Polynomial.ClearanceCover
end

namespace Test.Polynomial.ClearanceCover

/-- The quadratic completing-square certificate separates the whole unit interval with one retained leaf and unit
floors. -/
theorem quadratic_is_certified_without_subdivision :
    let unit : Bounds := ⟨0, 1, by decide⟩
    let quadratic := Source.prepare ⟨[16, -16, 5]⟩ ⟨[]⟩
    (Prepare.prepare quadratic unit).normFloor = 1 ∧
      (Prepare.prepare quadratic unit).coordinateFloor = 1 ∧
      (Prepare.prepare quadratic unit).cover.regions.length = 1 := by
  decide +kernel

/-- The global quadratic proposal is inapplicable here, and whole-interval Horner has zero separation; the actual cover
must contain several leaves. -/
theorem higher_degree_requires_subdivision :
    let symmetric : Bounds := ⟨-1, 1, by decide⟩
    let quartic := Source.prepare ⟨[1, 0, -1, 0, 1]⟩ ⟨[]⟩
    (Leaf.prepare quartic symmetric).normFloor = 0 ∧
      0 < (Prepare.prepare quartic symmetric).normFloor ∧
      1 < (Prepare.prepare quartic symmetric).cover.regions.length := by
  decide +kernel

/-- `t + i(1-t)` stays separated although neither component does globally. The two half-intervals use different
components and yield a uniform floor. -/
theorem different_local_components_combine :
    let unit : Bounds := ⟨0, 1, by decide⟩
    let switching := Source.prepare ⟨[1, 0]⟩ ⟨[-1, 1]⟩
    (Leaf.prepare switching unit).normFloor = 0 ∧
      (Leaf.prepare switching (Bisection.leftHalf unit)).realFloor = 0 ∧
      (Leaf.prepare switching (Bisection.leftHalf unit)).imagFloor = 1/2 ∧
      (Leaf.prepare switching (Bisection.rightHalf unit)).realFloor = 1/2 ∧
      (Leaf.prepare switching (Bisection.rightHalf unit)).imagFloor = 0 ∧
      (Prepare.prepare switching unit).normFloor = 1/4 ∧
      (Prepare.prepare switching unit).coordinateFloor = 1/2 ∧
      (Prepare.prepare switching unit).cover.regions.length = 2 := by
  decide +kernel

/-- Exhausting the zero subdivision budget leaves a zero proposal while further finite refinement certifies positive
quartic clearance. -/
theorem zero_budget_is_not_a_negative_certificate :
    let symmetric : Bounds := ⟨-1, 1, by decide⟩
    let quartic := Source.prepare ⟨[1, 0, -1, 0, 1]⟩ ⟨[]⟩
    (Prepare.refine (Leaf.prepare quartic symmetric) 0).normFloor = 0 ∧
      0 < (Prepare.refine (Leaf.prepare quartic symmetric) Prepare.defaultDepth).normFloor := by
  decide +kernel

/-- Constant Gaussian inputs and stationary intervals retain their exact positive squared-norm floors with one leaf. -/
theorem constants_and_stationary_intervals :
    let symmetric : Bounds := ⟨-1, 1, by decide⟩
    let quartic := Source.prepare ⟨[1, 0, -1, 0, 1]⟩ ⟨[]⟩
    (Prepare.prepare (Source.prepare ⟨[2]⟩ ⟨[-3]⟩) symmetric).normFloor = 13 ∧
      (Prepare.prepare quartic ⟨0, 0, le_rfl⟩).normFloor = 1 ∧
      (Prepare.prepare quartic ⟨0, 0, le_rfl⟩).cover.regions.length = 1 := by
  decide +kernel

/-- Both the root and an unresolved child retain the local sample attempt; their different radii give different exact
proposals. Neither failed proposal is confused with a proof that the quartic has a zero. -/
theorem local_sample_attempts_are_cached :
    let unit : Bounds := ⟨0, 1, by decide⟩
    let symmetric : Bounds := ⟨-1, 1, by decide⟩
    let quartic := Source.prepare ⟨[1, 0, -1, 0, 1]⟩ ⟨[]⟩
    let switching := Source.prepare ⟨[1, 0]⟩ ⟨[-1, 1]⟩
    ((Leaf.prepare quartic symmetric).sample.map (·.normFloor)) = some (-1151/2) ∧
      ((Leaf.prepare quartic (Bisection.leftHalf symmetric)).sample.map (·.normFloor)) = some (-287/2) ∧
      ((Leaf.prepare switching unit).sample.map (·.normFloor)) = some (-15/2) := by
  decide +kernel

/-- The sample bound itself can be positive, but a leaf already separated by its component bounds does not run this
additional calculation. -/
theorem sample_sound_proposal_and_positive_fast_path :
    let unit : Bounds := ⟨0, 1, by decide⟩
    let symmetric : Bounds := ⟨-1, 1, by decide⟩
    let quadratic := Source.prepare ⟨[16, -16, 5]⟩ ⟨[]⟩
    let switching := Source.prepare ⟨[1, 0]⟩ ⟨[-1, 1]⟩
    (Pair.Sample.prepare ⟨[2]⟩ ⟨[-3]⟩ symmetric).normFloor = 13/2 ∧
      (Leaf.prepare quadratic unit).sample.isNone = true ∧
      (Leaf.prepare switching (Bisection.leftHalf unit)).sample.isNone = true ∧
      (Leaf.prepare switching (Bisection.rightHalf unit)).sample.isNone = true := by
  decide +kernel
end Test.Polynomial.ClearanceCover

end
