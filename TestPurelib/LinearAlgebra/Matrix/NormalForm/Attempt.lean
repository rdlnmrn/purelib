module

import Purelib.LinearAlgebra.Matrix.NormalForm.Attempt
import Purelib.LinearAlgebra.Matrix.NormalForm.Coordinates
import Purelib.Data.Rat.Fraction.Field

/-!
# Complete and unresolved finite unit-pivot attempts

The same original two-by-two rectangle is tried with two literal finite
candidate pools. One stops after an actual successful pivot, retaining the
unresolved residual; the other supplies its missing inverse and completes.
-/

namespace TestPurelib.LinearAlgebra.Matrix.NormalForm.Attempt

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.LinearAlgebra.Matrix
open Purelib.Algebra.Ring

/-- The original rectangular table has independent diagonal entries one and two. -/
private def table : Rectangular Rational 2 2 :=
  .cons (.cons 1 (.cons 0 .nil)) (.cons (.cons 0 (.cons 2 .nil)) .nil)

/-- The literal pool omits the second diagonal coefficient's actual inverse. -/
private def limited := NormalForm.attempt table [0, 1]

/-- Read the accepted first receipt and actual terminal residual from the retained original history. -/
private def limitedReading : List Rational × Rational × Rational × List Rational :=
  match limited with
  | .incomplete (.pivot _ _ accepted step _ (.exhausted _ _ rejected)) _ =>
      (accepted.tested.map Unit.Rejected.product, accepted.inverse,
        step.residual 0 0, rejected.tested.map Unit.Rejected.product)
  | _ => ([], 0, 0, [])

/-- One rejected product precedes inverse one, then actual residual two exhausts products zero and two. -/
private theorem limited_ordered_products : limitedReading = ([0], 1, 2, [0, 2]) := by decide +kernel

/-- The incomplete attempt retains exactly one successful pivot. -/
private theorem limited_pivots : limited.history.pivotCount = 1 := by decide +kernel

/-- Both original candidate products were tested at each of the two actual stages. -/
private theorem limited_tests : limited.history.testCount = 4 := by decide +kernel

/-- The unresolved finite attempt does not expose a fabricated completed normal form. -/
private theorem limited_unresolved : limited.normal? = none := by decide +kernel

/-- The unresolved coefficient nevertheless has an inverse outside the original finite candidate list. -/
private theorem omitted_inverse_exists : (2 : Rational) * (1 / 2) = 1 := by decide +kernel

/-- Adding the actual missing inverse completes the same original rectangle. -/
private def sufficient := NormalForm.attempt table [0, 1, 1 / 2]

/-- Read the cached complete rank and its original rejected and untried candidate lists. -/
private def sufficientReading : Nat × List Rational × List Rational × List Rational :=
  match sufficient with
  | .complete normal (.pivot _ _ first _ _ (.pivot _ _ second _ _ _)) _ =>
      (normal.rank, first.remaining, second.tested.map Unit.Rejected.product, second.remaining)
  | _ => (0, [], [], [])

/-- The complete attempt retains rank two, the original skipped suffix and the second rejected prefix. -/
private theorem sufficient_order : sufficientReading = (2, [1 / 2], [0, 2], []) := by decide +kernel

/-- The complete original reduction performs two successful pivots. -/
private theorem sufficient_pivots : sufficient.history.pivotCount = 2 := by decide +kernel

/-- The original early success and three later probes account for exactly five candidate products. -/
private theorem sufficient_tests : sufficient.history.testCount = 5 := by decide +kernel

/-- The complete result uses its actual computed rank in the target-minus-kernel coordinate defect. -/
private def sufficientDefect : Int :=
  match sufficient with
  | .complete normal _ _ => normal.defect
  | .incomplete _ _ => 7

/-- The same square table's complete certified coordinate defect is zero. -/
private theorem sufficient_defect : sufficientDefect = 0 := by decide +kernel

/-- An empty candidate pool leaves the original nonzero table unresolved without scalar products. -/
private theorem empty_pool_tests : (NormalForm.attempt table []).history.testCount = 0 := by decide +kernel

end TestPurelib.LinearAlgebra.Matrix.NormalForm.Attempt
