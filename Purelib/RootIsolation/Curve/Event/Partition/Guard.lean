module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Product.List
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Box.Guard
public import Purelib.RootIsolation.Sturm.Event.Guard
import Mathlib.Data.List.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation

/-!
# Common finite event partitions for curve roots and box edges

The root-event polynomial of a boundary chart and the four cleared box-edge
polynomials must be classified on the same parameter cells.  This module
forms one product of their complete reduced-chain guards, uses it for every
central-third cut, and chooses a coefficient-computed depth below all of the
individual event-resolution widths.

Consequently every emitted leaf has, simultaneously:

* a finite Cauchy--Sturm event record for the chart root polynomial; and
* a finite event record for every nontrivial box-edge condition.

Identically-zero box conditions are retained separately by
`CurveBoxConditions.condition_zero_or_active`; they never make
the common cut guard vanish.
-/

namespace Purelib.RootIsolation.Curve.Event.Partition

open Purelib
open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

public section

/-- List the main chart-root guard followed by the active box-condition guards.

The event polynomial supplies the first guard. The original condition filter
retains only represented nonzero box conditions, and mapping their event
guards preserves the order and occurrences of that retained list. -/
@[expose] def eventGuards
    (event : Dense.Basic.RationalPolynomial) (curve : Curve.RationalCurve) (box : Box) :
    List (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Sturm.Event.polynomialEventGuard event ::
    (Curve.Box.activeConditionPolynomials curve box).map
      Sturm.Event.polynomialEventGuard

/-- Every retained guard is nonzero when the main event polynomial is nonzero.

The head guard retains the original nonzero event polynomial. Every mapped
box-condition guard retains its source condition and its false zero test. -/
theorem eventGuards_all_nonzero
    {event : Dense.Basic.RationalPolynomial} (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) :
    ∀ guard ∈ Curve.Event.Partition.eventGuards event curve box, guard.isZero = false := by
  intro guard member
  change guard ∈ Sturm.Event.polynomialEventGuard event ::
      (Curve.Box.activeConditionPolynomials curve box).map Sturm.Event.polynomialEventGuard at member
  cases member with
  | head => exact Sturm.Event.polynomialEventGuard_isZero_false eventNonzero
  | tail _ tailMember =>
      rcases Data.List.Map.mem_map.mp tailMember with ⟨condition, conditionMember, equal⟩
      subst guard
      exact Sturm.Event.polynomialEventGuard_isZero_false
        (Curve.Box.activeConditionPolynomials_all_nonzero curve box condition conditionMember)

/-- Multiply the event and active box-condition guards into one polynomial.

The finite guard list retains its original order and polynomial factors. A
false zero test for the event polynomial ensures that every factor and their
product are represented nonzero; identically zero box conditions are omitted. -/
@[expose] def commonGuard
    (event : Dense.Basic.RationalPolynomial) (curve : Curve.RationalCurve) (box : Box) :
      (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Rational.Product.List.polynomialProduct (Curve.Event.Partition.eventGuards event curve box)

/-- The common product of the nonzero event guards is nonzero. -/
theorem commonGuard_isZero_false
    {event : Dense.Basic.RationalPolynomial} (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) :
    (Curve.Event.Partition.commonGuard event curve box).isZero = false :=
  Dense.Rational.Product.List.polynomialProduct_isZero_false
    (Curve.Event.Partition.eventGuards_all_nonzero eventNonzero curve box)

/-- A nonzero common-guard evaluation makes every retained member guard nonzero at that parameter. -/
theorem eval_ne_zero_of_eventGuard
    {event : Dense.Basic.RationalPolynomial} {curve : Curve.RationalCurve} {box : Box}
    {guard : Dense.Basic.RationalPolynomial} {parameter : Fraction.Rational}
    (member : guard ∈ Curve.Event.Partition.eventGuards event curve box)
    (commonNonzero : (Curve.Event.Partition.commonGuard event curve box).eval parameter ≠ 0) :
    guard.eval parameter ≠ 0 :=
  Dense.Rational.Product.List.eval_ne_zero_of_mem_of_polynomialProduct member commonNonzero
end

end Purelib.RootIsolation.Curve.Event.Partition
