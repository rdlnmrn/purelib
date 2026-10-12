module
public import Purelib.Polynomial.Ascending.Rational.Jet.Basic
import Purelib.Data.Rat.Fraction

open Purelib.Polynomial.Ascending.Rational.Jet.Basic (TaylorJet)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite higher, Taylor, directional, and multivariable jets

The one-variable Taylor object below is a wrapper around the repository's
low-to-high finite rational polynomial program.  Repeated differentiation is
structural recursion on a requested natural order.  Multivariable first jets
store a displayed finite list of Gaussian-rational partial coefficients; a
directional coefficient is a finite dot-product recursion.

These are finite tables, not function spaces or infinite formal series.
-/

namespace Purelib.Polynomial.Ascending.Rational.Jet.Basic.TaylorJet
section

/-- The requested finite higher derivative table. -/
def derivativeOrder :
  TaylorJet → Nat → TaylorJet
  | jet, 0 => jet
  | jet, order + 1 => TaylorJet.derivative
    (derivativeOrder jet order)

/-- The displayed higher coefficient at the expansion origin. -/
def higherCoefficient (jet :
  TaylorJet) (order : Nat) : Fraction.Rational :=
  (jet.derivativeOrder order).coefficient 0

/-- Taking zero derivatives preserves the Taylor jet. -/
@[simp] theorem derivativeOrder_zero (jet :
  TaylorJet) :
    jet.derivativeOrder 0 = jet := rfl

/-- The next derivative order differentiates the preceding finite derivative table. -/
@[simp] theorem derivativeOrder_succ (jet :
  TaylorJet) (order : Nat) :
    jet.derivativeOrder (order + 1) =
      (jet.derivativeOrder order).derivative := rfl
end

end Purelib.Polynomial.Ascending.Rational.Jet.Basic.TaylorJet

end
