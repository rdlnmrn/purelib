module
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step
import Purelib.Polynomial.Dense.Rational.Bounds.Lipschitz
import Purelib.Data.Rat.Interval.Radius
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite constructive Cauchy-chain cells

This module records two kinds of locally resolved signed-remainder-chain
cells.  A stable list has the same signs at both endpoints.  An interior
signed step allows its middle member to change while the adjacent outer
members keep opposite signs, so the two local jumps cancel exactly.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step.Prepare

/-- Executable classifier for one cancelling signed Euclidean triple, using
the displayed left endpoint as its common finite sample. -/
def signedStepCellCertificate?
    (p q : Dense.Rational.Basic.CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) :
    Option (Dense.Rational.SignedRemainder.Signs.Step.SignedStepCellCertificate p q interval) :=
  let sample := interval.lower
  let next := -((Dense.Basic.DensePolynomial.divMod p q).remainder)
  if leftMargin : Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound p interval *
      Data.Rat.Interval.Radius.sampleRadiusSq interval sample < p.eval sample ^ 2 then
    if rightMargin : Dense.Rational.Bounds.Lipschitz.denseEvalSqLipschitzBound next interval *
        Data.Rat.Interval.Radius.sampleRadiusSq interval sample < next.eval sample ^ 2 then
      if outerOpposite : p.eval sample * next.eval sample < 0 then
        some
          { sample := sample
            sampleInside := ⟨le_rfl, interval.valid⟩
            leftMargin := leftMargin
            rightMargin := rightMargin
            outerOpposite := outerOpposite }
      else none
    else none
  else none
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Step.Prepare

end
