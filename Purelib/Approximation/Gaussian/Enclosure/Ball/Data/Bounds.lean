module
import Purelib.Data.Gaussian.Norm.Comparison
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field

open Purelib.Approximation.Gaussian.Enclosure.Ball

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.Gaussian.Basic.Canonical.Norm

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite numerical controller and adaptive replay

All executable state below is finite chart syntax, rational bounds, natural
source indices and bit lists.  In particular, neither a `Process` nor a
source evaluator occurs in a returned state.  Each productive chunk records
its model reads, including the second read after a residual inverse chart
change.  Buffered bits do not perform a model query.

This is the numerical interpreter.  Its connection to the certified
transducer is established separately; successful replay of an invented log
does not certify global coherence of its replies.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Ball.Data.Bounds

/-- Compute the numerical small-ball upper expression from the stored radius datum and reduced centre quadrance. -/
def smallUpper (ball : Data.BallData) :
  Fraction.Rational := 2 * (ball.radiusSq + Comparison.normSqFromReduced ball.center)

/-- Compute the numerical weighted sector-residual upper expression from the original ball data and sector
representative. -/
def residualUpper (sector :
  Data.ComplexContinuedFraction.Encoding.Sector) (ball
  : Data.BallData) : Fraction.Rational :=
  16 * ball.radiusSq + (16 / 15) * Comparison.normSqFromReduced (ball.center - sector.rep)

/-- Compute the numerical unary lower-bound expression from the stored radius datum and reduced centre quadrance. -/
def unaryLower (ball : Data.BallData) :
  Fraction.Rational :=
  ((Comparison.normSqFromReduced ball.center - 16 * ball.radiusSq) / (16 / 15)) / 2
end Purelib.Approximation.Gaussian.Enclosure.Ball.Data.Bounds

end
