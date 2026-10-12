module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Approximation.Gaussian.Enclosure.Sector.Budget
public import Purelib.Approximation.Rational.Request.Common
import Purelib.Data.Gaussian.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Enclosure.Sector

open Purelib.Approximation.Rational.Request

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

namespace Purelib.Approximation.Gaussian.Process.Normalization.Data

set_option genInjectivity false in
/-- Finite numerical data for the normalization domain.

The record retains the displayed lower quadrance and its rational weight; semantic positivity and safety certificates
are supplied separately. -/
@[ext] structure Domain where
  /-- The retained rational lower quadrance. -/ lowerSq : Fraction.Rational
  /-- The retained rational normalization weight. -/ weight : Fraction.Rational
deriving DecidableEq

constructive_injectivity Domain

/-- Compute domain data with weight two divided by the displayed lower quadrance minus one. -/
def Domain.ofLower (lowerSq : Fraction.Rational) :
  Domain :=
  ⟨lowerSq, 2 / (lowerSq - 1)⟩

/-- Compute a common rational normalization request from the retained domain margin and sector budget. -/
def Domain.target (domain :
  Domain) : Fraction.Rational :=
  Common.commonTarget
    ((domain.lowerSq - (domain.weight + 1) / domain.weight) / (domain.weight + 1))
    Budget.uniformRadiusSq

/-- Compute inverse-domain data from a binary scaling count and displayed upper quadrance. -/
def inverseDomain (count : Nat) (upper :
  Fraction.Rational) : Domain :=
  .ofLower (((2 : Fraction.Rational) ^ (count + 1) * upper)⁻¹)
end Purelib.Approximation.Gaussian.Process.Normalization.Data

end
