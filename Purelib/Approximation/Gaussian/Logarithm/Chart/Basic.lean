module

import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Data.Rat

section
@[expose] public section

/-!
# One certified complex logarithm branch chart

A chart scales the input by one displayed Gaussian rational `factor`, forms
the exact progressive quotient

`(factor * input - 1) / (factor * input + 1)`,

and requires finite certificates that every possible denominator has a fixed
positive lower quadrance and that every possible quotient lies in the local
disk of the finite complex-log recurrence.  One finite preparation step turns
the first certificate into whole-ball apartness before division.  A separate
progressive correction name selects the desired additive branch normalization.

This is deliberately a one-chart interface.  It is not a total complex
logarithm and it does not hide a branch choice or a completed complex value.
-/

namespace Purelib.Approximation.Gaussian.Logarithm

set_option genInjectivity false in
/-- Finite data selecting one branch-safe local chart. The correction is a name rather than a completed value, so
non-rational branch normalizations can still be refined on demand. -/
structure Chart (input : Gaussian.Name.Basic.Named) where
  /-- The displayed Gaussian rational scale factor for this logarithm chart. -/ factor : Canonical
  /-- Uniform candidate apartness of the exact scaled-plus-one denominator process. -/ denominatorApart :
    Possible.PossibleApart (Reduction.denominator input factor).process
  /-- The finite local-logarithm disk certificate for the quotient formed using that same denominator preparation. -/
    reducedDisk : Domain.Disk (Reduction.reduced input factor denominatorApart)
  /-- The retained progressive additive branch-correction name. -/ correction : Gaussian.Name.Basic.Named

constructive_injectivity Chart

namespace Chart.mk

end Chart.mk

namespace Chart

/-- Package the operational chart from two checkable rational inequalities: a positive denominator lower bound at every
finite input state, and the local disk bound for every pair of candidates admitted by the starting state. -/
def ofBounds (input : Gaussian.Name.Basic.Named)
  (factor : Canonical)
    (lowerSq : Fraction.Rational) (positive : 0 < lowerSq)
    (denominatorLower :
      ∀ (state : input.process.State) {source : Canonical},
        input.process.Possible state source →
          lowerSq ≤
            Data.Gaussian.Norm.Basic.normSq (factor * source + 1))
    (localBound : ∀ {numeratorSource denominatorSource : Canonical},
      input.process.Possible input.state numeratorSource →
      input.process.Possible input.state denominatorSource →
      Data.Gaussian.Norm.Basic.normSq
          ((factor * numeratorSource - 1) /
            (factor * denominatorSource + 1)) ≤ 1 / 9)
    (correction : Gaussian.Name.Basic.Named) : Chart input := by
  let apart := Reduction.denominatorPossibleApart input factor lowerSq positive
    denominatorLower
  exact
    { factor := factor
      denominatorApart := apart
      reducedDisk := Reduction.reducedDiskOfBounds input factor apart localBound
      correction := correction }

end Chart

namespace Chart.Basic

/-- A concrete inhabited chart: the exact rational input `1` uses factor `1`, reduced argument `0`, and zero correction.
-/
def unitChart :
  Chart
    (Named.exact 1) :=
  ofBounds
    (Named.exact 1)
    1 1 (by decide)
    (by
      intro state source possible
      change source = (1 : Canonical) at possible
      subst source
      decide)
    (by
      intro numeratorSource denominatorSource numeratorPossible
        denominatorPossible
      change numeratorSource = (1 : Canonical) at numeratorPossible
      change denominatorSource = (1 : Canonical) at denominatorPossible
      subst numeratorSource
      subst denominatorSource
      decide)
    (Named.exact 0)

end Chart.Basic

end Purelib.Approximation.Gaussian.Logarithm

end
