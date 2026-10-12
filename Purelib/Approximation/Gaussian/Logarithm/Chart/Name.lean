module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
import Purelib.Approximation.Gaussian.Logarithm.Chart.Reduction
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Logarithm (Chart)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

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

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Name

/-- Compute the finite local-logarithm name of the chart's exact apartness-prepared reduced argument. -/
def localOutput (input : Gaussian.Name.Basic.Named) (chart :
  Chart input) : Gaussian.Name.Basic.Named :=
  Local.Name.named
    (Reduction.reduced input chart.factor chart.denominatorApart) chart.reducedDisk

/-- The selected complex-log branch: local Horner output plus the explicitly supplied additive branch correction. -/
def named (input : Gaussian.Name.Basic.Named) (chart :
  Chart input) : Gaussian.Name.Basic.Named :=
  Named.add
    (localOutput input chart) chart.correction
end Purelib.Approximation.Gaussian.Logarithm.Chart.Name

end

section
@[expose] public section

/-!
# Computing exponential and logarithm as CCL names

The purpose of this module is not merely to expose Horner approximants.  It
proves that exponential and certified logarithm are computable operations on
the repository's arithmetic CCL representation: a productive raw CCL cursor
together with its finite rational accuracy sidechannel.

Each request first refines the constructed output process to one displayed
rational ball whose squared radius is below the requested positive rational
target.  The ordinary productive CCL cursor is then started at that same
finite state and returns exactly the requested number of bits.  Its
exact-cursor certificate ties every admitted parser tail back to an explicitly
possible rational value at that same refined state.  Thus the enclosure and
the CCL word are two synchronized observations of one output name.  The bare
raw word alone is intentionally not claimed to carry enough accuracy data.
The construction returns only finite rational data; it does not name a
completed transcendental value.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Name

/-! ## Explicitly charted complex logarithm -/

/-- The selected productive complex-logarithm name, retaining the original chart and additive correction. -/
def complexLogOutput (input : Gaussian.Name.Basic.Named)
    (chart : Chart input) : Gaussian.Name.Basic.Named :=
  named input chart

/-- Refine the selected complex-logarithm output at the displayed positive rational target. -/
def complexLogRequest (input : Gaussian.Name.Basic.Named)
    (chart : Chart input)
    (target : Fraction.Rational) (positive : 0 < target) : Gaussian.Name.Basic.Named :=
  Refinement.refined (complexLogOutput input chart) target positive
end Purelib.Approximation.Gaussian.Logarithm.Chart.Name

end
