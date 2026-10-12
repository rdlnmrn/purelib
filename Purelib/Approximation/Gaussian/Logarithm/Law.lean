module
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Inverse
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Logarithm.Chart.Inverse
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Difference
public import Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Exponential

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Law.Basic

section
@[expose] public section

/-!
# Operational laws at the persistent CCL-prefix layer

Operational equivalence compares two finite approximation programs by a
computed pair of later natural indices for every positive rational target.
This file carries that comparison all the way to persistent raw CCL cursors.
The two cursors may follow different displayed finite request schedules and
may emit different redundant words.  Each word nevertheless extends its own
earlier prefix, retains exact parser semantics for its certified origin, and
ends in a cylinder of the requested squared-chordal diameter.

The `BitLaw` wrapper then exposes the established arithmetic and exp/log laws
at precisely this bit-producing interface.  It does not identify completed
values or quantify over an infinite bitstream.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Law

/-- Every explicitly anchored logarithm branch satisfies `exp(log(y)) = y` at the persistent-prefix layer. -/
def exponential_logarithm {input :
  CoherentNamed}
    (branch : Anchored.AnchoredChart input) :
    Law.Basic.BitLaw (Exponential.Progressive.Range.Coherent.exp (AnchoredChart.output branch).name)
      input :=
  BitLaw.ofEquivalent (AnchoredChart.exponential_inverse branch)

/-- The reverse direction is necessarily local: the finite zero-alignment certificate selects the intended preimage
branch. -/
def logarithm_exponential (input :
  CoherentNamed)
    (branch : Anchored.AnchoredChart
      (Exponential.Progressive.Range.Coherent.exp input.name))
    (alignment : Difference.LocalAlignment
      input (AnchoredChart.output branch)) :
    Law.Basic.BitLaw (AnchoredChart.output branch) input :=
  BitLaw.ofEquivalent
    (Inverse.logarithm_exponential_inverse
      input branch alignment)

end Purelib.Approximation.Gaussian.Logarithm.Law

end
