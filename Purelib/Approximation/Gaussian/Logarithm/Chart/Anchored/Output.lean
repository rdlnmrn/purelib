module
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Coherent
import Purelib.Approximation.Gaussian.Logarithm.Chart.Name
import Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

section
@[expose] public section

/-!
# Finite branch calculus for certified complex logarithms

A branch is represented by a finite chart, its operational anchoring
certificate, and coherence of its progressive correction.  Transitions are
ordinary CCL subtraction trees.  Their laws compare finite observations; no
completed logarithm, global cut, integer branch index, or completed `2πi` is
introduced.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
namespace AnchoredChart

/-- The actual charted-logarithm CCL process with its finite coherence sidecar. -/
def output {input :
  CoherentNamed} (branch : Anchored.AnchoredChart input) :
    Coherent.CoherentNamed :=
  { name := Name.named input.name branch.chart
    coherent :=
      Coherent.complexLogNamedCoherent
        input.name branch.chart branch.correctionCoherent }
end AnchoredChart
end Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored

end
