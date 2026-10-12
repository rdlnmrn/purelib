module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored.Output
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Name
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Inverse
import Purelib.Approximation.Gaussian.Name.Coherent

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Logarithm.Chart
open Purelib.Approximation.Gaussian.Name.Coherent

public section

/-!
# Finite branch calculus for certified complex logarithms

A branch is represented by a finite chart, its operational anchoring
certificate, and coherence of its progressive correction.  Transitions are
ordinary CCL subtraction trees.  Their laws compare finite observations; no
completed logarithm, global cut, integer branch index, or completed `2πi` is
introduced.
-/

open Purelib.Approximation
namespace AnchoredChart

/-- Exponentiating the actual chart output reconstructs the original input through finite operational equality. -/
@[expose] def exponential_inverse {input :
  CoherentNamed}
    (branch : Anchored.AnchoredChart input) :
    Gaussian.Equivalence.NamedEquivalent
      (Exponential.Progressive.Range.Name.named branch.output.name)
      input.name :=
  Inverse.actualExp_chartedLog_named_equivalent
    input.name branch.chart branch.certificate input.coherent
      branch.correctionCoherent

end AnchoredChart

end

end Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
