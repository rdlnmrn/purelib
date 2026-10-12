module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Logarithm.Chart.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Branch
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Name.Basic

section

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm

open Purelib.Approximation.Gaussian.Logarithm.Chart.Branch

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

set_option genInjectivity false in
/-- One certified logarithm branch over a coherent CCL input. -/
structure AnchoredChart (input : CoherentNamed) where
  /-- The finite complex-logarithm chart indexed by the original coherent input name. -/ chart : Chart
    input.name
  /-- The operational branch-anchoring certificate indexed by that same input and chart. -/ certificate :
    BranchCertificate input.name chart
  /-- Finite coherence of the exact correction process retained by the chart. -/ correctionCoherent :
    Gaussian.Process.Coherence.Basic.Coherent chart.correction.process

constructive_injectivity AnchoredChart

end Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored

end

end
