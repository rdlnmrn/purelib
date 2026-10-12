module
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State

section
@[expose] public section

/-!
# Finite certificate acquisition: public theorem interface

Three distinct contracts are exposed here, without a universal partiality
framework:

* `boundedDivision` makes one prescribed request and returns an ordinary
  cached quotient or whole-ball smallness with persistent candidate bounds.
* `gapDivision` turns smallness into exact branch exclusion under a proved
  zero-or-gap law. `signedGap` computes a sufficient canonical inspection
  budget from an unsigned imaginary gap.
* `exact` decides between an equivalent prepared presentation and operational
  zero for the two supported finite provenance classes. Its semantic iff
  and presentation-invariance laws do not apply to opaque inputs lacking
  this provenance, nor to the overlapping numerical small/apart verdicts.

`separatedWord` prepares an entire word in either half-plane and exposes
single/fold agreement, braid invariance, reversal, and the dual period law
through its retained report. Negative imaginary evidence is not global
non-certifiability. Precision and inspection counts below are not CPU-time,
allocation, certificate-size, or general-polynomial separation bounds.
-/

namespace Purelib.Approximation.Gaussian.Division.Search.State

/-- Construct the initial denominator search state with the original named source, refinement index zero and reflexive
candidate provenance. -/
def initial (denominator : Coherent.CoherentNamed) :
  Name.Coherent.Refinement.State denominator :=
  Name.Coherent.Refinement.State.initial denominator
end Purelib.Approximation.Gaussian.Division.Search.State

end
