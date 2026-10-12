module
public import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Name.Basic
import Init.Prelude

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Approximation.Gaussian.Name.Sampling

section
@[expose] public section

/-!
# Progressive finite exponential

This is the local core of exponential as a CCL-to-CCL computation.  The input
is an existing arithmetic CCL name together with a finite domain certificate
for its candidates.  At natural index `n`, the output evaluates the depth-`n`
Horner program at the input's depth-`n` displayed rational witness, packages
those samples as a progressive enclosure process, and starts the unchanged
productive raw CCL controller on that process.  Thus neither side names a
completed point, while every requested finite output prefix is genuinely a
CCL prefix for the calculated exponential enclosure.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Sample

/-- The depth and the displayed input witness advance together. -/
def sample (input :
  Gaussian.Name.Basic.Named) (index : Nat) : Canonical :=
  Horner.Sample.sample (Exp.inputSample input index) index

/-- Evaluate the finite exponential Horner program at the input sample with the same displayed depth. -/
def sampleFrom (samples : Nat →
  Canonical) (index : Nat) : Canonical :=
  Horner.Sample.sample (samples index) index
end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Sample

end
