module
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Sequence.CCL.Output
public import Purelib.Approximation.Gaussian.Name.CCL.Output
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local

open Purelib.Data.CCL.Transducer.Machine

section
@[expose] public section

/-!
# Local complex logarithm as a CCL computation

The input to this module is a progressive name for the reduced argument
`z = (u - 1) / (u + 1)`, together with the finite chart certificate that every
currently possible Gaussian-rational candidate has quadrance at most `1/9`.
Finite input refinement and finite Horner depth advance together.  No
completed complex value, infinite series, or global branch is introduced.
The resulting approximation is used as the accuracy sidechannel of a
productive CCL output name; a separate explicit chart supplies the global
branch correction.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.CCL.Output

attribute [local irreducible] Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample.sample

/-- The progressive local complex-logarithm name emits exactly the requested finite bit count and preserves its initial
prefix. -/
theorem productive (input :
  Gaussian.Name.Basic.Named) (disk : Domain.Disk input) (count : Nat) :
    (Name.named input disk).machine.emitted.IsPrefix
        (Advance.advance
          (Name.named input disk).machine count).emitted ∧
      (Advance.advance
          (Name.named input disk).machine count).emitted.length = count :=
  (Name.approximation input disk).output_productive count

end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.CCL.Output

end
