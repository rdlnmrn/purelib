module
import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Sequence.CCL.Output
public import Purelib.Approximation.Gaussian.Name.CCL.Output
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local

open Purelib.Data.CCL.Transducer.Machine

section
@[expose] public section

/-!
# Local logarithm as a CCL computation

This is the local core of logarithm as a CCL-to-CCL computation.  The input is
an arithmetic CCL name carrying an explicit overlapping chart certificate.
Every candidate is a displayed real Gaussian rational whose coordinate lies
in `[1/2,2]`.  The output synchronizes later finite input witnesses with later
finite Horner depths, packages the result as an accuracy sidechannel, and
starts the unchanged productive CCL controller on it.  It does not assert a
completed positive real input or a completed logarithm.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.CCL.Output

/-- The progressive real logarithm name for the retained local chart emits exactly the requested finite bit count and
preserves its initial prefix. -/
theorem productive (input :
  Gaussian.Name.Basic.Named) (chart : Domain.Chart input) (count : Nat) :
    (Name.named input chart).machine.emitted.IsPrefix
        (Advance.advance
          (Name.named input chart).machine count).emitted ∧
      (Advance.advance
          (Name.named input chart).machine count).emitted.length = count :=
  (Name.approximation input chart).output_productive count

end Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.CCL.Output

end
