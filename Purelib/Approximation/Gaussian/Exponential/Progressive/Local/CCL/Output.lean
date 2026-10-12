module
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Name
import Purelib.Approximation.Gaussian.Sequence.CCL.Output
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.CCL.Transducer.Machine

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

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.CCL.Output

/-- The progressive exponential of the retained unit-disk input emits exactly the requested finite bit count and
preserves its initial prefix. -/
theorem productive (input :
  Gaussian.Name.Basic.Named) (domain : Approximation.Gaussian.Name.UnitDisk input) (count : Nat) :
    (Exponential.Progressive.Local.Name.named input domain).machine.emitted.IsPrefix
        (Advance.advance
          (Exponential.Progressive.Local.Name.named input domain).machine count).emitted ∧
      (Advance.advance
          (Exponential.Progressive.Local.Name.named input domain).machine count).emitted.length = count :=
  (Exponential.Progressive.Local.Name.approximation input domain).output_productive count

end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.CCL.Output

end
