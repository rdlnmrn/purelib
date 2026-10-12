module
import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Domain
public import Purelib.Approximation.Gaussian.Name.CCL.Output
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.Name
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic

open Purelib.Data.CCL.Transducer.Machine

section
@[expose] public section

/-!
# Finite dyadic range reduction for the progressive logarithm

A logarithm needs branch information.  This module records that information
as one finite dyadic chart: a natural exponent, a scaling direction, and a
proof that every candidate at the displayed input state is carried into the
overlapping real interval `[1/2,2]`.

The output is the local finite logarithm of the scaled input plus or minus an
explicit natural multiple of the independently generated finite `log 2`
samples.  No completed logarithm, limiting value, or infinite functional
equation appears in the construction.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.CCL.Output

/-- The logarithm name for the retained dyadic chart emits exactly the requested finite bit count and preserves its
initial prefix. -/
theorem productive (input :
  Gaussian.Name.Basic.Named) (chart : Domain.DyadicChart input)
    (count : Nat) :
    (Name.named input chart).machine.emitted.IsPrefix
        (Advance.advance
          (Name.named input chart).machine count).emitted ∧
      (Advance.advance
          (Name.named input chart).machine count).emitted.length = count :=
  (Name.named input chart).productive count

end Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Dyadic.CCL.Output

end
