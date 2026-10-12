module
public import Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Positive.Name
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.PositiveReal.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Positive

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.CCL.Transducer.Machine

section
@[expose] public section

/-!
# Automatic positive-real charting for a CCL logarithm

The input certificate supplies a displayed positive rational lower bound for
the real coordinate of every candidate at the current finite state.  One
explicit refinement makes the current ball small relative to that bound.
The rational real coordinate of the refined ball centre is then normalized
by a bounded dyadic scan, and every explicitly possible candidate at the
refined state is proved to land in the overlapping local logarithm chart.
The geometric ball may of course contain irrelevant non-real points; the
separate positive-real certificate excludes those from the process semantics.

This is branch data and finite error accounting only.  It neither selects a
point common to all refinements nor asserts a completed logarithm.  Its
purpose is to make positive-real logarithm an automatic CCL-to-CCL operator
on this certified domain: chart preparation, local logarithm, the finite
`log 2` correction, and every correction addition remain arithmetic CCL
names.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Positive.CCL.Output

/-- The automatically charted positive-real logarithm name emits exactly the requested finite bit count and preserves
its initial prefix. -/
theorem productive (input :
  Gaussian.Name.Basic.Named) (positive : Approximation.Gaussian.Name.PositiveReal input)
    (count : Nat) :
    (Name.named input positive).machine.emitted.IsPrefix
        (Advance.advance
          (Name.named input positive).machine count).emitted ∧
      (Advance.advance
          (Name.named input positive).machine count).emitted.length = count :=
  (Name.named input positive).productive count

end Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Positive.CCL.Output

end
