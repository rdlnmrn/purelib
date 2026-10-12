module
public import Purelib.Approximation.Gaussian.Name.Sampling
public import Purelib.Approximation.Gaussian.Sequence.UnitDisk
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.UnitDisk
import Purelib.Approximation.Gaussian.Process.Sampling
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Sampling

open Purelib.Approximation.Gaussian.Sequence

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

namespace Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Sampling

/-- Every canonical finite sample of a name certified in the unit disk has squared norm at most one. -/
theorem inputSample_unit {input :
  Gaussian.Name.Basic.Named} (domain : Approximation.Gaussian.Name.UnitDisk input)
    (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Exp.inputSample input index) ≤ 1 :=
  domain.possible_unit (Exp.inputSample_possible_start input index)

/-- Package the canonical witnesses of a unit-disk name with their retained unit bound and scale-four geometric pairwise
allowance. -/
def unitDiskSamples (input :
  Gaussian.Name.Basic.Named) (domain : Approximation.Gaussian.Name.UnitDisk input) : UnitDisk.UnitDiskSamples :=
  { value := Exp.inputSample input
    unit := inputSample_unit domain
    close := fun move =>
      Gaussian.Process.Sampling.witnessAt_later_close
        input.process input.state move }
end Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Sampling

end
