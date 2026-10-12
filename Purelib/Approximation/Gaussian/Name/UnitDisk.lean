module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Basic

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

namespace Purelib.Approximation.Gaussian.Name

/-- Every explicitly possible input at the supplied finite starting state is inside the rational closed unit disk.
Persistence transfers this certificate to every later sampled witness. -/
structure UnitDisk (input : Gaussian.Name.Basic.Named) : Prop where
  /-- Every possible reading at the retained input state has squared norm at most one. -/ possible_unit : ∀ {value :
    Data.Gaussian.Basic.Canonical},
    input.process.Possible input.state value → Data.Gaussian.Norm.Basic.normSq value ≤ 1

namespace UnitDisk

/-- Certify the exact Gaussian rational name using its supplied unit-disk bound. -/
theorem exact (value : Data.Gaussian.Basic.Canonical) (unit
  : Data.Gaussian.Norm.Basic.normSq value ≤ 1) :
    UnitDisk (Named.exact value) where
  possible_unit := by
    intro candidate possible
    change candidate = value at possible
    rw [possible]
    exact unit

end UnitDisk
end Purelib.Approximation.Gaussian.Name

end
