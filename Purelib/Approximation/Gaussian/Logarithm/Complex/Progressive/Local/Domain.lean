module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
public import Purelib.Approximation.Gaussian.Name.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Basic

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

namespace Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain

attribute [local irreducible] Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample.sample

/-- The closed reduced-argument disk used by the finite complex Horner program. -/
structure Disk (input :
  Gaussian.Name.Basic.Named) : Prop where
  /-- Every Gaussian value compatible with the retained input name has squared norm at most one ninth. -/
    possible_normSq : ∀ {value : Data.Gaussian.Basic.Canonical},
    input.process.Possible input.state value → Data.Gaussian.Norm.Basic.normSq value ≤ 1 / 9

namespace Disk

/-- Certify the local logarithm disk for an exact Gaussian name whose value has squared norm at most one ninth. -/
theorem exact (value :
  Data.Gaussian.Basic.Canonical) (bound : Data.Gaussian.Norm.Basic.normSq value ≤ 1 / 9) :
    Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain.Disk (Named.exact value) where
  possible_normSq := by
    intro candidate possible
    change candidate = value at possible
    rw [possible]
    exact bound

end Disk
end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain

end
