module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Data.Gaussian.RationalEmbedding
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Data.Gaussian.RationalEmbedding

open Purelib.Data.Rat

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

namespace Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Domain

/-- One redundant local chart for the real logarithm. -/
structure Chart (input :
  Gaussian.Name.Basic.Named) : Prop where
  /-- Every possible reading at the retained input state lies on the real axis between one half and two. -/
    possible_real_chart : ∀ {value : Data.Gaussian.Basic.Canonical},
    input.process.Possible input.state value →
      value.im = 0 ∧ 1 / 2 ≤ value.re ∧ value.re ≤ 2

namespace Chart

/-- Certify the local real-logarithm chart for an exact rational input between one half and two. -/
theorem exact (value :
  Fraction.Rational) (halfLe : 1 / 2 ≤ value)
    (leTwo : value ≤ 2) :
    Approximation.Gaussian.Logarithm.Real.Progressive.Local.Domain.Chart (Named.exact
      (Log.real value)) where
  possible_real_chart := by
    intro candidate possible
    change candidate = Log.real value at possible
    rw [possible]
    exact ⟨rfl, halfLe, leTwo⟩

end Chart
end Purelib.Approximation.Gaussian.Logarithm.Real.Progressive.Local.Domain

end
