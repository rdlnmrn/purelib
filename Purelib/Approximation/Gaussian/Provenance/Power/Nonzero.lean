module

public import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Approximation.Gaussian.Name.Coherent.Power.Composition
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Division.Obstruction.Zero
import Purelib.Approximation.Gaussian.Arithmetic.Mul

/-!
# Nonzero radicands of original apart square roots

An original apart generator with a retained square equation has a nonzero
radicand. The negative assertion follows by finite operational cancellation
at that same generator, without selecting another root or reading.
-/

public section

namespace Purelib.Approximation.Gaussian.Provenance.Power.PowerIdentity

open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)

/-- The square coefficient is nonzero whenever its original generator is apart. -/
theorem square_coefficient_nonzero {generator : CoherentNamed} {radicand : Canonical}
    (identity : PowerIdentity generator 2 radicand)
    (apart : Purelib.Approximation.Gaussian.Name.Basic.Named.Apart generator.name) : radicand ≠ 0 := by
  intro vanishes
  have square := NamedEquivalent.trans (NamedEquivalent.symm (Power.namedPower_two generator)) identity
  rw [vanishes] at square
  let zero := Coherence.exact 0
  have multipliedZero := Purelib.Approximation.Gaussian.Arithmetic.Mul.coherentMul_zero_right generator
  have sourceZero := Purelib.Approximation.Gaussian.Division.Cancellation.coherentMul_cancel_left
    generator generator zero apart (NamedEquivalent.trans square (NamedEquivalent.symm multipliedZero))
  exact Purelib.Approximation.Gaussian.Division.Obstruction.Zero.ZeroIdentity.incompatible_apart sourceZero apart

end Purelib.Approximation.Gaussian.Provenance.Power.PowerIdentity
