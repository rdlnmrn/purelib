module

import Purelib.Data.Gaussian.Inverse.Prepared
public import Purelib.Data.Gaussian.Basic
import Purelib.System.IO

namespace TestPurelib.Data.Gaussian.Inverse.Prepared

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

example (source : Canonical) : (source.prepareNorm).val = source.normSq := source.prepareNorm_eq

example (source : Canonical) (norm : { value : Rational // value = source.normSq }) :
    source.inverseFromNorm norm = source⁻¹ := source.inverseFromNorm_eq norm

example (source : Canonical) : source.preparedInverse = source⁻¹ := source.preparedInverse_eq

example : (0 : Canonical).preparedInverse = 0 := by decide +kernel

example (real : Rational) : (⟨real, 0⟩ : Canonical).preparedInverse = ⟨real⁻¹, 0⟩ := rfl

example : (⟨0, -2 / 3⟩ : Canonical).preparedInverse = ⟨0, 3 / 2⟩ := by decide +kernel

example : (⟨3, 4⟩ : Canonical).preparedInverse =
    (⟨⟨3, 25, by decide, ⟨⟨-8, 1, by decide⟩⟩⟩,
      ⟨-4, 25, by decide, ⟨⟨-6, 1, by decide⟩⟩⟩⟩ : Canonical) := by decide +kernel

/-- Check exact prepared norm and inverse agreement at zero, both signed axes and nonreal sources. -/
public def check : IO Unit := do
  let sources : List Canonical :=
    [0, 1, -1, ⟨2 / 3, 0⟩, ⟨-2 / 3, 0⟩, ⟨0, 2⟩, ⟨0, -2 / 3⟩, ⟨3, 4⟩, ⟨2 / 3, -5 / 7⟩]
  for source in sources do
    let norm := source.prepareNorm
    unless norm.val = source.normSq do
      throw (IO.userError "prepared norm changed the complete original rational")
    unless source.inverseFromNorm norm = source⁻¹ do
      throw (IO.userError "inverse from retained norm changed the complete original Gaussian")
    unless source.preparedInverse = source⁻¹ do
      throw (IO.userError "prepared inverse changed original zero or signed nonreal behavior")
  Purelib.System.IO.println "prepared Gaussian norm/inverse: zero, signed axes and nonreal original records agree"

/-- Evaluate the unchanged norm-based reciprocal behind a separate native call boundary. -/
@[noinline] private def originalInverse (source : Canonical) : IO Canonical :=
  pure (source.inverseFromNorm source.prepareNorm)

/-- Evaluate the prepared reciprocal behind a separate native call boundary. -/
@[noinline] private def prepared (source : Canonical) : IO Canonical := pure source.preparedInverse

/-- Compare complete reciprocal records and quiet timings on the same retained finite input.

The original prepared-norm formula remains the reference. Separate native
call boundaries prevent either timed computation from reusing the other's
result; record comparison happens after both timings.
-/
public def profile (source : Canonical) : IO Unit := do
  let started ← IO.monoNanosNow
  let original ← originalInverse source
  let originalEnded ← IO.monoNanosNow
  let actual ← prepared source
  let preparedEnded ← IO.monoNanosNow
  unless actual = original do
    throw (IO.userError "prepared inverse changed the complete original Gaussian record")
  Purelib.System.IO.println s!"prepared Gaussian inverse: norm {originalEnded - started} ns, \
    prepared {preparedEnded - originalEnded} ns; complete original record retained"

end TestPurelib.Data.Gaussian.Inverse.Prepared
