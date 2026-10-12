module
public import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Init.Prelude
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

section
@[expose] public section

/-!
# Semantic completeness and invariance of exact division decisions

Exact zero means an executable operational comparison with zero exists;
preparability means an equivalent whole-ball-apart presentation exists.
Neither predicate demands pointwise equality of approximate candidates.
The converse completeness laws require a computed exact decision, supplied
below by rational provenance and by the separate algebraic client. They are
not equality decisions for arbitrary opaque channels.
-/

namespace Purelib.Approximation.Gaussian.Division.Prepared
namespace Equivalence

/-- The proposition that the original channel admits a retained equivalent whole-ball-apart denominator presentation. -/
def IsPrepared (channel : Coherent.CoherentNamed) :
  Prop := Nonempty (Prepared channel)

end Equivalence

/-- Retain the already computed denominator and its apartness. Only its comparison to the new input presentation
changes. -/
def transport {first second :
  Coherent.CoherentNamed} (prepared : Prepared first)
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name) : Prepared second :=
  { denominator := prepared.denominator
    apart := prepared.apart
    equivalent := NamedEquivalent.trans
      (NamedEquivalent.symm equivalent) prepared.equivalent }

namespace Equivalence

/-- Operationally equivalent coherent channels admit prepared denominator presentations exactly under the same
condition. -/
theorem isPrepared_respects {first second :
  Coherent.CoherentNamed}
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name) :
      IsPrepared first ↔
      IsPrepared second :=
  ⟨fun ⟨prepared⟩ => ⟨prepared.transport equivalent⟩,
    fun ⟨prepared⟩ => ⟨prepared.transport (NamedEquivalent.symm equivalent)⟩⟩

end Equivalence

end Purelib.Approximation.Gaussian.Division.Prepared

end
