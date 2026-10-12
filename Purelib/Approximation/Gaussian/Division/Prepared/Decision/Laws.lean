module
public import Purelib.Approximation.Gaussian.Division.Prepared.Decision
import Purelib.Approximation.Gaussian.Division.Obstruction.Zero
public import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Coherent
import Init.Prelude
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Division.Prepared

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

namespace Purelib.Approximation.Gaussian.Division.Prepared.Decision
section Decision

/-- Read whether the retained exact denominator decision carries a prepared nonzero denominator. -/
def isPrepared {channel :
  Coherent.CoherentNamed} : Decision channel → Bool
  | .prepared _ => true
  | .excluded _ => false

/-- For the retained exact denominator decision, operational zero is equivalent to absence of a prepared denominator. -/
theorem zero_iff_unpreparable {channel :
  Coherent.CoherentNamed} (decision : Decision channel) :
    Zero.IsZero channel ↔ ¬ Equivalence.IsPrepared channel := by
  constructor
  · rintro ⟨zero⟩ ⟨prepared⟩
    exact Obstruction.Zero.ZeroIdentity.incompatible_prepared zero prepared
  · intro unavailable
    cases decision with
    | prepared prepared => exact False.elim (unavailable ⟨prepared⟩)
    | excluded zero => exact ⟨zero⟩

/-- For the retained exact denominator decision, preparation is equivalent to absence of an operational zero identity.
-/
theorem prepared_iff_nonzero {channel :
  Coherent.CoherentNamed} (decision : Decision channel) :
    Equivalence.IsPrepared channel ↔ ¬ Zero.IsZero channel := by
  constructor
  · rintro ⟨prepared⟩ ⟨zero⟩
    exact Obstruction.Zero.ZeroIdentity.incompatible_prepared zero prepared
  · intro nonzero
    cases decision with
    | prepared prepared => exact ⟨prepared⟩
    | excluded zero => exact False.elim (nonzero ⟨zero⟩)

/-- The decision flag is true exactly when a prepared denominator exists. -/
theorem isPrepared_eq_true_iff {channel :
  Coherent.CoherentNamed} (decision : Decision channel) :
    decision.isPrepared = true ↔ Equivalence.IsPrepared channel := by
  cases decision with
  | prepared prepared => exact ⟨fun _ => ⟨prepared⟩, fun _ => rfl⟩
  | excluded zero =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨prepared⟩
        exact False.elim (Obstruction.Zero.ZeroIdentity.incompatible_prepared zero prepared)

/-- The decision flag is false exactly when the original denominator is operationally zero. -/
theorem isPrepared_eq_false_iff {channel :
  Coherent.CoherentNamed} (decision : Decision channel) :
    decision.isPrepared = false ↔ Zero.IsZero channel := by
  cases decision with
  | prepared prepared =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨zero⟩
        exact False.elim (Obstruction.Zero.ZeroIdentity.incompatible_prepared zero prepared)
  | excluded zero => exact ⟨fun _ => ⟨zero⟩, fun _ => rfl⟩

/-- Independently derived exact verdicts cannot disagree on equivalent inputs. Returned certificate data need not be
equal. This law deliberately does not cover the overlapping numerical small/apart classification. -/
theorem respects {first second :
  Coherent.CoherentNamed} (left : Decision first) (right : Decision second)
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name) : left.isPrepared = right.isPrepared :=
      by
  cases left with
  | prepared prepared =>
      cases right with
      | prepared _ => rfl
      | excluded zero =>
        exact False.elim (Obstruction.Zero.ZeroIdentity.incompatible_prepared zero (prepared.transport equivalent))
  | excluded zero =>
      cases right with
      | prepared prepared =>
        exact False.elim (Obstruction.Zero.ZeroIdentity.incompatible_prepared (zero.transport equivalent) prepared)
      | excluded _ => rfl

end Decision
end Purelib.Approximation.Gaussian.Division.Prepared.Decision

end
