module

public import Purelib.Approximation.Gaussian.Name.Coherent.Apart
public import Purelib.Approximation.Gaussian.Process.Sampling

/-! # Actual state transport under equality of complete coherent names

Equality transports the same original process state and its possibility
proof. The full coherent-name equality also preserves the original semantic
allowance. Apartification reads that allowance from its stored source state.
-/

public section

namespace Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)

/-- Reindex one original process state along equality of the complete coherent names. -/
@[expose] def castState {first last : CoherentNamed} (equal : first = last)
    (state : first.name.process.State) : last.name.process.State :=
  Process.Sampling.castState (congrArg (fun value : CoherentNamed => value.name.process) equal) state

/-- The reindexed original state admits every same retained possible reading. -/
theorem possible_castState {first last : CoherentNamed} (equal : first = last)
    (state : first.name.process.State) {candidate : Canonical}
    (possible : first.name.process.Possible state candidate) :
    last.name.process.Possible (castState equal state) candidate :=
  Process.Sampling.possible_castState (congrArg (fun value : CoherentNamed => value.name.process) equal) state possible

/-- Complete coherent-name equality preserves the whole original enclosure at the transported actual state. -/
theorem castState_ball {first last : CoherentNamed} (equal : first = last) (state : first.name.process.State) :
    last.name.process.ball (castState equal state) = first.name.process.ball state := by
  cases equal
  rfl

/-- Complete coherent-name equality preserves the semantic allowance of the transported original state. -/
theorem castState_allowance {first last : CoherentNamed} (equal : first = last) (state : first.name.process.State) :
    last.coherent.allowance (castState equal state) = first.coherent.allowance state := by
  cases equal
  rfl

/-- Apartification retains exactly the original source state's semantic allowance. -/
theorem apartify_allowance (value : CoherentNamed)
    (apart : Process.Apart.Possible.PossibleApart value.name.process)
    (state : (value.apartify apart).name.process.State) :
    (value.apartify apart).coherent.allowance state = value.coherent.allowance state.source := rfl

end Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
