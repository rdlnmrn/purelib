module

public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Separated
public import Purelib.Approximation.Gaussian.Provenance.Algebraic.Imaginary

/-!
# Explicit algebraic imaginary provider

An already inspected algebraic imaginary difference supplies the existing
all-row provider when its actual retained decision is prepared. An excluded
difference remains available in the same original inspection.
-/

public section

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Algebraic

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Algebraic (Sidecar)

/-- The provider outcome indexed by an existing imaginary-difference decision.

An excluded difference retains its zero certificate in the original
inspection. A prepared difference supplies the existing provider on that
same original input channel.
-/
@[expose] def ImaginaryProviderOutcome {channel : CoherentNamed} {original : Sidecar channel}
    (inspection : Sidecar.ImaginaryInspection channel original) : Type 1 :=
  match inspection.compared.decision with
  | .excluded _ => PUnit
  | .prepared _ => Basic.Provider channel

/-- Reuse the supplied original inspection and prepare all rows only on its separated branch.

The returned inspection is the exact input, including both original sidecars,
the computed difference decision and paid observations. No new algebraic
resolution, imaginary observation or zero decision is performed.
-/
@[noinline, nospecialize] def imaginaryProvider {channel : CoherentNamed} {original : Sidecar channel}
    (inspection : Sidecar.ImaginaryInspection channel original) :
    (saved : { value : Sidecar.ImaginaryInspection channel original // value = inspection }) ×
      ImaginaryProviderOutcome saved.val := by
  refine ⟨⟨inspection, rfl⟩, ?_⟩
  have evidence := inspection.evidence
  unfold Sidecar.ImaginaryEvidence at evidence
  unfold ImaginaryProviderOutcome
  split
  · exact PUnit.unit
  · rename_i prepared selected
    split at evidence
    · rename_i zero excluded
      cases excluded.symm.trans selected
    · rename_i actual retained
      cases Division.Prepared.Decision.prepared.inj (retained.symm.trans selected)
      exact Separated.provider evidence.2.val

end Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Algebraic

end
