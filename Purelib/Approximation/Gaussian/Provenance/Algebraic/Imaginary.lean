module

public import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Conjugate
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Imaginary separation of an original algebraic construction

The original sidecar and its actual conjugation are retained together. Their
ordered difference uses the existing complete comparison cache and its exact
decision. A prepared difference additionally supplies the finite original-input
separation; an excluded difference retains its original zero certificate.
-/

public section

namespace Purelib.Approximation.Gaussian.Provenance.Algebraic.Sidecar

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Process.Imaginary (Separation)

/-- The retained bridge data for the existing exact difference decision.

The excluded case keeps its zero certificate in the original decision. The
prepared case keeps the exact paid observations and separation produced from
that same prepared denominator.
-/
@[expose] def ImaginaryEvidence {channel : CoherentNamed} {original : Sidecar channel}
    (compared : Compared original.conj original) : Type 1 :=
  match compared.decision with
  | .excluded _ => PUnit
  | .prepared prepared =>
      (observed : Separation.ConjugateObservations channel prepared (Separation.conjugateGap prepared ^ 2)) ×
        { result : Separation channel // result = observed.separation (Separation.conjugateGap_positive prepared)
          (Separation.conjugateGap_paid prepared) }

set_option genInjectivity false in
/-- Both actual original channels and the same cached algebraic difference decision.

The comparison retains the complete conjugated and original sidecars as its
left and right inputs, respectively. Its cached difference is the original
input minus its actual conjugate; the bridge uses its same stored decision.
-/
structure ImaginaryInspection (channel : CoherentNamed) (original : Sidecar channel) where
  /-- The actual original coherent channel. -/
  source : CoherentNamed
  /-- The source is the exact supplied original channel. -/
  source_eq : source = channel
  /-- The actual conjugated coherent channel. -/
  conjugated : CoherentNamed
  /-- The retained conjugation uses the same original channel. -/
  conjugated_eq : conjugated = channel.conj
  /-- Both actual sidecars and their once-computed complete ordered difference. -/
  compared : Compared original.conj original
  /-- The original excluded decision or the prepared decision's same finite separation data. -/
  evidence : ImaginaryEvidence compared

constructive_injectivity ImaginaryInspection

/-- Resolve the actual imaginary difference once and retain its original paid outcome.

This explicit operation may perform complete algebraic resolution. It preserves
the existing scalar-first resolver, the original sidecar and conjugate caches,
and the complete original zero decision when no separation is prepared.
-/
@[noinline, nospecialize] def inspectImaginary (channel : CoherentNamed) (original : Sidecar channel) :
    ImaginaryInspection channel original :=
  let conjugated := channel.conj
  let conjugatedSidecar := original.conj
  let compared := Compared.fallback conjugatedSidecar original 0 0
  let evidence : ImaginaryEvidence compared := by
    unfold ImaginaryEvidence
    split
    · exact PUnit.unit
    · rename_i prepared selected
      exact Separation.ofConjugatePrepared prepared
  ⟨channel, rfl, conjugated, rfl, compared, evidence⟩

end Purelib.Approximation.Gaussian.Provenance.Algebraic.Sidecar

end
