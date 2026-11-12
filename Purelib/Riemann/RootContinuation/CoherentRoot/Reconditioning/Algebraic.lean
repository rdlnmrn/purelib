module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning
public import Purelib.Approximation.Gaussian.Provenance.Algebraic
public import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison

/-!
# Retained algebraic evidence after original-cache reconditioning

The algebraic origin stores the original root certificate and actual restart.
Its numerical residual uses the unchanged original channel and the actual
restarted sample program, so later arithmetic retains both ownership and work.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning

open Purelib.RootIsolation
open Purelib.Approximation.Gaussian.Provenance

variable {polynomial : GaussianPolynomial} {ambient : Box}
variable {track : WindingOneTrack polynomial ambient}
variable {original : CertifiedName track} {start : Nat}

/-- Attach the original owner and actual restart to algebraic evidence on the unchanged original channel. -/
@[expose] def algebraic (prepared : Reconditioning original start) (input : FTA.Squarefree.Input polynomial) :
    Algebraic.Sidecar original.value :=
  Algebraic.Sidecar.ofReconditioning original input prepared

/-- Attach the original restart while consuming an exact cached ambient box.

The ambient equality transports the original track, certificate and restart
together. The algebraic origin retains those same original owners and samples,
without requesting a second executable ambient-box producer.
-/
@[expose] def algebraicFromAmbient (cachedAmbient : Box) (same : cachedAmbient = ambient)
    (prepared : Reconditioning original start) (input : FTA.Squarefree.Input polynomial) :
    Algebraic.Sidecar original.value := by
  subst ambient
  exact prepared.algebraic input

/-- Exact cached ambient transport preserves the complete original algebraic attachment. -/
theorem algebraicFromAmbient_eq (cachedAmbient : Box) (same : cachedAmbient = ambient)
    (prepared : Reconditioning original start) (input : FTA.Squarefree.Input polynomial) :
    prepared.algebraicFromAmbient cachedAmbient same input = prepared.algebraic input := by
  cases same
  rfl

/-- Reconditioned algebraic evidence retains the original polynomial. -/
theorem algebraic_polynomial (prepared : Reconditioning original start) (input : FTA.Squarefree.Input polynomial) :
    (prepared.algebraic input).polynomial = polynomial := rfl

/-- Reconditioned algebraic evidence reads the same actual restarted samples. -/
theorem algebraic_sample (prepared : Reconditioning original start) (input : FTA.Squarefree.Input polynomial)
    (index : Nat) :
    (prepared.algebraic input).residual.source.sample index = prepared.root.approximation.sample index := rfl

/-- Reconditioned algebraic evidence stores the original owner and the actual retained restart in its construction. -/
theorem algebraic_origin (prepared : Reconditioning original start) (input : FTA.Squarefree.Input polynomial) :
    (prepared.algebraic input).origin = .recondition original input prepared := rfl

/-- Compare original-cache and restarted-cache algebraic constructions on their unchanged original channel. -/
def compareOriginal (prepared : Reconditioning original start) (input : FTA.Squarefree.Input polynomial)
    (firstStart secondStart : Nat := 0) :
    Algebraic.Sidecar.Compared
      (Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated original input.toPositive))
      (prepared.algebraic input) firstStart secondStart :=
  Algebraic.Sidecar.compare _ _ firstStart secondStart

end Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning

end
