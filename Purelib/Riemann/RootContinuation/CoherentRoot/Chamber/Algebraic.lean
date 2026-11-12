module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
public import Purelib.Approximation.Gaussian.Provenance.Algebraic.Comparison
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Algebraic evidence on retained original chamber root caches

The geometric trace keeps every original path segment and occurrence. Its
endpoint sidecar uses that exact retained numerical root cache, leaving branch
correspondence separate from numerical comparison at a fixed endpoint.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Chamber

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Provenance
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)

namespace Root

/-- Attach original chamber evidence using an exact retained ambient box.

Both the track and its complete certified cache are transported only along the
supplied box equality. The original isolated-owner evidence consumes this same
cache and positive input; no chamber owner lookup is executed.
-/
@[expose] def algebraicFromBox {frame : ChamberFrame} {index : frame.Index} (root : Root frame index)
    (box : Box) (same : box = (frame.owner index).box) : Algebraic.Sidecar root.certificate.value :=
  let retained : Σ track : WindingOneTrack frame.polynomial box, CertifiedName track :=
    same.symm ▸ ⟨root.track, root.certificate⟩
  let certificate := retained.2
  let evidence := Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated certificate frame.input.toPositive)
  have channelEq : certificate.value = root.certificate.value := by
    cases same
    rfl
  channelEq ▸ evidence

/-- The exact retained ambient produces the complete original isolated-root sidecar. -/
theorem algebraicFromBox_eq {frame : ChamberFrame} {index : frame.Index} (root : Root frame index)
    (box : Box) (same : box = (frame.owner index).box) :
    algebraicFromBox root box same =
      Algebraic.Sidecar.ofRoot (PolynomialRoot.Sidecar.ofIsolated root.certificate frame.input.toPositive) := by
  cases same
  rfl

/-- Attach algebraic evidence to the original chamber owner using its actual retained initial box. -/
@[expose] def algebraic {frame : ChamberFrame} {index : frame.Index} (root : Root frame index) :
    Algebraic.Sidecar root.certificate.value :=
  algebraicFromBox root root.track.initial.box root.initial_box

/-- The cached initial-box construction preserves the complete original chamber sidecar. -/
theorem algebraic_eq {frame : ChamberFrame} {index : frame.Index} (root : Root frame index) :
    root.algebraic = Algebraic.Sidecar.ofRoot
      (PolynomialRoot.Sidecar.ofIsolated root.certificate frame.input.toPositive) :=
  algebraicFromBox_eq root root.track.initial.box root.initial_box

/-- Chamber algebraic evidence reads the same actual original root samples. -/
theorem algebraic_sample {frame : ChamberFrame} {index : frame.Index} (root : Root frame index) (stage : Nat) :
    root.algebraic.residual.source.sample stage = root.certificate.approximation.sample stage := by
  rewrite [algebraic_eq]
  exact PolynomialRoot.Sidecar.ofIsolated_residual_sample root.certificate frame.input.toPositive stage

/-- Chamber algebraic evidence keeps the polynomial of its original frame. -/
theorem algebraic_polynomial {frame : ChamberFrame} {index : frame.Index} (root : Root frame index) :
    root.algebraic.polynomial = frame.polynomial := by
  rewrite [algebraic_eq]
  exact PolynomialRoot.Sidecar.ofIsolated_residual_polynomial root.certificate frame.input.toPositive

end Root

namespace Trace

set_option genInjectivity false in
/-- Original geometric continuation and algebraic sidecars on its actual retained initial and endpoint caches.

The numerical endpoint is not operationally identified with the starting
value. The same retained trace supplies their geometric branch correspondence.
-/
structure Algebraic {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source) where
  /-- The exact original trace, including all intermediate occurrences and numerical caches. -/
  original : Trace path index source
  /-- The retained trace is the supplied original trace. -/
  original_eq : original = trace
  /-- Algebraic evidence using the original starting root cache. -/
  initial : Provenance.Algebraic.Sidecar source.certificate.value
  /-- The initial evidence consumes the same original starting occurrence. -/
  initial_eq : initial = source.algebraic
  /-- Algebraic evidence using the actual retained endpoint root cache. -/
  endpoint : Provenance.Algebraic.Sidecar original.endpoint.certificate.value
  /-- The endpoint evidence consumes the same selected original endpoint occurrence. -/
  endpoint_eq : endpoint = original.endpoint.algebraic

constructive_injectivity Algebraic

namespace Algebraic

/-- Attach initial and endpoint algebraic evidence without rebuilding any original continuation cache. -/
@[expose] def ofTrace {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source) : Algebraic trace :=
  ⟨trace, rfl, source.algebraic, rfl, trace.endpoint.algebraic, rfl⟩

variable {start finish : ChamberFrame} {path : ChamberPath start finish}
variable {index : start.Index} {source : Root start index} {trace : Trace path index source}

/-- The attached endpoint sidecar reads exactly its same retained numerical cache. -/
theorem endpoint_sample (evidence : Algebraic trace) (stage : Nat) :
    evidence.endpoint.residual.source.sample stage =
      evidence.original.endpoint.certificate.approximation.sample stage := by
  rewrite [evidence.endpoint_eq]
  exact Root.algebraic_sample _ stage

/-- Endpoint comparison consumes both independent caches at the same selected original occurrence. -/
def compareEndpoint (evidence : Algebraic trace) (other : Root finish (path.finalIndex index))
    (firstStart secondStart : Nat := 0) :
    Provenance.Algebraic.Sidecar.Compared evidence.endpoint other.algebraic firstStart secondStart :=
  Provenance.Algebraic.Sidecar.compare evidence.endpoint other.algebraic firstStart secondStart

/-- Same-endpoint operational agreement follows from the original owner, keeping both numerical root programs. -/
def endpointEquivalent (evidence : Algebraic trace) (other : Root finish (path.finalIndex index)) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      evidence.original.endpoint.certificate.value.name other.certificate.value.name :=
  evidence.original.endpoint.namedEquivalent other

end Algebraic

end Trace

end Purelib.Riemann.RootContinuation.CoherentRoot.Chamber

end
