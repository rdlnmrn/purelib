module

public import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic
public import Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning.Algebraic
public import Purelib.Riemann.RootContinuation.CoherentRoot.Accelerated
public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Algebraic
public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Arithmetic
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Construction
import Purelib.Approximation.Gaussian.Provenance.PolynomialRoot

/-!
# Production annotations on original continued and restarted root caches

The annotation keeps the exact coherent channel. Its algebraic construction
retains the original root owner, and a restart consumes its actual restarted
sample program without acquiring a replacement isolated root.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Annotated

open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open CoherentRoot.Chamber (Root Trace)
open Purelib.Polynomial.Dense.Companion (Operation)
open Purelib.Polynomial.Approximation.Gaussian renaming Arithmetic -> PolynomialArithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Provenance

/-- Attach the compared accelerated source to its retained original root channel.

This is the initial algebraic attachment to a bare original root. The bridge
retains its paid state, actual new numerical root and computed original-channel
comparison; no existing arithmetic sidecar or child cache is replaced.
-/
@[expose] def ofAccelerated {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {input : FTA.Squarefree.Input polynomial} {track : CoherentRoot.WindingOneTrack polynomial ambient}
    {start : Nat} (prepared : CoherentRoot.Accelerated input track start) : Annotated :=
  algebraic prepared.algebraic

/-- An accelerated-source annotation keeps the exact retained original channel. -/
theorem ofAccelerated_channel {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {input : FTA.Squarefree.Input polynomial} {track : CoherentRoot.WindingOneTrack polynomial ambient}
    {start : Nat} (prepared : CoherentRoot.Accelerated input track start) :
    (ofAccelerated prepared).channel = prepared.original.value := rfl

/-- An accelerated annotation retains that same compared algebraic source and its complete origin. -/
theorem ofAccelerated_provenance {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {input : FTA.Squarefree.Input polynomial} {track : CoherentRoot.WindingOneTrack polynomial ambient}
    {start : Nat} (prepared : CoherentRoot.Accelerated input track start) :
    (ofAccelerated prepared).provenance = some (.algebraic prepared.algebraic) := rfl

/-- Annotate the unchanged original root channel with its actual retained reconditioned algebraic cache. -/
@[expose] def ofReconditioning {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} {original : CoherentRoot.CertifiedName track}
    {start : Nat} (prepared : CoherentRoot.Reconditioning original start) (input : FTA.Squarefree.Input polynomial) :
    Annotated :=
  algebraic (prepared.algebraic input)

/-- A reconditioning annotation retains the exact original coherent channel. -/
theorem ofReconditioning_channel {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient} {original : CoherentRoot.CertifiedName track}
    {start : Nat} (prepared : CoherentRoot.Reconditioning original start) (input : FTA.Squarefree.Input polynomial) :
    (ofReconditioning prepared input).channel = original.value := rfl

/-- Annotate the exact selected original chamber occurrence using its retained numerical root cache. -/
@[expose] def ofChamberRoot {frame : ChamberFrame} {index : frame.Index}
    (root : CoherentRoot.Chamber.Root frame index) : Annotated :=
  algebraic root.algebraic

/-- A chamber-root annotation retains the same original root channel. -/
theorem ofChamberRoot_channel {frame : ChamberFrame} {index : frame.Index}
    (root : CoherentRoot.Chamber.Root frame index) : (ofChamberRoot root).channel = root.certificate.value := rfl

/-- Annotate the actual retained trace endpoint while its separate trace evidence keeps all geometric occurrences. -/
@[expose] def ofTraceEndpoint {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : CoherentRoot.Chamber.Root start index}
    {trace : CoherentRoot.Chamber.Trace path index source} (evidence : CoherentRoot.Chamber.Trace.Algebraic trace) :
    Annotated :=
  algebraic evidence.endpoint

/-- An endpoint annotation retains the actual same cached endpoint channel. -/
theorem ofTraceEndpoint_channel {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : CoherentRoot.Chamber.Root start index}
    {trace : CoherentRoot.Chamber.Trace path index source} (evidence : CoherentRoot.Chamber.Trace.Algebraic trace) :
    (ofTraceEndpoint evidence).channel = evidence.original.endpoint.certificate.value := rfl

section

variable {firstStart firstFinish secondStart secondFinish : ChamberFrame}
variable {firstPath : ChamberPath firstStart firstFinish} {secondPath : ChamberPath secondStart secondFinish}
variable {firstIndex : firstStart.Index} {secondIndex : secondStart.Index}
variable {firstRoot : Root firstStart firstIndex} {secondRoot : Root secondStart secondIndex}
variable {firstTrace : Trace firstPath firstIndex firstRoot} {secondTrace : Trace secondPath secondIndex secondRoot}

/-- Annotate arithmetic on the two original starting caches of retained input traces.

The supplied algebraic evidence retains both complete paths and original
occurrences. Its starting sidecars are consumed by the ordinary annotation
operation; no endpoint channel is identified with a starting value.
-/
@[expose] def ofTraceInitialArithmetic (operation : Operation)
    (first : Trace.Algebraic firstTrace) (second : Trace.Algebraic secondTrace) : Annotated :=
  match operation with
  | .add => (algebraic first.initial).add (algebraic second.initial)
  | .mul => (algebraic first.initial).mul (algebraic second.initial)

/-- Initial trace arithmetic is the ordinary annotation operation on both retained starting sidecars. -/
theorem ofTraceInitialArithmetic_eq (operation : Operation)
    (first : Trace.Algebraic firstTrace) (second : Trace.Algebraic secondTrace) :
    ofTraceInitialArithmetic operation first second = match operation with
      | .add => (algebraic first.initial).add (algebraic second.initial)
      | .mul => (algebraic first.initial).mul (algebraic second.initial) := by
  cases operation <;> rfl

/-- Initial trace arithmetic retains its actual algebraic operation and both starting child caches. -/
theorem ofTraceInitialArithmetic_provenance (operation : Operation)
    (first : Trace.Algebraic firstTrace) (second : Trace.Algebraic secondTrace) :
    (ofTraceInitialArithmetic operation first second).provenance =
      match operation with
      | .add => some (.algebraic (first.initial.add second.initial))
      | .mul => some (.algebraic (first.initial.mul second.initial)) := by
  cases operation <;> rfl

/-- Initial trace arithmetic keeps the operation on both actual starting channels. -/
theorem ofTraceInitialArithmetic_channel (operation : Operation)
    (first : Trace.Algebraic firstTrace) (second : Trace.Algebraic secondTrace) :
    (ofTraceInitialArithmetic operation first second).channel =
      PolynomialArithmetic.channel operation firstRoot.certificate.value secondRoot.certificate.value := by
  cases operation <;> rfl

/-- Annotate arithmetic on the two actual selected endpoint caches of retained input traces.

The source paths, endpoint occurrence indices and original sidecars remain in
the supplied evidence. Arithmetic consumes these exact endpoint caches even
when distinct ordered input occurrences produce coincident results.
-/
@[expose] def ofTraceEndpointArithmetic (operation : Operation)
    (first : Trace.Algebraic firstTrace) (second : Trace.Algebraic secondTrace) : Annotated :=
  match operation with
  | .add => (ofTraceEndpoint first).add (ofTraceEndpoint second)
  | .mul => (ofTraceEndpoint first).mul (ofTraceEndpoint second)

/-- Endpoint trace arithmetic is the ordinary annotation operation on both actual selected endpoint sidecars. -/
theorem ofTraceEndpointArithmetic_eq (operation : Operation)
    (first : Trace.Algebraic firstTrace) (second : Trace.Algebraic secondTrace) :
    ofTraceEndpointArithmetic operation first second = match operation with
      | .add => (ofTraceEndpoint first).add (ofTraceEndpoint second)
      | .mul => (ofTraceEndpoint first).mul (ofTraceEndpoint second) := by
  cases operation <;> rfl

/-- Endpoint trace arithmetic retains its actual algebraic operation and both selected original child caches. -/
theorem ofTraceEndpointArithmetic_provenance (operation : Operation)
    (first : Trace.Algebraic firstTrace) (second : Trace.Algebraic secondTrace) :
    (ofTraceEndpointArithmetic operation first second).provenance =
      match operation with
      | .add => some (.algebraic (first.endpoint.add second.endpoint))
      | .mul => some (.algebraic (first.endpoint.mul second.endpoint)) := by
  cases operation <;> rfl

/-- Endpoint trace arithmetic keeps the operation on both retained selected channels. -/
theorem ofTraceEndpointArithmetic_channel (operation : Operation)
    (first : Trace.Algebraic firstTrace) (second : Trace.Algebraic secondTrace) :
    (ofTraceEndpointArithmetic operation first second).channel =
      PolynomialArithmetic.channel operation first.original.endpoint.certificate.value
        second.original.endpoint.certificate.value := by
  cases operation <;> rfl

/-- Starting annotations agree with the arithmetic cache on those same original starting occurrences.

This comparison uses only the source configuration. The indexed arithmetic
certificate separately retains its canonical initial and endpoint readbacks
and both original geometric input paths.
-/
def traceInitialArithmeticEquivalent {operation : Operation}
    (first : Trace.Algebraic firstTrace) (second : Trace.Algebraic secondTrace)
    (arithmetic : CoherentRoot.Chamber.Arithmetic operation firstTrace secondTrace) :
    NamedEquivalent (ofTraceInitialArithmetic operation first second).channel.name
      arithmetic.initial.result.toApproximation.toNamed := by
  rewrite [ofTraceInitialArithmetic_channel]
  exact arithmetic.initial.equivalent

/-- Endpoint annotations agree with arithmetic after the same original input traces.

The retained trace equalities identify the two actual selected occurrences.
The comparison is entirely at that endpoint configuration and does not equate
the changing root values with their values at the source parameters.
-/
def traceEndpointArithmeticEquivalent {operation : Operation}
    (first : Trace.Algebraic firstTrace) (second : Trace.Algebraic secondTrace)
    (arithmetic : CoherentRoot.Chamber.Arithmetic operation firstTrace secondTrace) :
    NamedEquivalent (ofTraceEndpointArithmetic operation first second).channel.name
      arithmetic.endpoint.result.toApproximation.toNamed := by
  rewrite [ofTraceEndpointArithmetic_channel, first.original_eq, second.original_eq]
  exact arithmetic.endpointEquivalent

/-- Compare annotated continuation with independently retained arithmetic at the same selected endpoints.

Each independent root has the original path's selected owner index. The two
input occurrence comparisons are composed through the retained arithmetic
cache; close readings or equal result polynomials do not select the branches.
-/
def compareTraceEndpointArithmetic {operation : Operation}
    (first : Trace.Algebraic firstTrace) (second : Trace.Algebraic secondTrace)
    (arithmetic : CoherentRoot.Chamber.Arithmetic operation firstTrace secondTrace)
    (firstEnd : Root firstFinish (firstPath.finalIndex firstIndex))
    (secondEnd : Root secondFinish (secondPath.finalIndex secondIndex))
    (other : CoherentRoot.Arithmetic operation firstEnd.certificate secondEnd.certificate) :
    NamedEquivalent (ofTraceEndpointArithmetic operation first second).channel.name
      other.result.toApproximation.toNamed :=
  NamedEquivalent.trans (traceEndpointArithmeticEquivalent first second arithmetic)
    (arithmetic.compareEndpoint firstEnd secondEnd other)

end

/-- Compare complete checked expressions on independent caches at the same selected original trace endpoints.

Each atom keeps its own path, starting occurrence and retained endpoint.
The comparison covers the complete checked grammar, using both original
construction trees and their actual reciprocal preparations. It asserts
agreement at those endpoints, without identifying values at different path
parameters or selecting arithmetic branches from matching polynomials.
-/
def compareTraceEndpointExpression {arity : Nat}
    {starts finishes : Fin arity → ChamberFrame}
    {paths : (index : Fin arity) → ChamberPath (starts index) (finishes index)}
    {indices : (index : Fin arity) → (starts index).Index}
    {sources : (index : Fin arity) → Root (starts index) (indices index)}
    {traces : (index : Fin arity) → Trace (paths index) (indices index) (sources index)}
    (evidence : (index : Fin arity) → Trace.Algebraic (traces index))
    (others : (index : Fin arity) → Root (finishes index) ((paths index).finalIndex (indices index)))
    {expression : Checked.Expr arity}
    (first : Checked.Construction.Result (fun index => ofTraceEndpoint (evidence index)) expression)
    (second : Checked.Construction.Result (fun index => ofChamberRoot (others index)) expression) :
    NamedEquivalent first.channel.name second.channel.name :=
  first.namedEquivalent second (fun index => (evidence index).endpointEquivalent (others index))

/-- Complete checked arithmetic respects the actual retained reconditioning of every original root atom.

The before and after constructions keep their original isolated-root channels,
source caches and denominator preparations. Each input comparison consumes
its actual retained restart, while repeated and unused occurrences follow the
existing checked construction and its demand-cached atom comparisons.
-/
def compareReconditionedExpression {arity : Nat}
    {polynomials : Fin arity → CoherentRoot.GaussianPolynomial} {ambients : Fin arity → CoherentRoot.Box}
    {tracks : (index : Fin arity) → CoherentRoot.WindingOneTrack (polynomials index) (ambients index)}
    {originals : (index : Fin arity) → CoherentRoot.CertifiedName (tracks index)} {starts : Fin arity → Nat}
    (restarts : (index : Fin arity) → CoherentRoot.Reconditioning (originals index) (starts index))
    (inputs : (index : Fin arity) → FTA.Squarefree.Input (polynomials index))
    {expression : Checked.Expr arity}
    (first : Checked.Completed
      (fun index => polynomialRoot (PolynomialRoot.Sidecar.ofIsolated (originals index) (inputs index).toPositive))
      expression)
    (second : Checked.Completed
      (fun index => polynomialRoot (PolynomialRoot.Sidecar.ofIsolated (restarts index).root (inputs index).toPositive))
      expression) :
    NamedEquivalent first.channel.name second.channel.name :=
  first.namedEquivalent second (fun index => (restarts index).namedEquivalent (inputs index))

end Purelib.Approximation.Gaussian.Acquisition.Annotated

end
