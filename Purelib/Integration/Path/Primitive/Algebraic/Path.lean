module

public import Purelib.Integration.Path.Primitive.Algebraic.Numerical
public import Purelib.Data.Vector.Dependent
public import Purelib.Approximation.Gaussian.Provenance.Algebraic
import Purelib.Data.List.OfFn.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Chain.PathBoundary
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Integration.Path.Primitive
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original finite paths of admitted algebraic primitives

Each stored edge keeps the formal primitive identity and the actual finite
cell comparisons on its original integration program. A structural fold of
its original occurrence bank constructs the existing primitive path, retaining
every program and the exact original endpoint bank.
-/

public section

namespace Purelib.Integration.Path.Primitive.Algebraic

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Chain
open Purelib.Integration.Program.Comparison (RefinementProgram)
open Purelib.Data.Vector (DependentVector)

variable {Chart : Type} {sheets count : Nat}
    {polynomialAt : Chart → Coefficients} {rootAt : Chart → LiftedPoint sheets → RootReading}

local notation "Bank" => EndpointBank Chart sheets count polynomialAt rootAt

set_option genInjectivity false in
/-- An admitted original edge with its exact primitive and retained numerical construction.

Both endpoints use the same chart primitive. The formal certificate retains
its actual derivative check; the numerical models retain the original lifted
points, endpoint observations, program cells and derivative-residual budget.
No integral-equivalence conclusion is supplied as a construction input. -/
structure EdgeAdmission (bank : Bank) (edge : OrientedEdge count) where
  /-- The original differential expression in the starting endpoint's chart. -/
  differential : Expression (polynomialAt (bank edge.start).chart)
  /-- The actual cached finite exact-primitive check for that source differential. -/
  exact : Exact differential (bank edge.start).primitive
  /-- Both original endpoint occurrences belong to the same actual chart. -/
  chart_eq : (bank edge.finish).chart = (bank edge.start).chart
  /-- The original finishing primitive is the same chart primitive as the original starting primitive. -/
  primitive_eq : HEq (bank edge.finish).primitive (bank edge.start).primitive
  /-- The retained original starting endpoint's numerical sampler. -/
  startSampling : Endpoint.Sampling (bank edge.start)
  /-- The retained original finishing endpoint's numerical sampler. -/
  finishSampling : Endpoint.Sampling (bank edge.finish)
  /-- The actual original integration program for this edge occurrence. -/
  program : RefinementProgram
  /-- The original lifted path, local polynomial primitives, residual caches and numerical budget. -/
  models : PrimitiveEdge.PolynomialModels (bank edge.start).point (bank edge.finish).point
    startSampling.source finishSampling.source program
  /-- The numerical primitive edge constructed once from these same retained source models. -/
  numerical : PrimitiveEdge (bank edge.start).channel (bank edge.finish).channel
  /-- The cached numerical edge is the canonical construction from these original models. -/
  numerical_eq : numerical = startSampling.edgeTo finishSampling program models

constructive_injectivity EdgeAdmission

namespace EdgeAdmission

/-- Admit and retain an original edge by combining its checked exact primitive with its actual source models. -/
@[expose, noinline, nospecialize] def build (bank : Bank) (edge : OrientedEdge count)
    (differential : Expression (polynomialAt (bank edge.start).chart))
    (exact : Exact differential (bank edge.start).primitive)
    (chart : (bank edge.finish).chart = (bank edge.start).chart)
    (primitive : HEq (bank edge.finish).primitive (bank edge.start).primitive)
    (startSampling : Endpoint.Sampling (bank edge.start)) (finishSampling : Endpoint.Sampling (bank edge.finish))
    (program : RefinementProgram)
    (models : PrimitiveEdge.PolynomialModels (bank edge.start).point (bank edge.finish).point
      startSampling.source finishSampling.source program) : EdgeAdmission bank edge :=
  let numerical := startSampling.edgeTo finishSampling program models
  ⟨differential, exact, chart, primitive, startSampling, finishSampling, program, models, numerical, rfl⟩

/-- The admitted numerical edge consumes its actual retained original program. -/
theorem numerical_program {bank : Bank} {edge : OrientedEdge count} (admission : EdgeAdmission bank edge) :
    admission.numerical.program = admission.program := by
  rewrite [admission.numerical_eq]
  exact admission.startSampling.edgeTo_program admission.finishSampling admission.program admission.models

end EdgeAdmission

/-- The cached per-occurrence numerical admissions on one original structural edge vector.

Repeated occurrences keep separate original programs and cell caches. The
family is indexed by the actual original edge vector and endpoint bank. -/
abbrev Admissions (bank : Bank) {steps : Nat} (edges : Data.Vector (OrientedEdge count) steps) :=
  DependentVector (fun position => EdgeAdmission bank (edges position))

namespace Admissions

/-- Construct the original numerical primitive path by traversing the retained occurrence and admission spines.

The endpoint proof supplies only literal vertex alignments. Each actual
stored numerical edge and retained tail are reused without reconstructing
cell comparisons or replacing original integration programs. -/
@[noinline, nospecialize] def toPath (bank : Bank) : {steps : Nat} →
    (edges : Data.Vector (OrientedEdge count) steps) → Admissions bank edges →
    {start finish : Fin count} →
    PathBoundary.PathEndpoints edgeStart edgeFinish (List.ofFn fun position => edges position) start finish →
    PrimitivePath (bank start).channel (bank finish).channel
  | _, .nil, .nil, _, _, path => by
      have endpoint := path.nil_eq
      cases endpoint
      exact .nil _
  | _, .cons edge remaining, .cons admission tail, start, finish, path => by
      rewrite [Data.List.OfFn.Basic.ofFn_succ] at path
      have initial := path.cons_start
      have remainingPath := path.cons_tail
      cases initial
      exact .cons admission.numerical (toPath bank remaining tail remainingPath)

/-- Close the constructed path at the same original algebraic endpoint and retain its endpoint cancellation.

Literal closure keeps the original lifted sheet and chart owner. A path with
different endpoint bank keys needs explicit transport evidence separately. -/
@[noinline, nospecialize] def closed (bank : Bank) {steps : Nat}
    (edges : Data.Vector (OrientedEdge count) steps) (admissions : Admissions bank edges)
    {start : Fin count}
    (path : PathBoundary.PathEndpoints edgeStart edgeFinish (List.ofFn fun position => edges position) start start) :
    ClosedPrimitiveBoundary :=
  ClosedPrimitiveBoundary.ofLoop (admissions.toPath bank edges path)

end Admissions

namespace Endpoint

open Purelib.Approximation.Gaussian

/-- Interpret the retained endpoint coefficients using its original admitted root.

The caller supplies intrinsic algebraic evidence for the exact root channel;
the endpoint's square equation alone does not construct that admission. The
cached divided coefficients and original endpoint channel are reused. -/
@[expose] def sidecar (endpoint : Endpoint Chart sheets polynomialAt rootAt)
    (root : Provenance.Algebraic.Sidecar endpoint.root.1) : Provenance.Algebraic.Sidecar endpoint.channel := by
  unfold channel
  rewrite [endpoint.denotation.channel_eq]
  exact (Provenance.Algebraic.Sidecar.ofRational
    (Provenance.Rational.Basic.RationalSidecar.exact endpoint.denotation.value.re)).add
      ((Provenance.Algebraic.Sidecar.ofRational
        (Provenance.Rational.Basic.RationalSidecar.exact endpoint.denotation.value.im)).mul root)

end Endpoint

end Purelib.Integration.Path.Primitive.Algebraic

namespace Purelib.Integration.Path.Primitive

open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

/-- Construct the endpoint difference from the original two algebraic sidecars. -/
@[expose] def primitiveDifferenceSidecar {start finish : CoherentNamed}
    (startEvidence : Algebraic.Sidecar start) (finishEvidence : Algebraic.Sidecar finish) :
    Algebraic.Sidecar (primitiveDifference start finish) :=
  startEvidence.neg.add finishEvidence

/-- Attach admitted endpoints to the original primitive edge's integration output.

The edge's retained integration comparison transports their constructed
difference to the unchanged program output. -/
@[expose] def PrimitiveEdge.outputSidecar {start finish : CoherentNamed}
    (edge : PrimitiveEdge start finish) (startEvidence : Algebraic.Sidecar start)
    (finishEvidence : Algebraic.Sidecar finish) : Algebraic.Sidecar edge.program.output :=
  (primitiveDifferenceSidecar startEvidence finishEvidence).transport edge.integral_eq_difference

/-- Attach admitted endpoint evidence to the original primitive-path output sum.

The retained endpoint sidecars construct their difference, which is transported
along the path's actual integral comparison. The path and its ordered edge
programs remain the owners of the resulting channel. -/
@[expose] def PrimitivePath.integralSumSidecar {start finish : CoherentNamed}
    (path : PrimitivePath start finish) (startEvidence : Algebraic.Sidecar start)
    (finishEvidence : Algebraic.Sidecar finish) : Algebraic.Sidecar path.integralSum :=
  (primitiveDifferenceSidecar startEvidence finishEvidence).transport path.integralSum_eq_difference

/-- Attach the retained closed boundary's exact zero to its original integral output sum.

The boundary supplies both the original path comparison and its closure
witness; no identification of distinct geometric endpoints is introduced. -/
@[expose] def ClosedPrimitiveBoundary.integralSumSidecar (boundary : ClosedPrimitiveBoundary) :
    Algebraic.Sidecar boundary.integralSum :=
  Algebraic.Sidecar.ofRational ⟨0, boundary.integralSum_zero⟩

end Purelib.Integration.Path.Primitive

end
