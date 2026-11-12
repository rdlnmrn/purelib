module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Pieces
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Alignment.Queries
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Endpoints
public import Purelib.Riemann.Paths.OwnerTracePath.Split.Append
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Comparison
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.QuerySource.Endpoints
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTracePath.Suffix
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Ordered actual trace pieces on one retained comparison cache

The original comparison cache already stores each actual View. A finite
spine reads those Views and retains their exact source/moving/retention
pieces. Its stationary-expanded vertices and moving centered-child word
are related internally; root comparisons still use the SAME Alignment.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Comparison.Cache

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
  (CenterStates centeredEdges edgeOfStep edgeOfStep_point_one)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath (Suffix)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

attribute [local irreducible] CertifiedSquareRoot.rawRoot

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {first last : Endpoint} {budget : PreparedTraceBudget segment first last} {sheet : Fin 2}
    {referenceSource : Canonical} {referenceOwner : Owner referenceSource}
    {second : FixedRootBoxBudget.Budget referenceOwner}
    {movement : ∀ time : Rational, Inside time →
      Norm.Basic.normSq (referenceSource - curve.polynomial.eval (segment.pointAt time)) ≤ second.movement}

/-- The actual three-link pieces at every original accepted request, with their whole same-View factories.

The finite representation follows the SAME original subdivision and
comparison-cache tail. A stop retains no fabricated child or link.
-/
@[expose] def Incidence : ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits},
    Cache curve differential budget sheet second movement subdivision fits trace → Type
  | _, _, .stop _ _, _, _, _ => PUnit
  | _, _, .next _ _ _ _ _ _ _, _, _, retained =>
      {value : retained.1.Pieces // value = retained.1.pieces} × Incidence retained.2.2.2
termination_by structural _ _ subdivision _ _ _ => subdivision

namespace Incidence

/-- Read each GIVEN cache View once and retain its actual pieces without rebuilding a View, RootPath or reference. -/
def build {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace) : Incidence retained :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      (retained : Cache curve differential budget sheet second movement subdivision fits trace) → Incidence retained)
    subdivision
    (fun _ _ _ _ _ => PUnit.unit)
    (fun _current _inherited _request _cached _ordered _small _remaining _fits _trace retained =>
      let head := retained.1.pieces
      let tail := build retained.2.2.2
      ⟨⟨head, rfl⟩, tail⟩)
    fits trace retained
termination_by structural subdivision

/-- Locate all three actual constructor boundaries at one literal accepted-request occurrence.

The finite index follows the SAME retained cache tail. Each successor
transports through the whole original tailTrace suffix equality, then
prepends the already stored prefix. No headLink, View, query, reference or
continuation is reconstructed by this operation.
-/
def splitsAt {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (kept : Incidence retained) (index : Fin subdivision.stepCount) :
    OwnerPath.Split trace.path × OwnerPath.Split trace.path × OwnerPath.Split trace.path :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      (retained : Cache curve differential budget sheet second movement subdivision fits trace) →
      (kept : Incidence retained) → (index : Fin subdivision.stepCount) →
      OwnerPath.Split trace.path × OwnerPath.Split trace.path × OwnerPath.Split trace.path)
    subdivision
    (fun _ _ _ _ _ _ index => Fin.elim0 index)
    (fun _current _inherited _request _cached _ordered _small _remaining _fits trace retained kept index =>
      Fin.cases
        (motive := fun _ => OwnerPath.Split trace.path × OwnerPath.Split trace.path × OwnerPath.Split trace.path)
        ⟨kept.1.val.sourceSplit, kept.1.val.movingSplit, kept.1.val.retainedSplit⟩
        (fun index =>
          let divided := splitsAt retained.2.2.2 kept.2 index
          let first := OwnerPath.Split.castSuffix retained.1.tailTrace_suffix_eq divided.1
          let moving := OwnerPath.Split.castSuffix retained.1.tailTrace_suffix_eq divided.2.1
          let last := OwnerPath.Split.castSuffix retained.1.tailTrace_suffix_eq divided.2.2
          ⟨OwnerPath.Split.castPath kept.1.val.rejoin.symm
              (OwnerPath.Split.prependPath kept.1.val.front retained.1.tail.path first),
            OwnerPath.Split.castPath kept.1.val.rejoin.symm
              (OwnerPath.Split.prependPath kept.1.val.front retained.1.tail.path moving),
            OwnerPath.Split.castPath kept.1.val.rejoin.symm
              (OwnerPath.Split.prependPath kept.1.val.front retained.1.tail.path last)⟩) index)
    fits trace retained kept index
termination_by structural subdivision

/-- Read every retained source/moving/retention vertex in its actual original order. -/
def vertices : ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace),
    Incidence retained → List Canonical
  | _, _, .stop _ _, _, _, _, _ => []
  | _, _, .next _ _ _ _ _ _ _, _, _, retained, kept =>
      kept.1.val.front.vertices ++ vertices retained.2.2.2 kept.2
termination_by structural _ _ subdivision _ _ _ _ => subdivision

/-- Read the actual moving endpoint at every original accepted request, retaining its occurrence separately. -/
def movingVertices : ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace),
    Incidence retained → List Canonical
  | _, _, .stop _ _, _, _, _, _ => []
  | _, _, .next _ _ _ _ _ _ _, _, _, retained, kept =>
      retained.1.moving.point :: movingVertices retained.2.2.2 kept.2
termination_by structural _ _ subdivision _ _ _ _ => subdivision

/-- The retained incidence pieces reassemble every actual original trace vertex, including both stationary pieces. -/
theorem vertices_eq {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (kept : Incidence retained) : trace.path.vertices = vertices retained kept :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      (retained : Cache curve differential budget sheet second movement subdivision fits trace) →
      (kept : Incidence retained) → trace.path.vertices = vertices retained kept)
    subdivision
    (fun _ _ _ trace _ _ => by
      have original := congrArg OwnerPath.vertices trace.path_eq
      change trace.path.vertices = [] at original
      exact original)
    (fun _current _inherited _request _cached _ordered _small _remaining _fits _trace retained kept => by
      have joined := congrArg OwnerPath.vertices kept.1.val.rejoin
      have append := OwnerPath.append_vertices kept.1.val.front retained.1.tail.path
      have casted := congrArg (fun suffix : Suffix _remaining.terminalOwner => suffix.path.vertices)
        retained.1.tailTrace_suffix_eq
      have rest := vertices_eq retained.2.2.2 kept.2
      change _ = kept.1.val.front.vertices ++ _
      exact joined.trans (append.trans
        (congrArg (List.append kept.1.val.front.vertices) (casted.symm.trans rest))))
    fits trace retained kept
termination_by structural subdivision

/-- Erasing only the recorded stationary positions leaves the SAME actual request endpoint word. -/
theorem moving_requests {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (kept : Incidence retained) : movingVertices retained kept =
      subdivision.requests.map (fun request => segment.pointAt request.endpoint.parameter) :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      (retained : Cache curve differential budget sheet second movement subdivision fits trace) →
      (kept : Incidence retained) → movingVertices retained kept =
        subdivision.requests.map (fun request => segment.pointAt request.endpoint.parameter))
    subdivision
    (fun _ _ _ _ _ _ => rfl)
    (fun _current _inherited _request _cached _ordered _small _remaining _fits _trace retained kept => by
      change retained.1.moving.point :: _ = _ :: _
      exact congrArg₂ List.cons retained.1.moving_point (moving_requests retained.2.2.2 kept.2))
    fits trace retained kept
termination_by structural subdivision

/-- The actual moving word is exactly the SAME centered-child endpoint word, with its original center family.

Only the two recorded stationary positions are omitted. The retained
source and retention links and both signed comparisons remain in Incidence;
this geometric readback cancels no primitive normalization or offset.
-/
theorem moving_parents {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (kept : Incidence retained) (centers : CenterStates curve differential sheet subdivision) :
    movingVertices retained kept =
      (centeredEdges curve differential sheet subdivision centers).map (fun child => child.edge.point 1) :=
  Subdivision.casesOn
    (motive := fun current _ subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      (retained : Cache curve differential budget sheet second movement subdivision fits trace) →
      (kept : Incidence retained) → (centers : CenterStates curve differential sheet subdivision) →
      movingVertices retained kept =
        (centeredEdges curve differential sheet subdivision centers).map (fun child => child.edge.point 1))
    subdivision
    (fun _ _ _ _ _ _ _ => rfl)
    (fun current inherited request cached ordered small remaining _fits _trace retained kept centers => by
      have endpoint := edgeOfStep_point_one curve differential segment within current inherited request
        cached ordered small sheet
      change retained.1.moving.point :: _ = _ :: _
      exact congrArg₂ List.cons (retained.1.moving_point.trans endpoint.symm)
        (moving_parents retained.2.2.2 kept.2 centers.2))
    fits trace retained kept centers
termination_by structural subdivision

end Incidence

end Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Comparison.Cache

end
