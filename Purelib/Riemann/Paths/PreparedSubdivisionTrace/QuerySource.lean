module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.RootPath
import Purelib.Riemann.Integration.PreparedConstantModels.Endpoints
public import Purelib.Riemann.Readings.UniformPreparedRequests.Query
import Purelib.Riemann.Paths.OwnerTracePath.StationaryHead

/-! # Actual query and primitive-sample incidence at a stored source reset

The complete original Trace.View supplies the literal source-stationary
link. Its realized signed comparison composes with the same retained query
and local primitive sample. The inherited trace Owner is never replaced.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace

namespace PreparedTraceBudget.Trace.View

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision CachedSource StepRequest Endpoint)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge edgeOfStep)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {first last current : Endpoint} {budget : PreparedTraceBudget segment first last}
variable {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
variable {request : StepRequest} {cached : CachedSource segment current inherited request}
variable {ordered : current.parameter ≤ request.endpoint.parameter}
variable {small : ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter <
  (PreparedSheetContinuation.prepared segment current inherited request).track.initial.clearance.bound}
variable {remaining : Subdivision segment within request.endpoint
  (PreparedSheetContinuation.advance segment within current inherited request small)}
variable {fits : budget.RequestsFit current
  (Subdivision.next current inherited request cached ordered small remaining).requests}
variable {trace : Trace budget (Subdivision.next current inherited request cached ordered small remaining) fits}
variable (view : View budget current inherited request cached ordered small remaining fits trace)

/-- Compare the exact cached zero channel with the literal inherited Owner through its SAME stored source link.

The original zero-name law identifies the existing evaluator channel with
its cached prepared Owner. The retained stationary link supplies the
signed source handoff. No query, initial-box uniqueness refinement or new
comparison Owner is constructed by this exact endpoint operation.
-/
def sourceEquivalent (sheet : Fin 2) :
    NamedEquivalent
      ((edgeOfStep curve differential segment within current inherited request cached ordered small sheet).rootName
        0
        (edgeOfStep curve differential segment within current inherited request cached ordered small sheet).baseInside)
      (ownerName inherited) := by
  let edge := edgeOfStep curve differential segment within current inherited request cached ordered small sheet
  have zeroName : edge.rootName 0 edge.baseInside = ownerName cached.preparedOwner :=
    edge.rootName_zero_eq_cached
  let canonical := NamedEquivalent.transport rfl zeroName
    (NamedEquivalent.refl (edge.rootName 0 edge.baseInside))
  let stationary := trace.path.stationaryHeadEquivalent view.source view.1.property view.source_point
  let sourceToPrepared := NamedEquivalent.transport rfl view.source_name_eq stationary
  exact canonical.trans sourceToPrepared.symm

variable {sheet : Fin 2}

/-- Derive actual trace-Owner to actual primitive-Point agreement with both retained observations unchanged.

The center belongs to the same original prepared edge. The LocalRequest
and Point retain their original neighborhood and request indices; the
same Query is consumed by both comparisons and is never acquired again.
-/
def sampleEquivalent
    (center : PreparedEdge.CenterState
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet))
    {count : Nat} {target : Rational}
    (localRequest : LocalRequest
      (⟨edgeOfStep curve differential segment within current inherited request cached ordered small sheet, center⟩ :
        CenteredEdge curve differential) count target)
    (query : PreparedEdge.Query
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet)
      0
        (edgeOfStep curve differential segment within current inherited request cached ordered small sheet).baseInside)
    (inside : localRequest.neighborhood.box.Contains (segment.pointAt current.parameter))
    (sample : ContinuedNeighborhood.Point localRequest.neighborhood (segment.pointAt current.parameter)) :
    NamedEquivalent (ownerName inherited) sample.certificate.value.name :=
  (view.sourceEquivalent sheet).symm.trans
    (localRequest.retainedQueryEquivalent 0
      (edgeOfStep curve differential segment within current inherited request cached ordered small sheet).baseInside
      query (PreparedEdge.point_zero _) inside sample)

end PreparedTraceBudget.Trace.View

end Purelib.Riemann.Paths.PreparedSubdivisionTrace

end
