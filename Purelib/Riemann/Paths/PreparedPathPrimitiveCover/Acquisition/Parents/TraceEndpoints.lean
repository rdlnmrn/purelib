module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.RootPath
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Endpoints
import Purelib.Data.List.Membership

/-! # Direct endpoint incidence on the original paid Segment and its retained Parents

The SAME whole materialized path is reindexed by its original rootTrace
operation. Original parent/center equations transport only child bounds
and complete parent indices. No RootComparisons or fixed-box movement
certificate is needed to read the literal endpoint occurrences.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

namespace Acquisition.Segment.Parents

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge centeredEdges centeredEdges_length)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
variable {retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request}
variable {sheet : Fin 2} {count : Nat}
variable (parents : Parents differential sheet count retained)

/-- Read the same original child as a centered-family index, transporting only its exact original bound. -/
@[expose] def centeredIndex (index : Fin parents.covered.parents.length) :
    Fin (centeredEdges curve differential sheet retained.traced.prepared.subdivision parents.centers).length :=
  ⟨index.val, Eq.mp (congrArg
    (fun word : List (CenteredEdge curve differential) => index.val < word.length) parents.parents_eq) index.isLt⟩

/-- The centered index retains the literal original physical child coordinate. -/
theorem centeredIndex_val (index : Fin parents.covered.parents.length) :
    (parents.centeredIndex index).val = index.val := by
  rfl

/-- Read that SAME child in the original accepted request list, retaining its actual raw occurrence coordinate. -/
@[expose] def requestIndex (index : Fin parents.covered.parents.length) :
    Fin retained.traced.prepared.subdivision.requests.length :=
  let raw := Trace.rawIndex retained.traced.prepared.subdivision parents.centers (parents.centeredIndex index)
  ⟨raw.val, Eq.mpr (congrArg (fun size : Nat => raw.val < size)
    retained.traced.prepared.subdivision.requests_length) raw.isLt⟩

/-- The original request and centered indices keep exactly the SAME physical occurrence coordinate. -/
theorem requestIndex_val (index : Fin parents.covered.parents.length) :
    (parents.requestIndex index).val = index.val := by
  rfl

/-- Locate endpoint comparisons directly on this SAME actual paid trace with its original whole factory equation.

rootTrace only reverses original endpoint/finish-Owner reindices on the
supplied path. One direct finite lookup consumes its actual selected View;
parent equality transports only the complete centered-child interface.
-/
def traceEndpointComparisons
    (actual : OwnerPath curve.polynomial start sourceOwner finish retained.traced.finishOwner)
    (actual_eq : actual = retained.traced.trace.get) (index : Fin parents.covered.parents.length) :
    Trace.EndpointComparisons (parents.covered.parents[index.val]'index.isLt) :=
  let selected := Trace.endpointsAt (retained.rootTrace actual actual_eq) parents.centers
    (parents.centeredIndex index)
  have same := getElem_congr parents.parents_eq
    (i := index.val) (j := (parents.centeredIndex index).val) rfl index.isLt
  Eq.mp (congrArg (fun parent : CenteredEdge curve differential => Trace.EndpointComparisons parent) same.symm) selected

end Acquisition.Segment.Parents

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

end
