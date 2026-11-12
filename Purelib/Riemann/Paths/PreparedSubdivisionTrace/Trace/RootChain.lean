module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.RootPath
public import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Paths.OwnerTracePath.StationaryHead
import Purelib.Riemann.Integration.PreparedConstantModels.Endpoints
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Signed root chains read from the same materialized original subdivision trace

Each accepted request reads its three actual suffixes once. The source and
retention links carry their own original realization certificates; exact
cached query endpoint laws attach the original centered parents. No source
preparation, moving transport, reserve reset, independent reference Owner,
second budget, center selection or observation is reconstructed.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates CenteredEdge centeredEdges edgeOfStep)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {first last : Endpoint} {budget : PreparedTraceBudget segment first last} {sheet : Fin 2}

attribute [local irreducible] CertifiedSquareRoot.rawRoot

/-- Read the signed chain of the SAME original subdivision and centers from its actual materialized Trace.

Only suffix extraction and original realization comparisons are performed.
Every following step receives the exact retained view.tailTrace. The
complete original trace-factory identity supplies all source/moving/tail
owner readbacks; no independent movement premise is needed.
-/
def rootChain {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests}
    (trace : Trace budget subdivision fits)
    (centers : CenterStates curve differential sheet subdivision) :
    RootChain (centeredEdges curve differential sheet subdivision centers)
      (ownerRootName inherited.parameterNonzero inherited)
      (ownerRootName subdivision.terminalOwner.parameterNonzero subdivision.terminalOwner) :=
  Subdivision.casesOn
    (motive := fun current inherited subdivision =>
      (fits : budget.RequestsFit current subdivision.requests) →
      (trace : Trace budget subdivision fits) →
      (centers : CenterStates curve differential sheet subdivision) →
      RootChain (centeredEdges curve differential sheet subdivision centers)
        (ownerRootName inherited.parameterNonzero inherited)
        (ownerRootName subdivision.terminalOwner.parameterNonzero subdivision.terminalOwner))
    subdivision
    (fun _ owner _ _ _ => .nil (NamedEquivalent.refl (ownerRootName owner.parameterNonzero owner)))
    (fun current inherited request cached ordered small remaining fits trace centers =>
      let view := View.build trace
      let edge := edgeOfStep curve differential segment within current inherited request cached ordered small sheet
      let child : CenteredEdge curve differential := ⟨edge, centers.1⟩
      let originalSource := trace.path.stationaryHeadEquivalent view.source view.1.property view.source_point
      let source : NamedEquivalent (ownerRootName inherited.parameterNonzero inherited)
          (ownerRootName cached.preparedOwner.parameterNonzero cached.preparedOwner) :=
        NamedEquivalent.transport rfl view.source_name_eq originalSource
      let entry : NamedEquivalent (ownerRootName inherited.parameterNonzero inherited)
          (edge.rootName 0 edge.baseInside) :=
        NamedEquivalent.transport rfl edge.rootName_zero_eq_cached.symm source
      let originalRetention := view.moving.path.stationaryHeadEquivalent view.tail view.2.2.property
        (view.tail_point.trans view.moving_point.symm)
      let movingName : ownerRootName view.movingOwner.parameterNonzero view.movingOwner =
          ownerRootName view.moving.owner.parameterNonzero view.moving.owner :=
        PreparedBankRootChains.ownerName_eq_of_heq
          (congrArg curve.polynomial.eval view.moving_point).symm view.movingOwner_heq
      let storedName := congrArg (fun owner => ownerRootName owner.parameterNonzero owner) remaining.sourceOwner_eq
      let retention : NamedEquivalent (ownerRootName view.movingOwner.parameterNonzero view.movingOwner)
          (ownerRootName remaining.sourceOwner.parameterNonzero remaining.sourceOwner) :=
        NamedEquivalent.transport movingName.symm view.tail_name_eq originalRetention
      let movingQuery : edge.rootName 1 (by decide) =
          ownerRootName view.movingOwner.parameterNonzero view.movingOwner :=
        edge.rootName_one_eq_transported.trans
          (congrArg (fun owner => ownerRootName owner.parameterNonzero owner) view.movingOwner_eq).symm
      let seam := NamedEquivalent.transport movingQuery.symm storedName retention
      let tail := rootChain view.tailTrace centers.2
      .cons child entry (tail.changeStart seam))
    fits trace centers
termination_by structural subdivision

end Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Trace

end
