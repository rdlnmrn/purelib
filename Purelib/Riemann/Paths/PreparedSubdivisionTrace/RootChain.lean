module

public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Comparison
public import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Paths.OwnerTracePath.StationaryHead
import Purelib.Riemann.Integration.PreparedConstantModels.Endpoints
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Root chains of the same retained subdivision comparison cache

The supplied comparison cache already contains one actual View and RootPath
per accepted request. This fold reads those same views and the supplied
center family. The stationary head and retention links derive signed root
agreement from their own realization certificates; exact evaluator endpoint
readbacks identify the intervening cached queries. No source preparation,
query transport, reserve reset, center or comparison cache is reconstructed.
-/

public section

namespace Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Comparison.Cache

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates CenteredEdge centeredEdges edgeOfStep)
open Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {first last : Endpoint} {budget : PreparedTraceBudget segment first last} {sheet : Fin 2}
    {referenceSource : Canonical} {referenceOwner : Owner referenceSource}
    {second : FixedRootBoxBudget.Budget referenceOwner}
    {movement : ∀ time : Rational, Inside time →
      Norm.Basic.normSq (referenceSource - curve.polynomial.eval (segment.pointAt time)) ≤ second.movement}

attribute [local irreducible] CertifiedSquareRoot.rawRoot

/-- Read the existing actual trace views from the original comparison cache.

Every complete View is retained literally, including its three actual
suffixes and their defining Option equations. The independent RootPath
and Reference caches remain with the original input; no View is rebuilt.
-/
def views : ∀ {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits},
    Cache curve differential budget sheet second movement subdivision fits trace → Trace.Views subdivision fits trace
  | _, _, .stop _ _, _, _, _ => PUnit.unit
  | _, _, .next _ _ _ _ _ _ _, _, _, retained =>
      ⟨retained.1, views retained.2.2.2⟩
termination_by structural _ _ subdivision _ _ _ => subdivision

/-- Retain the exact original budget, complete materialized trace and literal cached suffix Views.

The existing comparison cache remains an input with all its independent
Owners and paths intact. This exact view supplies the original root-chain
operation without constructing another comparison or suffix cache.
-/
def rootViews {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace) :
    Trace.RootViews subdivision := ⟨first, last, budget, ⟨fits⟩, trace, retained.views⟩

/-- The supplied original comparison cache contributes its whole literal trace-view spine. -/
theorem rootViews_views {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace) :
    HEq retained.rootViews.2.2.2.2.2 retained.views := by
  unfold rootViews
  rfl

/-- Construct the original cached root chain through the same retained actual trace views and supplied centers.

The original general subdivision operation consumes the literal original
budget, Trace and Views. Its supplied-cache branch derives both stationary
joins from those actual suffixes; no original preparation or advance is
repeated to manufacture an endpoint Owner.
-/
def rootChain {current : Endpoint}
    {inherited : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current inherited}
    {fits : budget.RequestsFit current subdivision.requests} {trace : Trace budget subdivision fits}
    (retained : Cache curve differential budget sheet second movement subdivision fits trace)
    (centers : CenterStates curve differential sheet subdivision) :
    RootChain (centeredEdges curve differential sheet subdivision centers)
      (ownerRootName inherited.parameterNonzero inherited)
      (ownerRootName subdivision.terminalOwner.parameterNonzero subdivision.terminalOwner) :=
  PreparedBankRootChains.subdivisionRootChain curve differential segment within sheet subdivision centers
    (some retained.rootViews)

end Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget.Comparison.Cache

end
