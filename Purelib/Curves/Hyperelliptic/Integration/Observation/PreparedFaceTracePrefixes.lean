module
import Purelib.Data.Int.Arithmetic
import Purelib.Data.List.Membership
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Polynomial.Winding.Polygon.Stationary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Paths.PreparedSubdivisionTrace
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Paths.PreparedQueryTraceEdges
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Actual prepared-edge prefixes inside a clear face

The retained segment budgets realize each accepted step, including both
stationary preparation handoffs. Finite induction reaches the actual owner
of every centered parent, with its winding determined by the face potential.
All auxiliary prefixes below occur only in propositions: querying the
integration bank does not execute a second preparation or build a quadratic
list of prefix traces.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Dense.Gaussian.Path

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Polynomial.Winding

open Purelib.Polynomial.Winding.Polygon

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPathWinding

open Purelib.Riemann.Paths.OwnerTracePath

open Purelib.Riemann.Paths.PreparedPathTrace

open Purelib.Riemann.Paths.PreparedPathWinding

open Purelib.Riemann.Paths.PreparedQueryTraceEdges

open Purelib.Riemann.Paths.PreparedSubdivisionTrace

open Purelib.Riemann.Topology

open Purelib.RootIsolation.SquareRoot.Owner

open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision)
open Purelib.Riemann.Paths.PreparedClearPathModels (CompleteSegment PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge CenterStates centeredEdges)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths.ClearBoxPathWinding.ClearBoxPaths (windingPotential segment_winding)
open _root_.Purelib.Polynomial.Geometry.ClearPath (InBox)

/-- A realized prefix reaches this actual owner with the clear-face winding difference.

The existential retains a trace from the supplied source owner to the actual terminal owner. Its winding is the
difference of the two endpoint potentials in the same retained face box. -/
@[expose] def Reached {polynomial : ClearPath.GaussianPolynomial} (box : Rational.Box) {start finish :
  Data.Gaussian.Basic.Canonical}
    (first : SquareRootContinuationChain.Owner (polynomial.eval start)) (last : SquareRootContinuationChain.Owner
      (polynomial.eval finish)) : Prop :=
  ∃ trace : OwnerTracePath.OwnerPath polynomial start first finish last,
    Polygon.Basic.chainRaw polynomial start trace.vertices =
      ClearBoxPaths.windingPotential polynomial box finish - ClearBoxPaths.windingPotential polynomial box start

namespace Reached

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {box :
  Purelib.Geometry.Rational.Box}

/-- The empty owner trace reaches the original owner with zero face-potential difference.

Both endpoints retain the same supplied owner and point. Their identical face-potential values have zero integer
difference, matching the winding of the empty trace. -/
theorem refl {point : Data.Gaussian.Basic.Canonical} (owner : SquareRootContinuationChain.Owner (polynomial.eval point))
  : PreparedFaceTracePrefixes.Reached box owner owner :=
  ⟨.nil point owner, (Data.Int.Arithmetic.sub_eq_zero_of_eq rfl).symm⟩

/-- Concatenate retained owner traces and add their face-potential winding differences. -/
theorem append {start middle finish : Data.Gaussian.Basic.Canonical} {first : SquareRootContinuationChain.Owner
  (polynomial.eval start)}
    {center : SquareRootContinuationChain.Owner (polynomial.eval middle)} {last : SquareRootContinuationChain.Owner
      (polynomial.eval finish)}
    (left : PreparedFaceTracePrefixes.Reached box first center) (right : PreparedFaceTracePrefixes.Reached box center
      last) : PreparedFaceTracePrefixes.Reached box first last := by
  obtain ⟨leftTrace, leftWinding⟩ := left
  obtain ⟨rightTrace, rightWinding⟩ := right
  refine ⟨leftTrace.append rightTrace, ?_⟩
  rw [OwnerPath.append_vertices,
    Polygon.Basic.chainRaw_append,
    leftTrace.vertices_terminal, leftWinding, rightWinding]
  omega

/-- Transport reachability along an exact endpoint equality and the corresponding retained owner equality. -/
theorem castFinish {start finish nextFinish : Data.Gaussian.Basic.Canonical} {first : SquareRootContinuationChain.Owner
  (polynomial.eval start)}
    {last : SquareRootContinuationChain.Owner (polynomial.eval finish)} {next : SquareRootContinuationChain.Owner
      (polynomial.eval nextFinish)}
    (equal : finish = nextFinish) (same : HEq last next) (reached : PreparedFaceTracePrefixes.Reached box first last) :
    PreparedFaceTracePrefixes.Reached box first next := by
  cases equal
  cases eq_of_heq same
  exact reached

end Reached

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {box : Purelib.Geometry.Rational.Box} {base : Purelib.Data.Gaussian.Basic.Canonical} {source :
    Owner (curve.polynomial.eval base)}

/-- Both endpoints and the inherited source owner belong to the actual centered parent.

The certificate retains geometric containment, reachability of the original parent owner and reachability of each
bounded direct-query owner. Its conditions refer to the supplied parent and source, independently of the displayed sheet
label. -/
structure ParentReached (box : Rational.Box) {base : Data.Gaussian.Basic.Canonical} (source :
  SquareRootContinuationChain.Owner (curve.polynomial.eval base))
    (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) : Prop where
  /-- The original parent starting point lies in the retained clear face box. -/ first_inside : box.Contains
    (parent.edge.point 0)
  /-- The original parent finishing point lies in the retained clear face box. -/ last_inside : box.Contains
    (parent.edge.point 1)
  /-- The actual inherited parent owner is reached from the original source with the required face winding. -/
    owner_reached : PreparedFaceTracePrefixes.Reached box source parent.edge.owner
  /-- Every bounded direct parent query reaches its actual query owner with the same face-potential rule. -/
    query_reached : ∀ fraction (inside : 0 ≤ fraction ∧ fraction ≤ 1),
    PreparedFaceTracePrefixes.Reached box source (parent.edge.directQueryOwner fraction inside)

/-- Every retained bounded segment parameter stays in the box containing its original endpoints. -/
private theorem point_inside {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (first : box.Contains start) (last : box.Contains finish) (endpoint : PreparedSheetContinuation.Endpoint) :
    box.Contains (segment.pointAt endpoint.parameter) := by
  rw [ClearSegment.pointAt_eq_line]
  exact Rational.Box.contains_line first last endpoint.inside

/-- A direct prepared query fits the retained trace budget and reaches its actual owner.

The original source trace is extended by the budget-certified query path; clear-face winding computes its exact
potential difference. -/
private theorem query_reached_of_budget (clearance : Region.RegionClearance curve.polynomial box)
    (parent : PreparedConstantModels.PreparedEdge curve differential) {left right : PreparedSheetContinuation.Endpoint}
    (budget : Riemann.Paths.PreparedTraceBudget parent.segment left right)
    (diameterSmall : parent.request.rootDiameter ≤ budget.rootDiameter)
    (movementSmall : ClearSheetContinuation.variationBound parent.segment
      parent.left.parameter parent.request.endpoint.parameter ≤ budget.movementBudget)
    (firstInside : box.Contains parent.start) (lastInside : box.Contains parent.finish)
    (reached : PreparedFaceTracePrefixes.Reached box source parent.owner) (fraction : Fraction.Rational) (inside : 0 ≤
      fraction ∧ fraction ≤ 1) :
    PreparedFaceTracePrefixes.Reached box source (parent.directQueryOwner fraction inside) := by
  apply reached.append
  refine ⟨PreparedTraceBudget.queryPath
    budget diameterSmall movementSmall fraction inside, ?_⟩
  rw [PreparedTraceBudget.queryPath_vertices,
    Stationary.chainRaw_cons_self curve.polynomial _
    (parent.segment.pointAt_eval_ne_zero parent.left.parameter parent.left.inside)]
  change (Segment.segment curve.polynomial (parent.segment.pointAt parent.left.parameter)
    (parent.segment.pointAt (PreparedSheetContinuation.parameterAt parent.left parent.request fraction))).doubledWinding
      + 0 = _
  rw [Int.add_zero]
  let query : Endpoint := ⟨PreparedSheetContinuation.parameterAt parent.left parent.request fraction,
    PreparedSheetContinuation.parameterAt_inside parent.left parent.request parent.ordered fraction inside⟩
  exact ClearBoxPaths.segment_winding clearance (BranchIsolation.degreePositive curve)
    (parent.segment.restrict parent.within parent.left.parameter query.parameter parent.left.inside query.inside)
    (point_inside parent.segment firstInside lastInside parent.left)
    (point_inside parent.segment firstInside lastInside query)

/-- Every retained subdivision step reaches its actual parent owner and terminal handoff.

The original fitted budgets extend the retained prefix at each step, including stationary accepted requests. Structural
list membership identifies that step or the unchanged tail while preserving the supplied center states and actual query
owners. -/
theorem subdivision_reached (clearance : Region.RegionClearance curve.polynomial box)
    (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish) (within : segment.WithinAmbient)
    (firstInside : box.Contains start) (lastInside : box.Contains finish) (sheet : Fin 2)
    {budgetLeft budgetRight : PreparedSheetContinuation.Endpoint} (budget : Riemann.Paths.PreparedTraceBudget
      segment budgetLeft budgetRight) :
    ∀ {left : PreparedSheetContinuation.Endpoint} {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval
      (segment.pointAt left.parameter))}
      (subdivision : PreparedSheetContinuation.Subdivision segment within left owner)
      (centers : PreparedSubdivisionModelCore.CenterStates curve differential sheet subdivision),
      budget.RequestsFit left subdivision.requests → PreparedFaceTracePrefixes.Reached box source owner →
        (∀ parent ∈ PreparedSubdivisionModelCore.centeredEdges curve differential sheet subdivision centers,
          PreparedFaceTracePrefixes.ParentReached box source parent) ∧
          PreparedFaceTracePrefixes.Reached box source subdivision.terminalOwner
  | _, _, .stop _ _, _, _, reached => ⟨(by intro parent membership; cases membership), reached⟩
  | left, owner, .next _ _ request cached ordered safe remaining, centers, fits, reached => by
      let step : PreparedSheetContinuation.Subdivision segment within left owner :=
        .next left owner request cached ordered safe (.stop request.endpoint _)
      have stepFit : budget.RequestsFit left step.requests := ⟨fits.1, fits.2.1, trivial⟩
      have next : PreparedFaceTracePrefixes.Reached box owner (PreparedSheetContinuation.advance segment within left
        owner request safe) := by
        refine ⟨PreparedTraceBudget.ownerPath budget step stepFit,
          (PreparedTraceBudget.ownerPath_chainRaw
            budget step stepFit).trans ?_⟩
        change (Segment.segment curve.polynomial (segment.pointAt left.parameter)
          (segment.pointAt request.endpoint.parameter)).doubledWinding + 0 = _
        rw [Int.add_zero]
        exact ClearBoxPaths.segment_winding clearance (BranchIsolation.degreePositive curve)
          (segment.restrict within left.parameter request.endpoint.parameter left.inside request.endpoint.inside)
          (point_inside segment firstInside lastInside left)
          (point_inside segment firstInside lastInside request.endpoint)
      have rest := subdivision_reached
        clearance differential segment within firstInside lastInside sheet
        budget remaining centers.2 fits.2.2 (reached.append next)
      refine ⟨?_, rest.2⟩
      intro parent membership
      dsimp only [PreparedSubdivisionModelCore.centeredEdges] at membership
      rcases Data.List.Membership.mem_cons.mp membership with equal | membership
      · subst parent
        refine ⟨?_, ?_, reached, ?_⟩
        · rw [PreparedConstantModels.PreparedEdge.point_zero]
          exact point_inside segment firstInside lastInside left
        · rw [PreparedConstantModels.PreparedEdge.point_one]
          exact point_inside segment firstInside lastInside request.endpoint
        · exact query_reached_of_budget clearance _ budget fits.1 fits.2.1 firstInside lastInside reached
      · exact rest.1 parent membership

/-- Endpoint equality transports preserve the actual complete-segment owners, not merely operationally equivalent
replacements. -/
theorem completeSegment_reached (clearance : Region.RegionClearance curve.polynomial box)
    (differential : Differentials.Basic.Differential genus) (sheet : Fin 2) {ambient : Rational.Box}
      {start finish : Data.Gaussian.Basic.Canonical}
    {segment : ClearPath.ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} (prepared :
      PreparedClearPathModels.CompleteSegment segment within owner)
    (budget : Riemann.Paths.PreparedTraceBudget segment PreparedClearPathModels.zeroEndpoint
      PreparedClearPathModels.oneEndpoint)
    (fits : budget.RequestsFit PreparedClearPathModels.zeroEndpoint prepared.subdivision.requests)
    (firstInside : box.Contains start) (lastInside : box.Contains finish) (reached : PreparedFaceTracePrefixes.Reached
      box source owner) :
    (∀ parent ∈ prepared.centeredEdges curve differential sheet, PreparedFaceTracePrefixes.ParentReached box source
      parent) ∧
      PreparedFaceTracePrefixes.Reached box source prepared.finishOwner := by
  have initial : PreparedFaceTracePrefixes.Reached box source (PreparedClearPathModels.ownerAtStart segment owner) :=
    reached.castFinish segment.pointAt_zero.symm (by
      unfold PreparedClearPathModels.ownerAtStart
      exact (Transport.castOwnerParameter_heq _ _).symm)
  have result := subdivision_reached clearance
    differential segment within firstInside lastInside sheet budget
    prepared.subdivision (PreparedSubdivisionAutomaticModels.canonicalCenterStates
      curve differential sheet prepared.subdivision) fits initial
  exact ⟨result.1, result.2.castFinish prepared.finish_eq prepared.finishOwner_heq_terminalOwner.symm⟩

/-- A proof-only owner transport leaves the actual centered parent list unchanged, without unfolding complete-segment
terminal acquisition. -/
private theorem parents_castOwner (differential : Differentials.Basic.Differential genus) (sheet : Fin 2)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
      curve.polynomial ambient start finish}
    {first second : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} (equal : first = second) (prepared
      : PreparedClearPathModels.PreparedPath path first) :
    (CenteredPathChain.ofPreparedPath curve differential sheet
      (PreparedPath.castOwner equal prepared)).parents =
      (CenteredPathChain.ofPreparedPath curve differential sheet prepared).parents := by
  cases equal
  rfl

/-- The cached trace lineage reaches every actual centered parent and final owner.

Each complete segment retains its original budget and owner handoff. Append membership follows the same parent
occurrence; exact owner transports occur only in the proof and do not rebuild the prepared path. -/
theorem lineage_reached (clearance : Region.RegionClearance curve.polynomial box)
    (differential : Differentials.Basic.Differential genus) (sheet : Fin 2) {ambient : Rational.Box} :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner},
      PreparedPath.TraceLineage prepared → ClearPath.InBox box path → PreparedFaceTracePrefixes.Reached box source owner
        →
        (∀ parent ∈ (CenteredPathChain.ofPreparedPath curve differential sheet prepared).parents,
          PreparedFaceTracePrefixes.ParentReached box source parent) ∧
          PreparedFaceTracePrefixes.Reached box source (PreparedPathGluing.finishOwner prepared)
  | _, _, _, _, _, .nil _ _, _, reached => ⟨(by intro parent membership; cases membership), reached⟩
  | _, _, _, _, _, .cons budget fits finishEq remaining, inside, reached => by
      have first := completeSegment_reached clearance differential sheet _ budget fits inside.1 inside.2.start reached
      have rest := lineage_reached
        clearance differential sheet remaining inside.2
        (first.2.castFinish rfl (heq_of_eq finishEq.symm))
      constructor
      · intro parent membership
        change parent ∈ (CenteredPathChain.dataOfCompleteSegment curve differential sheet _).parents ++ _ at membership
        rw [CenteredPathChain.dataOfCompleteSegment_parents, parents_castOwner] at membership
        rcases Data.List.Membership.mem_append.mp membership with membership | membership
        · exact first.1 parent membership
        · exact rest.1 parent membership
      · change PreparedFaceTracePrefixes.Reached box source (PreparedPathGluing.finishOwner
          (PreparedPath.castOwner finishEq _))
        rw [PreparedPath.castOwner_finishOwner]
        exact rest.2

/-- Every edge in the actual public traced preparation is reached from its supplied source owner. The producer supplies
the retained lineage. -/
theorem traced_parent_reached (clearance : Region.RegionClearance curve.polynomial box)
    (differential : Differentials.Basic.Differential genus) (sheet : Fin 2) {ambient : Rational.Box}
      {finish : Data.Gaussian.Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient base finish} (traced : PreparedPathTrace.TracedPath
      path
      source)
    (inside : ClearPath.InBox box path) (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential)
    (membership : parent ∈ (CenteredPathChain.ofPreparedPath curve differential sheet traced.prepared).parents) :
    PreparedFaceTracePrefixes.ParentReached box source parent :=
  (lineage_reached clearance differential sheet traced.lineage inside (PreparedFaceTracePrefixes.Reached.refl source)).1
    parent membership

end Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
