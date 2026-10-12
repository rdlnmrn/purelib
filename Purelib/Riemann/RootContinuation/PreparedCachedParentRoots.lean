module
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Paths.PreparedClearPathModels

public import Purelib.Riemann.Topology.PreparedBankRootChains
public import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-!
# Root chains consuming retained parent caches

The canonical extraction proves which owner each stored parent inherits.
That provenance is propositional and erased. Operational root joins are then
constructed by traversing the retained parents, without extracting their
canonical centers again.
-/

namespace Purelib.Riemann.RootContinuation.PreparedCachedParentRoots.PreparedRefinementRootEndpoints

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge CenterStates centeredEdges)
open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.Riemann.Paths.PreparedClearPathModels (CompleteSegment PreparedPath)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName queryEquivalentAdvance)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision advance)
open Purelib.Riemann.Paths.PreparedPathGluing (finishOwner)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- Exact successive root-owner names along the original centered parent list.

The empty chain identifies its endpoint names; each nonempty step keeps the parent's original initial owner and the
actual advanced owner passed to the retained tail. -/
def OwnerChain : List (CenteredEdge curve differential) → Named → Named → Prop
  | [], first, last => first = last
  | parent :: parents, first, last =>
      first = ownerName parent.edge.owner ∧
        OwnerChain parents (ownerName (advance parent.edge.segment parent.edge.within
          parent.edge.left parent.edge.owner parent.edge.request parent.edge.small)) last

namespace OwnerChain

/-- Transport an original owner chain along exact endpoint-name equalities. -/
theorem castNames {parents : List (CenteredEdge curve differential)} {first last left right : Named}
    (firstEq : first = left) (lastEq : last = right) (chain : OwnerChain parents first last) :
    OwnerChain parents left right := by
  cases firstEq
  cases lastEq
  exact chain

/-- Concatenate original owner chains sharing the same middle name. -/
theorem append : ∀ {firstParents secondParents : List (CenteredEdge curve differential)}
    {first middle last : Named}, OwnerChain firstParents first middle →
      OwnerChain secondParents middle last → OwnerChain (firstParents ++ secondParents) first last
  | [], _, _, _, _, equal, second => by
      change _ = _ at equal
      cases equal
      exact second
  | _ :: _, _, _, _, _, first, second =>
      ⟨first.1, append first.2 second⟩

open Purelib.Approximation.Gaussian in
/-- Convert the original exact owner chain into its retained root-equivalence chain. -/
def rootChain : ∀ (parents : List (CenteredEdge curve differential)) {first last : Named},
    OwnerChain parents first last → RootChain parents first last
  | [], _, _, equal => .nil (by
      change _ = _ at equal
      cases equal
      exact Equivalence.NamedEquivalent.refl _)
  | parent :: parents, _, _, chain =>
      .cons parent (by
        rw [chain.1]
        exact parent.edge.ownerRootEquivalent_baseQuery)
        ((rootChain parents chain.2).changeStart (queryEquivalentAdvance parent.edge))

end OwnerChain

open Purelib.Curves.Hyperelliptic in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- The original centered subdivision edges retain the initial and terminal root-owner names. -/
theorem subdivisionOwnerChain (curve : Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential
  genus)
    {ambient : Purelib.Geometry.Rational.Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2) :
    ∀ {left : Endpoint} {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
      (subdivision : Subdivision segment within left owner)
      (centers : CenterStates curve differential sheet subdivision),
      OwnerChain (centeredEdges curve differential sheet subdivision centers)
        (ownerName owner) (ownerName subdivision.terminalOwner)
  | _, _, .stop _ _, _ => rfl
  | _, _, .next _ _ _ _ _ _ remaining, centers =>
      ⟨rfl, subdivisionOwnerChain curve differential segment within sheet remaining centers.2⟩

/-- Heterogeneously equal original root owners have equal names after parameter transport. -/
private theorem ownerName_eq_of_heq {firstParameter secondParameter : Gaussian}
    (equal : firstParameter = secondParameter) {first : Owner firstParameter} {second : Owner secondParameter}
    (same : HEq first second) : ownerName first = ownerName second := by
  cases equal
  cases same
  rfl

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
open Purelib.RootIsolation in
/-- Transporting the original segment owner to its initial parameter preserves its name. -/
private theorem ownerAtStart_name {ambient : Purelib.Geometry.Rational.Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (owner : Owner (curve.polynomial.eval start)) :
    ownerName (PreparedClearPathModels.ownerAtStart segment owner) = ownerName owner := by
  apply ownerName_eq_of_heq (congrArg curve.polynomial.eval segment.pointAt_zero)
  unfold PreparedClearPathModels.ownerAtStart
  exact SquareRoot.Owner.Transport.castOwnerParameter_heq _ _

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- The complete segment's retained terminal owner and transported finish owner have the same name. -/
private theorem finishOwner_name {ambient : Purelib.Geometry.Rational.Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {owner : Owner (curve.polynomial.eval start)}
    (prepared : CompleteSegment segment within owner) :
    ownerName prepared.subdivision.terminalOwner = ownerName prepared.finishOwner :=
  ownerName_eq_of_heq (congrArg curve.polynomial.eval prepared.finish_eq)
    prepared.finishOwner_heq_terminalOwner.symm

open Purelib.Curves.Hyperelliptic
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Integration
/-- The original complete segment's centered edges retain its initial and final owner names. -/
theorem completeSegmentOwnerChain (curve : Basic.HyperellipticCurve genus) (differential :
  Differentials.Basic.Differential genus)
    {ambient : Purelib.Geometry.Rational.Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    OwnerChain (prepared.centeredEdges curve differential sheet) (ownerName owner) (ownerName prepared.finishOwner) :=
  (subdivisionOwnerChain curve differential segment within sheet prepared.subdivision
    (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve differential sheet prepared.subdivision)).castNames
      (ownerAtStart_name segment owner) (finishOwner_name prepared)

/-- The original prepared path's centered parents retain the exact start-to-finish owner chain. -/
theorem preparedPathOwnerChain (curve : Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential
  genus)
    (sheet : Fin 2) {ambient : Purelib.Geometry.Rational.Box} :
    ∀ {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)} (prepared : PreparedPath path owner),
      OwnerChain (PreparedDirectDyadicRefinements.CenteredPathChain.ofPreparedPath curve differential sheet
        prepared).parents
        (ownerName owner) (ownerName (finishOwner prepared))
  | _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, .cons _ _ _ _ head tail => by
      have first := completeSegmentOwnerChain curve differential sheet head
      rw [← PreparedDirectDyadicRefinements.CenteredPathChain.dataOfCompleteSegment_parents
        curve differential sheet head] at first
      exact first.append (preparedPathOwnerChain curve differential sheet tail)

end Purelib.Riemann.RootContinuation.PreparedCachedParentRoots.PreparedRefinementRootEndpoints

namespace Purelib.Riemann.RootContinuation.PreparedCachedParentRoots.ParentCache

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.RootContinuation.PreparedCachedParentRoots.PreparedRefinementRootEndpoints (OwnerChain)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathGluing (finishOwner)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {ambient :
  Purelib.Geometry.Rational.Box}
  {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
    finish}
  {owner : Owner (curve.polynomial.eval start)} {prepared : CoveredTracedPath path owner}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {sheet : Fin 2}

open Purelib.Riemann.RootContinuation
/-- Read the original owner-name chain through a retained parent cache's exact list identity. -/
theorem ownerChain (cache : ParentCache prepared differential sheet) :
    OwnerChain cache.parents (ownerName owner) (ownerName (finishOwner prepared.traced.prepared)) := by
  rw [cache.parents_eq]
  exact PreparedCachedParentRoots.PreparedRefinementRootEndpoints.preparedPathOwnerChain curve differential sheet
    prepared.traced.prepared

/-- Read the root-equivalence chain of the exact cached parents and original endpoint names. -/
def rootChain (cache : ParentCache prepared differential sheet) :
    RootChain cache.parents (ownerName owner) (ownerName (finishOwner prepared.traced.prepared)) :=
  PreparedCachedParentRoots.PreparedRefinementRootEndpoints.OwnerChain.rootChain cache.parents (ownerChain cache)

end Purelib.Riemann.RootContinuation.PreparedCachedParentRoots.ParentCache
