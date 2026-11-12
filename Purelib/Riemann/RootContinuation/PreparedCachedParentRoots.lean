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
public import Purelib.Data.List.DependentProduct
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
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedSubdivisionTrace
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Paths.PreparedSegmentParentBanks
import Purelib.Data.List.Append
import Purelib.Tactic.QuotientFreeOmega
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
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge CenterStates centeredEdges edgeOfStep)
open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.Riemann.Paths.PreparedClearPathModels (CompleteSegment PreparedPath)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName queryEquivalentAdvance)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision advance)
open Purelib.Riemann.Paths.PreparedPathGluing (finishOwner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

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
theorem subdivisionOwnerChain (curve : HyperellipticCurve genus) (differential : Differential
  genus)
    {ambient : Geometry.Rational.Box} {start finish : Gaussian}
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

section Prefix

open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedPathTrace
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.RootIsolation.SquareRoot.Owner

/-- Every actual centered parent starts at the exact original owner after its preceding trace links.

Each retained subdivision step contributes its original source join, moving
link and target join. The prefix reads those supplied links and ends at the
same complete original parent owner; center construction appears only in the
erased source equation.
-/
theorem subdivisionPrefix (curve : HyperellipticCurve genus) (differential : Differential genus)
    {ambient : Geometry.Rational.Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2)
    {left right : Endpoint} (budget : PreparedTraceBudget segment left right) :
    ∀ {current : Endpoint} {owner : Owner (curve.polynomial.eval (segment.pointAt current.parameter))}
      (subdivision : Subdivision segment within current owner)
      (centers : CenterStates curve differential sheet subdivision)
      (fits : budget.RequestsFit current subdivision.requests)
      (index : Fin (centeredEdges curve differential sheet subdivision centers).length),
      let retained := (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget subdivision fits).splitAt
        (3 * index.val)
      let parent := (centeredEdges curve differential sheet subdivision centers)[index.val]'index.isLt
      retained.point = parent.edge.point 0 ∧ HEq retained.owner parent.edge.owner := by
  intro current owner subdivision
  induction subdivision with
  | stop current owner =>
      intro centers fits index
      exact False.elim (Nat.not_lt_zero index.val index.isLt)
  | @next current owner request cached ordered small remaining ih =>
      intro centers fits index
      rcases index with ⟨position, bounded⟩
      cases position with
      | zero =>
          exact ⟨(Integration.PreparedConstantModels.PreparedEdge.point_zero
            (edgeOfStep curve differential segment within current owner request cached ordered small sheet)).symm,
            HEq.rfl⟩
      | succ position =>
          have tailBound : position < (centeredEdges curve differential sheet remaining centers.2).length :=
            Nat.lt_of_succ_lt_succ bounded
          have retained := ih centers.2 fits.2.2 ⟨position, tailBound⟩
          have offset : 3 * (position + 1) = Nat.succ (Nat.succ (Nat.succ (3 * position))) := by
            rewrite [Nat.mul_succ]
            rfl
          dsimp only
          rewrite [offset]
          exact retained

/-- Complete-segment endpoint transport preserves each original parent-prefix owner and actual starting point.

The retained subdivision and its three original links per parent are reused.
Only the original exact complete-segment endpoint and owner transports enter
the proof; no parent or continuation cache is rebuilt.
-/
theorem completeSegmentPrefix (curve : HyperellipticCurve genus) (differential : Differential genus)
    {ambient : Geometry.Rational.Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner)
    (budget : PreparedTraceBudget segment PreparedClearPathModels.zeroEndpoint PreparedClearPathModels.oneEndpoint)
    (fits : budget.RequestsFit PreparedClearPathModels.zeroEndpoint prepared.subdivision.requests)
    (index : Fin (prepared.centeredEdges curve differential sheet).length) :
    let retained := (CompleteSegment.ownerPath prepared budget fits).splitAt (3 * index.val)
    let parent := (prepared.centeredEdges curve differential sheet)[index.val]'index.isLt
    retained.point = parent.edge.point 0 ∧ HEq retained.owner parent.edge.owner := by
  have original := subdivisionPrefix curve differential segment within sheet budget prepared.subdivision
    (Integration.PreparedSubdivisionAutomaticModels.canonicalCenterStates curve differential sheet
      prepared.subdivision) fits index
  have changed := OwnerPath.splitAt_castEndpoints prepared.start_eq prepared.finish_eq
    (by
      unfold PreparedClearPathModels.ownerAtStart
      exact Transport.castOwnerParameter_heq _ _)
    prepared.finishOwner_heq_terminalOwner.symm
    (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget prepared.subdivision fits) (3 * index.val)
  exact ⟨changed.1.trans original.1, changed.2.trans original.2⟩

/-- A complete segment's retained trace has exactly three original links per actual centered parent. -/
theorem completeSegmentTraceLength (curve : HyperellipticCurve genus) (differential : Differential genus)
    {ambient : Geometry.Rational.Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner)
    (budget : PreparedTraceBudget segment PreparedClearPathModels.zeroEndpoint PreparedClearPathModels.oneEndpoint)
    (fits : budget.RequestsFit PreparedClearPathModels.zeroEndpoint prepared.subdivision.requests) :
    (CompleteSegment.ownerPath prepared budget fits).vertices.length =
      3 * (prepared.centeredEdges curve differential sheet).length := by
  rewrite [CompleteSegment.ownerPath, OwnerPath.castEndpoints_vertices,
    PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath_length,
    CenteredPathChain.completeSegment_centeredEdges_length]
  rfl

/-- The exact link count and original parent-owner occurrences of one retained trace. -/
private def PrefixProperty {start finish : Gaussian}
    {source : Owner (curve.polynomial.eval start)} {target : Owner (curve.polynomial.eval finish)}
    (trace : OwnerPath curve.polynomial start source finish target)
    (parents : List (CenteredEdge curve differential)) : Prop :=
  trace.vertices.length = 3 * parents.length ∧
    ∀ index : Fin parents.length,
      let retained := trace.splitAt (3 * index.val)
      let parent := parents[index.val]'index.isLt
      retained.point = parent.edge.point 0 ∧ HEq retained.owner parent.edge.owner

/-- Retaining an original complete segment preserves all actual parent-prefix owners after its exact finish transport.
-/
private theorem ofPreparedPrefixes (curve : HyperellipticCurve genus) (differential : Differential genus)
    {ambient : Geometry.Rational.Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner)
    (budget : PreparedTraceBudget segment PreparedClearPathModels.zeroEndpoint PreparedClearPathModels.oneEndpoint)
    (fits : budget.RequestsFit PreparedClearPathModels.zeroEndpoint prepared.subdivision.requests)
    (requests : List StepRequest) (requestsEq : requests = prepared.subdivision.requests)
    (finishOwner : Owner (curve.polynomial.eval finish)) (finishEq : finishOwner = prepared.finishOwner) :
    PrefixProperty
      (TracedSegment.ofPrepared
        budget prepared fits requests requestsEq finishOwner finishEq).trace.get
      (prepared.centeredEdges curve differential sheet) := by
  change PrefixProperty
    ((CompleteSegment.ownerPath prepared budget fits).reindexOwners rfl finishEq.symm) _
  constructor
  · rewrite [OwnerPath.reindexOwners_vertices]
    exact completeSegmentTraceLength curve differential sheet prepared budget fits
  · intro index
    have original := completeSegmentPrefix curve differential sheet prepared budget fits index
    have changed := OwnerPath.splitAt_castEndpoints rfl rfl HEq.rfl (heq_of_eq finishEq.symm)
      (CompleteSegment.ownerPath prepared budget fits) (3 * index.val)
    exact ⟨changed.1.trans original.1, changed.2.trans original.2⟩

/-- Concatenation preserves each actual parent occurrence and its same original trace owner. -/
private theorem appendPrefixes {start middle finish : Gaussian}
    {source : Owner (curve.polynomial.eval start)} {center : Owner (curve.polynomial.eval middle)}
    {target : Owner (curve.polynomial.eval finish)}
    (first : OwnerPath curve.polynomial start source middle center)
    (last : OwnerPath curve.polynomial middle center finish target)
    {parents remaining : List (CenteredEdge curve differential)}
    (firstPrefixes : PrefixProperty first parents) (lastPrefixes : PrefixProperty last remaining) :
    PrefixProperty (first.append last) (parents ++ remaining) := by
  constructor
  · rewrite [OwnerPath.append_vertices, List.Append.length_append, firstPrefixes.1, lastPrefixes.1,
      List.Append.length_append, Nat.mul_add]
    rfl
  · intro index
    by_cases inside : index.val < parents.length
    · have bounded : 3 * index.val ≤ first.vertices.length := by
        rewrite [firstPrefixes.1]
        exact Nat.mul_le_mul_left 3 inside.le
      have changed := OwnerPath.splitAt_append_left (3 * index.val) first last bounded
      have retained := firstPrefixes.2 ⟨index.val, inside⟩
      have parentEq := List.Append.getElem_append_left parents remaining index.val inside index.isLt
      dsimp only at retained ⊢
      rewrite [parentEq]
      exact ⟨changed.1.trans retained.1, changed.2.trans retained.2⟩
    · let position := index.val - parents.length
      have lower : parents.length ≤ index.val := Nat.le_of_not_gt inside
      have upper : index.val < parents.length + remaining.length := by
        exact index.isLt.trans_eq (List.Append.length_append parents remaining)
      have bounded : position < remaining.length := by
        dsimp only [position]
        omega0
      have offset : parents.length + position = index.val := Nat.add_sub_of_le lower
      have combinedBound : parents.length + position < (parents ++ remaining).length := by
        rewrite [offset]
        exact index.isLt
      have parentEq := (getElem_congr rfl offset.symm index.isLt).trans
        (List.Append.getElem_append_right parents remaining position bounded combinedBound)
      have stepOffset : 3 * index.val = first.vertices.length + 3 * position := by
        rewrite [← offset, Nat.mul_add, firstPrefixes.1]
        rfl
      have changed := OwnerPath.splitAt_append_right first last (3 * position)
      have retained := lastPrefixes.2 ⟨position, bounded⟩
      dsimp only at retained ⊢
      rewrite [stepOffset, parentEq]
      exact ⟨changed.1.trans retained.1, changed.2.trans retained.2⟩

/-- Original traced-path concatenation preserves all supplied segment and tail parent-prefix owners. -/
private theorem tracedConsPrefixes (curve : HyperellipticCurve genus) (differential : Differential genus)
    (sheet : Fin 2) {ambient : Geometry.Rational.Box} {start middle finish : Gaussian}
    {head : Geometry.ClearPath.ClearSegment curve.polynomial ambient start middle}
    {tail : Geometry.ClearPath curve.polynomial ambient middle finish}
    {within : head.WithinAmbient} {owner : Owner (curve.polynomial.eval start)}
    (first : TracedSegment head within owner)
    (rest : TracedPath tail first.finishOwner)
    (firstPrefixes : PrefixProperty first.trace.get (first.prepared.centeredEdges curve differential sheet))
    (restPrefixes : PrefixProperty rest.trace.get
      (CenteredPathChain.ofPreparedPath curve differential sheet rest.prepared).parents) :
    PrefixProperty (TracedPath.cons first rest).trace.get
      (CenteredPathChain.ofPreparedPath curve differential sheet
        (TracedPath.cons first rest).prepared).parents := by
  change PrefixProperty (first.trace.get.append rest.trace.get)
    ((CenteredPathChain.dataOfCompleteSegment curve differential sheet first.prepared).parents ++
      (CenteredPathChain.ofPreparedPath curve differential sheet
        (PreparedPath.castOwner first.finishOwner_eq rest.prepared)).parents)
  rewrite [CenteredPathChain.dataOfCompleteSegment_parents, PreparedSegmentParentBanks.parents_castOwner]
  exact appendPrefixes first.trace.get rest.trace.get firstPrefixes restPrefixes

/-- The original covered-path producer retains the actual centered parent-owner sequence in its supplied trace. -/
private theorem buildPrefixes (curve : HyperellipticCurve genus) (differential : Differential genus)
    (sheet : Fin 2) {ambient : Geometry.Rational.Box} :
    ∀ {start finish : Gaussian} (path : Geometry.ClearPath curve.polynomial ambient start finish)
      (within : path.WithinAmbient) (owner : Owner (curve.polynomial.eval start)),
      let covered := CoveredTracedPath.build path within owner
      PrefixProperty covered.traced.trace.get
        (CenteredPathChain.ofPreparedPath curve differential sheet covered.traced.prepared).parents
  | _, _, .nil point, within, owner => by
      constructor
      · rfl
      · intro index
        exact False.elim (Nat.not_lt_zero index.val index.isLt)
  | _, _, .cons head tail, within, owner => by
      unfold CoveredTracedPath.build
        CoveredTracedPath.cons
      dsimp only
      apply tracedConsPrefixes curve differential sheet
      · exact ofPreparedPrefixes curve differential sheet _ _ _ _ _ _ _
      · exact buildPrefixes curve differential sheet tail within.tail _

end Prefix

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
private theorem ownerAtStart_name {ambient : Geometry.Rational.Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (owner : Owner (curve.polynomial.eval start)) :
    ownerName (PreparedClearPathModels.ownerAtStart segment owner) = ownerName owner := by
  apply ownerName_eq_of_heq (congrArg curve.polynomial.eval segment.pointAt_zero)
  unfold PreparedClearPathModels.ownerAtStart
  exact SquareRoot.Owner.Transport.castOwnerParameter_heq _ _

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- The complete segment's retained terminal owner and transported finish owner have the same name. -/
private theorem finishOwner_name {ambient : Geometry.Rational.Box} {start finish : Gaussian}
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
theorem completeSegmentOwnerChain (curve : HyperellipticCurve genus) (differential :
  Differential genus)
    {ambient : Geometry.Rational.Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner) :
    OwnerChain (prepared.centeredEdges curve differential sheet) (ownerName owner) (ownerName prepared.finishOwner) :=
  (subdivisionOwnerChain curve differential segment within sheet prepared.subdivision
    (PreparedSubdivisionAutomaticModels.canonicalCenterStates curve differential sheet prepared.subdivision)).castNames
      (ownerAtStart_name segment owner) (finishOwner_name prepared)

/-- The original prepared path's centered parents retain the exact start-to-finish owner chain. -/
theorem preparedPathOwnerChain (curve : HyperellipticCurve genus) (differential : Differential
  genus)
    (sheet : Fin 2) {ambient : Geometry.Rational.Box} :
    ∀ {start finish : Gaussian} {path : Geometry.ClearPath curve.polynomial ambient start finish}
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

variable {genus : Nat} {curve : HyperellipticCurve genus} {ambient :
  Geometry.Rational.Box}
  {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
    finish}
  {owner : Owner (curve.polynomial.eval start)} {prepared : CoveredTracedPath path owner}
  {differential : Differential genus} {sheet : Fin 2}

open Purelib.Riemann.RootContinuation
/-- Read the original owner-name chain through a retained parent cache's exact list identity. -/
theorem ownerChain (cache : ParentCache prepared differential sheet) :
    OwnerChain cache.parents (ownerName owner) (ownerName (finishOwner prepared.traced.prepared)) := by
  rw [cache.parents_eq]
  exact PreparedRefinementRootEndpoints.preparedPathOwnerChain curve differential sheet
    prepared.traced.prepared

/-- Read the root-equivalence chain of the exact cached parents and original endpoint names. -/
def rootChain (cache : ParentCache prepared differential sheet) :
    RootChain cache.parents (ownerName owner) (ownerName (finishOwner prepared.traced.prepared)) :=
  OwnerChain.rootChain cache.parents (ownerChain cache)

end Purelib.Riemann.RootContinuation.PreparedCachedParentRoots.ParentCache

namespace Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus} {ambient : Purelib.Geometry.Rational.Box}
variable {start finish : Gaussian} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
variable {owner : Owner (curve.polynomial.eval start)} {prepared : CoveredTracedPath path owner}
variable {differential : Differential genus} {sheet : Fin 2}

/-- The same supplied production trace reaches each actual cached parent at its complete original owner.

The whole original factory equation identifies the retained path, while the
parent-list equation is used only in this proof. It supplies no successful
root comparison and constructs no parent, center or owner cache.
-/
theorem prefix_owner (cache : ParentCache prepared differential sheet) (within : path.WithinAmbient)
    (produced : prepared = CoveredTracedPath.build
      path within owner) (index : Fin cache.parents.length) :
    let retained := prepared.traced.trace.get.splitAt (3 * index.val)
    let parent := cache.parents[index.val]'index.isLt
    retained.point = parent.edge.point 0 ∧ HEq retained.owner parent.edge.owner := by
  have original := PreparedRefinementRootEndpoints.buildPrefixes curve differential sheet path within owner
  have retained := Eq.mpr (congrArg
    (fun covered : CoveredTracedPath path owner =>
      PreparedRefinementRootEndpoints.PrefixProperty covered.traced.trace.get
        (Integration.PreparedDirectDyadicRefinements.CenteredPathChain.ofPreparedPath
          curve differential sheet covered.traced.prepared).parents) produced) original
  have actual := Eq.mpr (congrArg
    (PreparedRefinementRootEndpoints.PrefixProperty prepared.traced.trace.get) cache.parents_eq) retained
  exact actual.2 index

/-- The original owner-path type ending at one actual cached parent's own source coordinate and owner. -/
def OwnerPrefix (cache : ParentCache prepared differential sheet) (index : Fin cache.parents.length) : Type :=
  let parent := cache.parents[index.val]'index.isLt
  OwnerPath curve.polynomial start owner
    (parent.edge.segment.pointAt parent.edge.left.parameter) parent.edge.owner

/-- Read an original parent prefix from the supplied whole trace without forcing or rebuilding that trace again.

The same cached links form the prefix, whose endpoint is transported by its
computed original parent-owner identity. The supplied whole trace equality
and source factory equation are erased; they request no successful numerical
comparison or continuation.
-/
def ownerPrefixFromTrace (cache : ParentCache prepared differential sheet) (within : path.WithinAmbient)
    (produced : prepared = CoveredTracedPath.build
      path within owner) (trace : OwnerPath curve.polynomial start owner finish prepared.traced.finishOwner)
    (traceEq : trace = prepared.traced.trace.get) (index : Fin cache.parents.length) : OwnerPrefix cache index := by
  let selected := trace.splitAt (3 * index.val)
  let parent := cache.parents[index.val]'index.isLt
  have aligned : selected.point = parent.edge.point 0 ∧ HEq selected.owner parent.edge.owner :=
    Eq.mpr (congrArg (fun actual : OwnerPath curve.polynomial start owner finish prepared.traced.finishOwner =>
      (actual.splitAt (3 * index.val)).point = parent.edge.point 0 ∧
        HEq (actual.splitAt (3 * index.val)).owner parent.edge.owner) traceEq)
      (cache.prefix_owner within produced index)
  exact selected.initial.castEndpoints rfl
    (aligned.1.trans parent.edge.point_zero) HEq.rfl aligned.2

/-- Force the same original whole trace once and read the actual cached parent's prefix from it. -/
def ownerPrefix (cache : ParentCache prepared differential sheet) (within : path.WithinAmbient)
    (produced : prepared = CoveredTracedPath.build
      path within owner) (index : Fin cache.parents.length) : OwnerPrefix cache index :=
  let trace := prepared.traced.trace.get
  cache.ownerPrefixFromTrace within produced trace rfl index

/-- The default readback is the complete cache-aware prefix on this same retained whole trace. -/
theorem ownerPrefix_default (cache : ParentCache prepared differential sheet) (within : path.WithinAmbient)
    (produced : prepared = CoveredTracedPath.build
      path within owner) (index : Fin cache.parents.length) :
    cache.ownerPrefix within produced index =
      cache.ownerPrefixFromTrace within produced prepared.traced.trace.get rfl index := rfl

/-- Every actual prefix vertex belongs to the same supplied original whole trace. -/
theorem ownerPrefixFromTrace_member (cache : ParentCache prepared differential sheet) (within : path.WithinAmbient)
    (produced : prepared = CoveredTracedPath.build
      path within owner) (trace : OwnerPath curve.polynomial start owner finish prepared.traced.finishOwner)
    (traceEq : trace = prepared.traced.trace.get) (index : Fin cache.parents.length) (point : Gaussian)
    (member : point ∈ (cache.ownerPrefixFromTrace within produced trace traceEq index).vertices) :
    point ∈ trace.vertices := by
  unfold ownerPrefixFromTrace at member
  rewrite [OwnerPath.castEndpoints_vertices] at member
  exact (trace.splitAt (3 * index.val)).prefix_member point member

/-- The original dependent-product bank of prefixes on the exact retained parent occurrences. -/
def OwnerPrefixes (cache : ParentCache prepared differential sheet) : Type :=
  DependentProduct cache.parents (fun index => OwnerPrefix cache index)

/-- Cache all actual parent prefixes while forcing their same whole original trace outside the entry producer.

Each entry consumes only the supplied trace's original links. Neither the
source preparation, target joins, center queries nor primitive cover are
acquired again; the exact actual parent indices remain those of this cache.
-/
def ownerPrefixes (cache : ParentCache prepared differential sheet) (within : path.WithinAmbient)
    (produced : prepared = CoveredTracedPath.build
      path within owner) : OwnerPrefixes cache :=
  let trace := prepared.traced.trace.get
  DependentProduct.ofFn cache.parents (fun index => cache.ownerPrefixFromTrace within produced trace rfl index)

/-- Every cached entry is the complete original prefix readback on the same once-forced whole trace. -/
theorem ownerPrefixes_get (cache : ParentCache prepared differential sheet) (within : path.WithinAmbient)
    (produced : prepared = CoveredTracedPath.build
      path within owner) (index : Fin cache.parents.length) :
    DependentProduct.get cache.parents (cache.ownerPrefixes within produced) index =
      cache.ownerPrefixFromTrace within produced prepared.traced.trace.get rfl index := by
  unfold ownerPrefixes
  exact DependentProduct.get_ofFn cache.parents _ index

end Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache
