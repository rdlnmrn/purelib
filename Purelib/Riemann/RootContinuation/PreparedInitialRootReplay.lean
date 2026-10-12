module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.RootContinuation.PreparedClosedBankRoots
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Cache
import Purelib.Riemann.Topology.PreparedBankRootChains
public import Purelib.Riemann.Topology.PreparedCycleReplay
public import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.PreparedCycleModels

@[expose] public section

/-!
# Restoring the original initial root chain from saved centres

The certified parent list already contains every centre sampled by the
canonical initial state. This module reads the stored subdivision owners and
parent records, then assembles the original segment, bank and closing root
chains. Canonical preparation and centring occur only in erased source
equations or inside an explicitly requested operational comparison.
-/

namespace Purelib.Riemann.RootContinuation.PreparedInitialRootReplay

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge edgeOfStep centeredEdges)
open Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels (canonicalCenterStates)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.PreparedClearPathModels (CompleteSegment PreparedPath)

variable {genus : Nat} (curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus) (source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus)

section
open Purelib.Approximation.Gaussian
/-- Change a root chain's start while retaining its stored tail.

Composes the supplied name agreement with the first entry or empty-chain witness, preserving every child and remaining
chain node. -/
def changeStartStored {parents : List (CenteredEdge curve source)}
    {first middle last : Name.Basic.Named}
    (roots : RootChain parents middle last) (equivalent : Equivalence.NamedEquivalent first middle) :
    RootChain parents first last :=
  RootChain.casesOn
    (motive := fun parents middle last _ => Equivalence.NamedEquivalent first middle →
      RootChain parents first last) roots
    (fun {_ _} finish initial => .nil (initial.trans finish))
    (fun child {_ _ _} entry tail initial => .cons child (initial.trans entry) tail) equivalent

/-- Stored start transport equals the original root-chain start operation. -/
private theorem changeStartStored_eq {parents : List (CenteredEdge curve source)}
    {first middle last : Name.Basic.Named}
    (roots : RootChain parents middle last) (equivalent : Equivalence.NamedEquivalent first middle) :
    changeStartStored curve source roots equivalent = roots.changeStart equivalent := by
  cases roots <;> rfl

end

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.Topology in
/-- Transport across an exact parent-list equality preserves the root chain heterogeneously. -/
private theorem castChildren_heq {parents children : List (CenteredEdge curve source)}
    {first last : Name.Basic.Named} (equal : parents = children) (roots : RootChain parents first last) :
    HEq (PreparedBankRootChains.RootChain.castChildren equal roots) roots := by
  cases equal
  rfl

open Purelib.Approximation.Gaussian in
/-- Wrapping a retained comparison procedure leaves its equivalence record unchanged. -/
private theorem deferredComparison_eq {first last : Name.Basic.Named}
    (equivalent : Equivalence.NamedEquivalent first last) :
    (show Equivalence.NamedEquivalent first last from
      ⟨fun left right amount positive => equivalent.compare left right amount positive⟩) = equivalent := by
  cases equivalent
  rfl

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.Integration in
/-- Transport a prepared edge's original entry comparison to its retained parent.

Uses the exact parent-edge equality and defers calls to the original owner-to-base-query comparison. -/
def parentEntry (edge : PreparedConstantModels.PreparedEdge curve source)
    (parent : CenteredEdge curve source) (equal : parent.edge = edge) :
    Equivalence.NamedEquivalent (ownerName edge.owner) (parent.edge.rootName 0 parent.edge.baseInside) :=
  cast (congrArg (fun current : PreparedConstantModels.PreparedEdge curve source =>
    Equivalence.NamedEquivalent (ownerName edge.owner) (current.rootName 0 current.baseInside)) equal.symm)
    ⟨fun left right amount positive => edge.ownerRootEquivalent_baseQuery.compare left right amount positive⟩

open Purelib.Riemann.Integration in
/-- The canonical centered parent retains the edge's original entry comparison. -/
private theorem parentEntry_self (edge : PreparedConstantModels.PreparedEdge curve source)
    (equal : (⟨edge, PreparedConstantModels.PreparedEdge.CenterState.canonical edge⟩ : CenteredEdge curve source).edge =
      edge) :
    parentEntry curve source edge ⟨edge, PreparedConstantModels.PreparedEdge.CenterState.canonical edge⟩ equal =
      edge.ownerRootEquivalent_baseQuery := by
  exact deferredComparison_eq edge.ownerRootEquivalent_baseQuery

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Topology in
/-- Transport a prepared edge's finish comparison to its retained parent.

Keeps the exact advanced owner and defers calls to the original query-to-advance comparison, using only the supplied
parent-edge identity. -/
def parentJoin (edge : PreparedConstantModels.PreparedEdge curve source)
    (parent : CenteredEdge curve source) (equal : parent.edge = edge) :
    Equivalence.NamedEquivalent (parent.edge.rootName 1 (by decide))
      (ownerName (PreparedSheetContinuation.advance edge.segment edge.within edge.left edge.owner edge.request
        edge.small)) :=
  cast (congrArg (fun current : PreparedConstantModels.PreparedEdge curve source =>
    Equivalence.NamedEquivalent (current.rootName 1 (by decide))
      (ownerName (PreparedSheetContinuation.advance edge.segment edge.within edge.left edge.owner edge.request
        edge.small)))
    equal.symm)
    ⟨fun left right amount positive =>
      (PreparedBankRootChains.queryEquivalentAdvance edge).compare left right amount positive⟩

open Purelib.Riemann.Integration in
open Purelib.Riemann.Topology in
/-- The canonical centered parent retains the original query-to-advance comparison. -/
private theorem parentJoin_self (edge : PreparedConstantModels.PreparedEdge curve source)
    (equal : (⟨edge, PreparedConstantModels.PreparedEdge.CenterState.canonical edge⟩ : CenteredEdge curve source).edge =
      edge) :
    parentJoin curve source edge ⟨edge, PreparedConstantModels.PreparedEdge.CenterState.canonical edge⟩ equal =
      PreparedBankRootChains.queryEquivalentAdvance edge := by
  exact deferredComparison_eq (PreparedBankRootChains.queryEquivalentAdvance edge)

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Topology in
/-- Replay a subdivision root chain on an explicitly retained parent list.

Follows the original subdivision spine, keeps each actual head parent and tail list, and transports entry and join
comparisons through their exact readback equalities. -/
def subdivisionRoots {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2)
    {left : Endpoint} {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval (segment.pointAt
      left.parameter))}
    (spine : Subdivision segment within left owner) :
    (parents : List (CenteredEdge curve source)) →
    parents = (CenteredPathChain.dataOfCanonicalSubdivision curve source segment within sheet spine).parents →
    RootChain parents (ownerName owner) (ownerName spine.terminalOwner) :=
  Subdivision.casesOn
    (motive := fun _ owner spine => (parents : List (CenteredEdge curve source)) →
      parents = (CenteredPathChain.dataOfCanonicalSubdivision curve source segment within sheet spine).parents →
      RootChain parents (ownerName owner) (ownerName spine.terminalOwner)) spine
    (fun _ owner parents equal =>
      PreparedBankRootChains.RootChain.castChildren equal.symm
        (RootChain.nil (Equivalence.NamedEquivalent.refl (ownerName owner))))
    (fun current owner request cached ordered small remaining parents =>
      List.casesOn
        (motive := fun parents =>
          parents = (CenteredPathChain.dataOfCanonicalSubdivision curve source segment within sheet
            (.next current owner request cached ordered small remaining)).parents →
          RootChain parents (ownerName owner) (ownerName remaining.terminalOwner)) parents
        (fun equal => by
          rw [CenteredPathChain.dataOfCanonicalSubdivision_next] at equal
          cases equal)
        (fun parent rest equal =>
          let edge := edgeOfStep curve source segment within current owner request cached ordered small sheet
          have equalCons : parent :: rest =
              ⟨edge, PreparedConstantModels.PreparedEdge.CenterState.canonical edge⟩ ::
                (CenteredPathChain.dataOfCanonicalSubdivision curve source segment within sheet remaining).parents :=
                  equal
          have headEqual := (List.cons.inj equalCons).1
          have tailEqual := (List.cons.inj equalCons).2
          let entry := parentEntry curve source edge parent (congrArg CenteredEdge.edge headEqual)
          let join := parentJoin curve source edge parent (congrArg CenteredEdge.edge headEqual)
          let tail := subdivisionRoots segment within sheet remaining rest tailEqual
          .cons parent entry (changeStartStored curve source tail join)))
termination_by structural spine

section
open Purelib.Approximation.Gaussian
/-- Cons preserves heterogeneous equality of root-chain tails with equal parent lists. -/
private theorem cons_heq (child : CenteredEdge curve source)
    {parents children : List (CenteredEdge curve source)} {first last : Name.Basic.Named}
    (equal : parents = children)
    (entry : Equivalence.NamedEquivalent first (child.edge.rootName 0 child.edge.baseInside))
    {tail : RootChain parents (child.edge.rootName 1 (by decide)) last}
    {other : RootChain children (child.edge.rootName 1 (by decide)) last} (same : HEq tail other) :
    HEq (RootChain.cons child entry tail) (RootChain.cons child entry other) := by
  cases equal
  cases eq_of_heq same
  rfl

/-- Start-name transport preserves heterogeneous equality over equal parent lists. -/
private theorem changeStart_heq {parents children : List (CenteredEdge curve source)}
    {first middle last : Name.Basic.Named} (equal : parents = children)
    {roots : RootChain parents middle last} {other : RootChain children middle last}
    (same : HEq roots other) (equivalent : Equivalence.NamedEquivalent first middle) :
    HEq (roots.changeStart equivalent) (other.changeStart equivalent) := by
  cases equal
  cases eq_of_heq same
  rfl

end

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Topology in
/-- The replayed subdivision chain equals the canonical chain heterogeneously.

Inducts over the original spine, retaining the exact parent identities and the original entry and finish comparison
records. -/
private theorem subdivisionRoots_heq {ambient : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) (sheet : Fin 2)
    {left : Endpoint} {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval (segment.pointAt
      left.parameter))}
    (spine : Subdivision segment within left owner) :
    ∀ (parents : List (CenteredEdge curve source))
      (equal : parents = (CenteredPathChain.dataOfCanonicalSubdivision curve source segment within sheet
        spine).parents),
    HEq (subdivisionRoots curve source segment within sheet spine parents equal)
      (PreparedBankRootChains.subdivisionRootChain curve source segment within sheet spine
        (canonicalCenterStates curve source sheet spine)) := by
  induction spine with
  | stop left owner =>
      intro parents equal
      cases equal
      rfl
  | next left owner request cached ordered small remaining ih =>
      intro parents equal
      cases equal
      simp only [CenteredPathChain.dataOfCanonicalSubdivision_next]
      unfold subdivisionRoots PreparedBankRootChains.subdivisionRootChain
      dsimp only [canonicalCenterStates]
      rw [changeStartStored_eq, parentEntry_self, parentJoin_self]
      let edge := edgeOfStep curve source segment within left owner request cached ordered small sheet
      exact cons_heq curve source ⟨edge, PreparedConstantModels.PreparedEdge.CenterState.canonical edge⟩
        (CenteredPathChain.dataOfCanonicalSubdivision_parents curve source segment within sheet remaining)
        edge.ownerRootEquivalent_baseQuery
        (changeStart_heq curve source
          (CenteredPathChain.dataOfCanonicalSubdivision_parents curve source segment within sheet remaining)
          (ih _ rfl) (PreparedBankRootChains.queryEquivalentAdvance edge))

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.Topology in
/-- Transport across exact endpoint-name equalities preserves the chain heterogeneously. -/
private theorem castNames_heq {parents : List (CenteredEdge curve source)}
    {first last left right : Name.Basic.Named}
    (firstEq : first = left) (lastEq : last = right) (roots : RootChain parents first last) :
    HEq (PreparedBankRootChains.RootChain.castNames firstEq lastEq roots) roots := by
  cases firstEq
  cases lastEq
  rfl

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann.Topology
/-- Replay roots for a complete segment on its retained parents.

Uses the original subdivision chain and exact start/finish owner-name identities to preserve the segment's endpoint
owners. -/
def segmentRoots {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner)
    (parents : List (CenteredEdge curve source))
    (equal : parents = (CenteredPathChain.dataOfCompleteSegment curve source sheet prepared).parents) :
    RootChain parents (ownerName owner) (ownerName prepared.finishOwner) :=
  PreparedBankRootChains.RootChain.castNames
    (PreparedBankRootChains.ownerAtStart_name segment owner) (PreparedBankRootChains.finishOwner_name
      prepared)
    (subdivisionRoots curve source segment within sheet prepared.subdivision parents equal)

/-- Segment replay is heterogeneously equal to the original complete-segment chain.

Combines the subdivision identity with exact endpoint-name transports. -/
private theorem segmentRoots_heq {ambient : Box} {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : CompleteSegment segment within owner)
    (parents : List (CenteredEdge curve source))
    (equal : parents = (CenteredPathChain.dataOfCompleteSegment curve source sheet prepared).parents) :
    HEq (segmentRoots curve source sheet prepared parents equal)
      (PreparedBankRootChains.completeSegmentRootChain curve source sheet prepared) := by
  unfold segmentRoots PreparedBankRootChains.completeSegmentRootChain
  exact (castNames_heq curve source _ _ _).trans
    ((subdivisionRoots_heq curve source segment within sheet prepared.subdivision parents equal).trans
      (castNames_heq curve source _ _ _).symm)

end

open Purelib.Approximation.Gaussian in
/-- Append preserves heterogeneous equality of chains over equal component lists. -/
private theorem append_heq {first second left right : List (CenteredEdge curve source)}
    {a b c : Name.Basic.Named} (firstEq : first = left) (secondEq : second = right)
    {firstRoots : RootChain first a b} {secondRoots : RootChain second b c}
    {leftRoots : RootChain left a b} {rightRoots : RootChain right b c}
    (firstSame : HEq firstRoots leftRoots) (secondSame : HEq secondRoots rightRoots) :
    HEq (firstRoots.append secondRoots) (leftRoots.append rightRoots) := by
  cases firstEq
  cases secondEq
  cases eq_of_heq firstSame
  cases eq_of_heq secondSame
  rfl

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Topology in
/-- Replay a prepared path's root chain on a retained parent list.

Splits the actual list at each segment's retained step count, reuses its prefix and suffix, and composes the
corresponding segment and tail chains. -/
def pathRoots {ambient : Box} (sheet : Fin 2)
    {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (prepared : PreparedPath path owner) :
    (parents : List (CenteredEdge curve source)) →
    parents = (CenteredPathChain.ofPreparedPath curve source sheet prepared).parents →
    RootChain parents (ownerName owner) (ownerName (PreparedPathGluing.finishOwner prepared)) :=
  PreparedPath.casesOn
    (motive := fun {start finish} _ owner prepared => (parents : List (CenteredEdge curve source)) →
      parents = (CenteredPathChain.ofPreparedPath curve source sheet prepared).parents →
      RootChain parents (ownerName owner) (ownerName (PreparedPathGluing.finishOwner prepared))) prepared
    (fun _ owner parents equal =>
      PreparedBankRootChains.RootChain.castChildren equal.symm
        (RootChain.nil (Equivalence.NamedEquivalent.refl (ownerName owner))))
    (fun _ _ _ _ head tail parents equal =>
      let count := head.subdivision.stepCount
      have firstEq : parents.take count = (CenteredPathChain.dataOfCompleteSegment curve source sheet head).parents :=
        by
        rw [equal, CenteredPathChain.ofPreparedPath]
        exact List.take_left' (CenteredPathChain.dataOfCompleteSegment_parents_length curve source sheet head)
      have lastEq : parents.drop count = (CenteredPathChain.ofPreparedPath curve source sheet tail).parents := by
        rw [equal, CenteredPathChain.ofPreparedPath]
        exact List.drop_left' (CenteredPathChain.dataOfCompleteSegment_parents_length curve source sheet head)
      let first := segmentRoots curve source sheet head (parents.take count) firstEq
      let last := pathRoots sheet tail (parents.drop count) lastEq
      PreparedBankRootChains.RootChain.castChildren
        (List.take_append_drop count parents) (first.append last))
termination_by structural prepared

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Topology in
/-- Path replay is heterogeneously equal to the original prepared-path chain.

Uses exact take/drop identities and the segment replay certificate while preserving each original append order. -/
private theorem pathRoots_heq {ambient : Box} (sheet : Fin 2)
    {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (prepared : PreparedPath path owner) :
    ∀ (parents : List (CenteredEdge curve source))
      (equal : parents = (CenteredPathChain.ofPreparedPath curve source sheet prepared).parents),
    HEq (pathRoots curve source sheet prepared parents equal)
      (PreparedBankRootChains.preparedPathRootChain curve source sheet prepared) := by
  induction prepared with
  | nil point owner =>
      intro parents equal
      exact castChildren_heq curve source _ _
  | cons segment path owner within head tail ih =>
      intro parents equal
      unfold pathRoots
      dsimp only
      apply HEq.trans (castChildren_heq curve source _ _)
      unfold PreparedBankRootChains.preparedPathRootChain
      have firstEq : parents.take head.subdivision.stepCount =
          (CenteredPathChain.dataOfCompleteSegment curve source sheet head).parents := by
        rw [equal, CenteredPathChain.ofPreparedPath]
        exact List.take_left' (CenteredPathChain.dataOfCompleteSegment_parents_length curve source sheet head)
      have lastEq : parents.drop head.subdivision.stepCount =
          (CenteredPathChain.ofPreparedPath curve source sheet tail).parents := by
        rw [equal, CenteredPathChain.ofPreparedPath]
        exact List.drop_left' (CenteredPathChain.dataOfCompleteSegment_parents_length curve source sheet head)
      apply append_heq curve source firstEq lastEq
      · exact (segmentRoots_heq curve source sheet head _ firstEq).trans (castChildren_heq curve source _ _).symm
      · exact ih _ lastEq

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Topology in
open Purelib.RootIsolation in
/-- Replay roots through the actual cached prepared path of a dyadic bank.

Retains the supplied parent list and its identity with the cached centered-bank readback. -/
def bankRoots {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (bank : PreparedPath.DyadicBank depth diameter positive path owner)
    (parents : List (CenteredEdge curve source))
    (equal : parents = (CenteredPathChain.ofDyadicBank curve source sheet bank).parents) :
    RootChain parents (ownerName owner) (ownerName (PreparedPathGluing.finishOwner bank.prepared)) :=
  pathRoots curve source sheet (SquareRoot.Preparation.Bank.Cache.DyadicBank.cache bank).prepared parents
    (equal.trans (congrArg (fun data => data.parents)
      (PreparedCycleReplay.centeredBank_eq_cache curve source sheet bank)))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Topology in
/-- The prepared path chain matches the bank's canonical root chain heterogeneously.

Checks all original bank constructors, retaining the certified executed bank's parent transport. -/
private theorem bank_canonical_heq {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (bank : PreparedPath.DyadicBank depth diameter positive path owner) :
    HEq (PreparedBankRootChains.preparedPathRootChain curve source sheet bank.prepared)
      (PreparedBankRootChains.dyadicBankRootChain curve source sheet bank) := by
  cases bank with
  | safe => rfl
  | executed => rfl
  | executedCertified checked => exact (castChildren_heq curve source _ _).symm
  | certified => rfl

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Topology in
open Purelib.RootIsolation in
/-- Bank replay is heterogeneously equal to the original dyadic-bank chain.

Combines the cached path replay identity with the bank constructor's exact canonical-chain readback. -/
private theorem bankRoots_heq {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (bank : PreparedPath.DyadicBank depth diameter positive path owner)
    (parents : List (CenteredEdge curve source))
    (equal : parents = (CenteredPathChain.ofDyadicBank curve source sheet bank).parents) :
    HEq (bankRoots curve source sheet bank parents equal)
      (PreparedBankRootChains.dyadicBankRootChain curve source sheet bank) := by
  unfold bankRoots
  exact (pathRoots_heq curve source sheet
    (SquareRoot.Preparation.Bank.Cache.DyadicBank.cache bank).prepared parents _).trans
    (bank_canonical_heq curve source sheet bank)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Topology in
/-- The centered bank's parent count equals the retained prepared step count. -/
public theorem bank_length {depth : Nat} {diameter : Fraction.Rational} {positive : 0 < diameter}
    {ambient : Box} {start finish : Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (bank : PreparedPath.DyadicBank depth diameter positive path owner) :
    (CenteredPathChain.ofDyadicBank curve source sheet bank).parents.length = bank.prepared.stepCount :=
  (CenteredPathChain.ofDyadicBank_parents_length curve source sheet bank).trans bank.prepared_stepCount.symm

/-- Read the first retained block by taking its exact declared length. -/
public theorem split_take {first last : List (CenteredEdge curve source)}
    (parents : List (CenteredEdge curve source)) (count : Nat) (lengthEq : first.length = count)
    (equal : parents = first ++ last) : parents.take count = first := by
  rw [equal]
  exact List.take_left' lengthEq

/-- Read the remaining retained block after dropping the exact first-block length. -/
public theorem split_drop {first last : List (CenteredEdge curve source)}
    (parents : List (CenteredEdge curve source)) (count : Nat) (lengthEq : first.length = count)
    (equal : parents = first ++ last) : parents.drop count = last := by
  rw [equal]
  exact List.drop_left' lengthEq

open Purelib.Riemann.Readings in
set_option genInjectivity false in
/-- Four retained parent blocks of a joined boundary tour.

Keeps forward, right, backward and left lists with their original dyadic-bank identities and their exact ordered
concatenation to the input parents. -/
structure JoinedInputs (tour : PreparedBoundaryGluing.JoinedBoundaryDoublePath curve)
    (parents : List (CenteredEdge curve source)) where
  /-- Retained forward parent block. -/ forward : List (CenteredEdge curve source)
  /-- Retained right-boundary parent block. -/ right : List (CenteredEdge curve source)
  /-- Retained backward parent block. -/ backward : List (CenteredEdge curve source)
  /-- Retained left-boundary parent block. -/ left : List (CenteredEdge curve source)
  /-- The forward block is exactly the original sheet-zero bank parents. -/ forward_eq : forward =
    (CenteredPathChain.ofDyadicBank curve source 0 tour.data.forwardChecked).parents
  /-- The right block is exactly the original sheet-zero boundary bank parents. -/ right_eq : right =
    (CenteredPathChain.ofDyadicBank curve source 0 tour.data.rightBoundaryChecked).parents
  /-- The backward block is exactly the original sheet-one bank parents. -/ backward_eq : backward =
    (CenteredPathChain.ofDyadicBank curve source 1 tour.data.backwardChecked).parents
  /-- The left block is exactly the original sheet-one boundary bank parents. -/ left_eq : left =
    (CenteredPathChain.ofDyadicBank curve source 1 tour.data.leftBoundaryChecked).parents
  /-- The four blocks concatenate in tour order to the actual parent list. -/ combined_eq : forward ++ (right ++
    (backward ++ left)) = parents

constructive_injectivity JoinedInputs

open Purelib.Riemann.Integration in
open Purelib.Riemann.Readings in
/-- Split the actual joined-boundary parents into their four retained blocks.

Uses the original prepared step counts and take/drop operations, retaining all bank readbacks and the exact
recombination equality. -/
def joinedInputs (tour : PreparedBoundaryGluing.JoinedBoundaryDoublePath curve)
    (parents : List (CenteredEdge curve source))
    (equal : parents = (PreparedSwitchedRefinements.boundaryState curve source tour.data).parents) :
    JoinedInputs curve source tour parents :=
  let firstCount := tour.data.forwardChecked.prepared.stepCount
  let rightCount := tour.data.rightBoundaryChecked.prepared.stepCount
  let backCount := tour.data.backwardChecked.prepared.stepCount
  let forward := parents.take firstCount
  let afterForward := parents.drop firstCount
  let right := afterForward.take rightCount
  let afterRight := afterForward.drop rightCount
  let backward := afterRight.take backCount
  let left := afterRight.drop backCount
  have allEqual := equal.trans (PreparedSwitchedRefinements.boundaryState_parents curve source tour.data)
  have forwardEqual := split_take curve source parents firstCount (bank_length curve source 0
    tour.data.forwardChecked) allEqual
  have afterForwardEqual := split_drop curve source parents firstCount (bank_length curve source 0
    tour.data.forwardChecked) allEqual
  have rightEqual := split_take curve source afterForward rightCount
    (bank_length curve source 0 tour.data.rightBoundaryChecked) afterForwardEqual
  have afterRightEqual := split_drop curve source afterForward rightCount
    (bank_length curve source 0 tour.data.rightBoundaryChecked) afterForwardEqual
  have backwardEqual := split_take curve source afterRight backCount
    (bank_length curve source 1 tour.data.backwardChecked) afterRightEqual
  have leftEqual := split_drop curve source afterRight backCount
    (bank_length curve source 1 tour.data.backwardChecked) afterRightEqual
  ⟨forward, right, backward, left, forwardEqual, rightEqual, backwardEqual, leftEqual, by
    change parents.take firstCount ++ ((parents.drop firstCount).take rightCount ++
      (((parents.drop firstCount).drop rightCount).take backCount ++
        ((parents.drop firstCount).drop rightCount).drop backCount)) = parents
    rw [List.take_append_drop, List.take_append_drop, List.take_append_drop]⟩

open Purelib.Riemann.Readings in
open Purelib.Riemann.Topology in
/-- Assemble the root chain of four retained joined-boundary blocks.

Replays each original bank, transports only stored adjacent owner identities, and appends the chains in
forward/right/backward/left order. -/
def joinedRoots (tour : PreparedBoundaryGluing.JoinedBoundaryDoublePath curve)
    {parents : List (CenteredEdge curve source)} (parts : JoinedInputs curve source tour parents) :
    RootChain parents (ownerName tour.data.forwardOwner) (ownerName tour.finishOwner) :=
  let forward := bankRoots curve source 0 tour.data.forwardChecked parts.forward parts.forward_eq
  let right := PreparedBankRootChains.RootChain.castNames
    (congrArg ownerName tour.rightOwner_eq) rfl
    (bankRoots curve source 0 tour.data.rightBoundaryChecked parts.right parts.right_eq)
  let backward := PreparedBankRootChains.RootChain.castNames
    (congrArg ownerName tour.backwardOwner_eq) rfl
    (bankRoots curve source 1 tour.data.backwardChecked parts.backward parts.backward_eq)
  let left := PreparedBankRootChains.RootChain.castNames
    (congrArg ownerName tour.leftOwner_eq) (congrArg ownerName tour.finishOwner_eq.symm)
    (bankRoots curve source 1 tour.data.leftBoundaryChecked parts.left parts.left_eq)
  PreparedBankRootChains.RootChain.castChildren parts.combined_eq
    (forward.append (right.append (backward.append left)))

open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- The assembled joined-boundary replay equals its original chain heterogeneously.

Uses the four bank replay certificates and exact owner and parent-list transports. -/
private theorem joinedRoots_heq (tour : PreparedBoundaryGluing.JoinedBoundaryDoublePath curve)
    {parents : List (CenteredEdge curve source)} (parts : JoinedInputs curve source tour parents) :
    HEq (joinedRoots curve source tour parts) (PreparedClosedBankRoots.JoinedBoundaryDoublePath.initialRootChain tour
      source) := by
  unfold joinedRoots PreparedClosedBankRoots.JoinedBoundaryDoublePath.initialRootChain
  apply HEq.trans (castChildren_heq curve source _ _)
  apply HEq.trans ?_ (castChildren_heq curve source _ _).symm
  apply append_heq curve source parts.forward_eq
    (congrArg₂ List.append parts.right_eq (congrArg₂ List.append parts.backward_eq parts.left_eq))
  · exact bankRoots_heq curve source 0 tour.data.forwardChecked parts.forward parts.forward_eq
  · apply append_heq curve source parts.right_eq (congrArg₂ List.append parts.backward_eq parts.left_eq)
    · exact (castNames_heq curve source _ _ _).trans
        ((bankRoots_heq curve source 0 tour.data.rightBoundaryChecked parts.right parts.right_eq).trans
          (castNames_heq curve source _ _ _).symm)
    · apply append_heq curve source parts.backward_eq parts.left_eq
      · exact (castNames_heq curve source _ _ _).trans
          ((bankRoots_heq curve source 1 tour.data.backwardChecked parts.backward parts.backward_eq).trans
            (castNames_heq curve source _ _ _).symm)
      · exact (castNames_heq curve source _ _ _).trans
          ((bankRoots_heq curve source 1 tour.data.leftBoundaryChecked parts.left parts.left_eq).trans
            (castNames_heq curve source _ _ _).symm)

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.Topology in
/-- Finish-name transport preserves heterogeneous equality over equal parent lists. -/
private theorem changeFinish_heq {parents children : List (CenteredEdge curve source)}
    {first last finish : Name.Basic.Named} (equal : parents = children)
    {roots : RootChain parents first last} {other : RootChain children first last}
    (same : HEq roots other) (equivalent : Equivalence.NamedEquivalent last finish) :
    HEq (PreparedBankRootChains.RootChain.changeFinish roots equivalent) (PreparedBankRootChains.RootChain.changeFinish
      other equivalent) := by
  cases equal
  cases eq_of_heq same
  rfl

open Purelib.Riemann.Integration in
open Purelib.Riemann.Readings in
open Purelib.Riemann.Topology in
/-- Close the replayed joined-boundary chain with its retained root agreement.

Keeps the original parent list and tour, changing only the final name through the stored closure equivalence. -/
def closedRoots (tour : PreparedBoundaryClosure.ClosedBoundaryDoublePath curve)
    (parents : List (CenteredEdge curve source))
    (equal : parents = (PreparedSwitchedRefinements.boundaryState curve source tour.joined.data).parents) :
    RootChain parents (ownerName tour.joined.data.forwardOwner) (ownerName tour.joined.data.forwardOwner) :=
  PreparedBankRootChains.RootChain.changeFinish
    (joinedRoots curve source tour.joined (joinedInputs curve source tour.joined parents equal)) tour.rootEquivalent

open Purelib.Riemann.Integration in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Closed replay equals the original closed-boundary initial chain heterogeneously. -/
private theorem closedRoots_heq (tour : PreparedBoundaryClosure.ClosedBoundaryDoublePath curve)
    (parents : List (CenteredEdge curve source))
    (equal : parents = (PreparedSwitchedRefinements.boundaryState curve source tour.joined.data).parents) :
    HEq (closedRoots curve source tour parents equal)
      (PreparedClosedBankRoots.ClosedBoundaryDoublePath.initialRootChain tour source) := by
  exact changeFinish_heq curve source equal
    (joinedRoots_heq curve source tour.joined (joinedInputs curve source tour.joined parents equal)) _

open Purelib.Riemann.Integration
open Purelib.Riemann.Readings
open Purelib.Riemann.Topology
/-- Attach replayed closed roots to the actual retained initial state.

Requires its exact equality with the original root-closed initial state and preserves its parents and geometric closure
witness. -/
def initial (tour : PreparedBoundaryClosure.ClosedBoundaryDoublePath curve)
    (state : PreparedSwitchedRefinements.DirectSwitchedState curve source)
    (equal : state = (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial tour source).state) :
    PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState curve source (ownerName
      tour.joined.data.forwardOwner) where
  state := state
  closed := by rw [equal]; exact (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial tour
    source).closed
  roots := closedRoots curve source tour state.parents (by rw [equal]; rfl)

/-- The replayed initial state equals the original root-closed initial state.

Uses the exact closed-chain replay equality while preserving the state and closure certificate. -/
theorem initial_eq (tour : PreparedBoundaryClosure.ClosedBoundaryDoublePath curve)
    (state : PreparedSwitchedRefinements.DirectSwitchedState curve source)
    (equal : state = (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial tour source).state) :
    initial curve source tour state equal =
      PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial tour source := by
  cases equal
  have rootsEqual := eq_of_heq (closedRoots_heq curve source tour
    (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial tour source).state.parents rfl)
  exact congrArg (fun roots => PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState.mk
    (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial tour source).state
      (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial tour source).closed roots) rootsEqual

end Purelib.Riemann.RootContinuation.PreparedInitialRootReplay
