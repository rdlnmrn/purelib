module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Junctions
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Queries
public import Purelib.Riemann.Paths.OwnerTracePath.Concatenation
public import Purelib.Riemann.Paths.OwnerTracePath.Join
import Purelib.Data.Vector.Dependent.Subtype
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Linked
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.RootComparison
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTracePath.Concatenation.Split
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.RootChain
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Data.List.DependentProduct
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Refinement

/-! # Sewn root paths of the actual retained local member

The original open block paths and their own spatial ambients stay intact.
The original uniform parameter junctions compare their retained finishing
and starting references. Actual Owner joins then sew the supplied paths;
one separate final/first join closes the resulting sampled root trace.
This construction does not identify that representative with the member's
staged cycle or provide a parameter/spatial cylinder.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib.Data.Rat.Fraction
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order.Arithmetic (instZeroLEOneClass)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin ownerName)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_heq
  castOwnerParameter_initial_box)
open PreparedParent (startPoint finishPoint)

namespace StageAttempt.Requested.LocalMember

attribute [local irreducible] CertifiedSquareRoot.rawRoot
attribute [local irreducible] PreparedParent.ShiftedAcquisition.Linked.first
attribute [local irreducible] Shifted.requested ShiftedGeometry.Requested.request ShiftedGeometry.Request.shape

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}
    {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    {zeroPaid : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    {zero : LocalMember source ranges allocation roots widths targetCurrent targetFloor targetRootStage 0 zeroPaid}
    {increment : Canonical} {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    (cached : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage increment admitted)

/-- The original start coordinate and the SAME block's actual first Step Owner. -/
@[expose] def startVertex (index : Fin (parent :: parents).length) :
    Σ point : Canonical, Owner ((Fibre.frameCurve cached.targetFrame).polynomial.eval point) :=
  ⟨(startPoint ((parent :: parents)[index.val]'index.isLt)).coordinate,
    (DependentProduct.get (parent :: parents) cached.member.blocks index).first.owner⟩

/-- The original finish coordinate and the SAME acquired block's actual terminal Owner. -/
@[expose] def finishVertex (index : Fin (parent :: parents).length) :
    Σ point : Canonical, Owner ((Fibre.frameCurve cached.targetFrame).polynomial.eval point) :=
  ⟨(finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate,
    (DependentProduct.get (parent :: parents) cached.member.blocks index).shifted.acquired.traced.finishOwner⟩

/-- Read the SAME already materialized open OwnerPath at one literal original block occurrence. -/
@[expose] def blockPath (index : Fin (parent :: parents).length) :
    OwnerPath (Fibre.frameCurve cached.targetFrame).polynomial
      (cached.startVertex index).1 (cached.startVertex index).2
      (cached.finishVertex index).1 (cached.finishVertex index).2 :=
  (DependentProduct.get (parent :: parents) cached.member.blocks index).actual.val

/-- The retained open path is the whole original actual trace factory, including all moving and stationary links. -/
theorem blockPath_eq (index : Fin (parent :: parents).length) :
    cached.blockPath index =
      (DependentProduct.get (parent :: parents) cached.member.blocks index).shifted.acquired.traced.trace.get :=
  (DependentProduct.get (parent :: parents) cached.member.blocks index).actual.property

/-- The actual starting Owner carries the SAME retained first Step's complete root-certificate name. -/
theorem startVertex_rootName (index : Fin (parent :: parents).length) :
    ownerName (cached.startVertex index).2 =
      (DependentProduct.get (parent :: parents) cached.member.blocks index).first.root.value.name := by
  change ownerName (DependentProduct.get (parent :: parents) cached.member.blocks index).first.owner = _
  rewrite [(DependentProduct.get (parent :: parents) cached.member.blocks index).first.root_eq]
  rfl

/-- Read the SAME block's actual signed child RootChain anchored at its original materialized path Owners. -/
@[expose] def blockRoots (index : Fin (parent :: parents).length) :
    RootChain (DependentProduct.get (parent :: parents) cached.member.blocks index).shifted.parents.covered.parents
      (ownerRootName (cached.startVertex index).2.parameterNonzero (cached.startVertex index).2)
      (ownerRootName (cached.finishVertex index).2.parameterNonzero (cached.finishVertex index).2) :=
  (DependentProduct.get (parent :: parents) cached.member.blocks index).roots

/-- The signed child chain retains its whole original actual-path/reference-cache factory. -/
theorem blockRoots_eq (index : Fin (parent :: parents).length) :
    cached.blockRoots index =
      (DependentProduct.get (parent :: parents) cached.member.blocks index).shifted.parents.rootChain
        (DependentProduct.get (parent :: parents) cached.member.blocks index).comparison.paths.rootViews :=
  (DependentProduct.get (parent :: parents) cached.member.blocks index).roots_eq

/-- The actual source chain identifies this finish coordinate with the literal following start coordinate. -/
theorem followingPoint (index : Fin (parent :: parents).length) :
    (cached.finishVertex index).1 = (cached.startVertex (followingIndex parent parents index)).1 :=
  (congrArg (fun point : LiftedPoint 2 => point.coordinate) (following_point chain index)).symm

/-- The retained parameter path reaches the radicand of this SAME actual member finish coordinate. -/
theorem junction_finishParameter (index : Fin (parent :: parents).length)
    (continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted index) :
    continued.path.point 1 =
      (Fibre.frameCurve cached.targetFrame).polynomial.eval (cached.finishVertex index).1 :=
  (continued.point_eq 1).trans
    (congrArg (fun offset : Canonical => (Paths.polynomial (parameter + offset)).eval
      (finishPoint ((parent :: parents)[index.val]'index.isLt)).coordinate) (Basic.one_mul increment))

/-- The SAME junction radicand is the following actual member's original start radicand. -/
theorem junction_startParameter (index : Fin (parent :: parents).length)
    (continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted index) :
    continued.path.point 1 = (Fibre.frameCurve cached.targetFrame).polynomial.eval
      (cached.startVertex (followingIndex parent parents index)).1 :=
  (junction_finishParameter (cached := cached) (zero := zero) index continued).trans
    (congrArg (Fibre.frameCurve cached.targetFrame).polynomial.eval (cached.followingPoint index))

/-- Reindex the SAME cached h-member finishing reference to the exact original junction radicand. -/
@[expose] def junctionFirstReference (index : Fin (parent :: parents).length)
    (continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted index) : Owner (continued.path.point 1) :=
  castOwnerParameter (junction_finishParameter (cached := cached) (zero := zero) index continued).symm
    (DependentProduct.get (parent :: parents) cached.member.blocks index).comparison.finishReference

/-- Reindex the SAME cached following h-member starting reference without selecting a new root. -/
@[expose] def junctionLastReference (index : Fin (parent :: parents).length)
    (continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted index) : Owner (continued.path.point 1) :=
  castOwnerParameter (junction_startParameter (cached := cached) (zero := zero) index continued).symm
    (DependentProduct.get (parent :: parents) cached.member.blocks
      (followingIndex parent parents index)).comparison.firstReference

/-- The first displayed radicand cast preserves the whole original h-member finishing reference. -/
theorem junctionFirstReference_heq (index : Fin (parent :: parents).length)
    (continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted index) :
    HEq (junctionFirstReference (cached := cached) (zero := zero) index continued)
      (DependentProduct.get (parent :: parents) cached.member.blocks index).comparison.finishReference :=
  castOwnerParameter_heq (junction_finishParameter (cached := cached) (zero := zero) index continued).symm
    (DependentProduct.get (parent :: parents) cached.member.blocks index).comparison.finishReference

/-- The following displayed radicand cast preserves the whole original h-member starting reference. -/
theorem junctionLastReference_heq (index : Fin (parent :: parents).length)
    (continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted index) :
    HEq (junctionLastReference (cached := cached) (zero := zero) index continued)
      (DependentProduct.get (parent :: parents) cached.member.blocks
        (followingIndex parent parents index)).comparison.firstReference :=
  castOwnerParameter_heq (junction_startParameter (cached := cached) (zero := zero) index continued).symm
    (DependentProduct.get (parent :: parents) cached.member.blocks
      (followingIndex parent parents index)).comparison.firstReference

/-- The first reindexed actual reference refines the original first zero-member seed box. -/
theorem junctionFirstReference_refines (index : Fin (parent :: parents).length)
    (continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted index) :
    (junctionFirstReference (cached := cached) (zero := zero) index continued).track.initial.box.Refines
      ((covered.entry index).val.neighborhood count).base.seed.owner.track.initial.box := by
  have same := (castOwnerParameter_initial_box (junction_finishParameter (cached := cached) (zero :=
    zero) index continued).symm
    (DependentProduct.get (parent :: parents) cached.member.blocks index).comparison.finishReference).trans
    (DependentProduct.get (parent :: parents) cached.member.blocks index).comparison.finishReference_box
  change (castOwnerParameter (junction_finishParameter (cached := cached) (zero := zero) index continued).symm
    (DependentProduct.get (parent :: parents) cached.member.blocks
      index).comparison.finishReference).track.initial.box.Refines _
  rewrite [same]
  exact Geometry.Rational.Box.refines_refl _

/-- The following reindexed reference refines its separate original second zero-member seed box. -/
theorem junctionLastReference_refines (index : Fin (parent :: parents).length)
    (continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted index) :
    (junctionLastReference (cached := cached) (zero := zero) index continued).track.initial.box.Refines
      ((covered.entry (followingIndex parent parents index)).val.neighborhood
        count).base.seed.owner.track.initial.box := by
  have same := (castOwnerParameter_initial_box (junction_startParameter (cached := cached) (zero :=
    zero) index continued).symm
    (DependentProduct.get (parent :: parents) cached.member.blocks
      (followingIndex parent parents index)).comparison.firstReference).trans
    (DependentProduct.get (parent :: parents) cached.member.blocks
      (followingIndex parent parents index)).comparison.firstReference_box
  change (castOwnerParameter (junction_startParameter (cached := cached) (zero := zero) index continued).symm
    (DependentProduct.get (parent :: parents) cached.member.blocks
      (followingIndex parent parents index)).comparison.firstReference).track.initial.box.Refines _
  rewrite [same]
  exact Geometry.Rational.Box.refines_refl _

/-- Compose two actual retained reference comparisons with the SAME full-parameter junction endpoint comparison.

Both cast h-reference Owners remain the original member's stored Owners.
The original firstRetained/secondRetained outputs are supplied as data;
this composition builds no additional fixed-box or member reference.
-/
def junctionEquivalent (index : Fin (parent :: parents).length)
    (continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted index)
    (first : NamedEquivalent
      (ownerRootName (continued.path.nonzero 1
        ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩)
        (continued.path.First 1 ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩))
      (ownerName (junctionFirstReference (cached := cached) (zero := zero) index continued)))
    (last : NamedEquivalent
      (ownerRootName (continued.path.nonzero 1
        ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩)
        (continued.path.Second 1 ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩))
      (ownerName (junctionLastReference (cached := cached) (zero := zero) index continued))) :
    NamedEquivalent (ownerName (cached.finishVertex index).2)
      (ownerName (cached.startVertex (followingIndex parent parents index)).2) := by
  let left := DependentProduct.get (parent :: parents) cached.member.blocks index
  let right := DependentProduct.get (parent :: parents) cached.member.blocks (followingIndex parent parents index)
  let referenceCompared := first.symm.trans ((continued.path.expose continued.final).trans last)
  have firstName := SquareRootTrackEquivalence.ownerRootName_castOwnerParameter
    (junction_finishParameter (cached := cached) (zero := zero) index continued).symm left.comparison.finishReference
  have lastName := SquareRootTrackEquivalence.ownerRootName_castOwnerParameter
    (junction_startParameter (cached := cached) (zero := zero) index continued).symm right.comparison.firstReference
  let references := NamedEquivalent.transport firstName lastName referenceCompared
  exact left.comparison.referenceEquivalent.trans (references.trans right.comparison.startEquivalent.symm)

/-- The two original reference-comparison outputs and their composed actual endpoint comparison, with whole factories.

The original operations construct their genuine budget.ownerAt references
at time one. Their outputs are retained once, separately from the GIVEN h
references and the SAME original full-parameter final comparator.
-/
@[expose] def JunctionComparison (index : Fin (parent :: parents).length)
    (continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted index) :=
  (first : {value : NamedEquivalent
      (ownerRootName (continued.path.nonzero 1
        ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩)
        (continued.path.First 1 ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩))
      (ownerName (junctionFirstReference (cached := cached) (zero := zero) index continued)) //
    value = continued.path.firstRetained 1
      ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩
      (junctionFirstReference (cached := cached) (zero := zero) index continued)
        (junctionFirstReference_refines (cached := cached) (zero := zero) index continued)}) ×
  (last : {value : NamedEquivalent
      (ownerRootName (continued.path.nonzero 1
        ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩)
        (continued.path.Second 1 ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩))
      (ownerName (junctionLastReference (cached := cached) (zero := zero) index continued)) //
    value = continued.path.secondRetained 1
      ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩
      (junctionLastReference (cached := cached) (zero := zero) index continued)
        (junctionLastReference_refines (cached := cached) (zero := zero) index continued)}) ×
  {value : NamedEquivalent (ownerName (cached.finishVertex index).2)
      (ownerName (cached.startVertex (followingIndex parent parents index)).2) //
    value = junctionEquivalent (cached := cached) (zero := zero) index continued first.val last.val}

/-- Bind the two original reference comparison calls once and retain their actual outputs and composite factory. -/
def junctionComparison (index : Fin (parent :: parents).length)
    (continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted index) : JunctionComparison (cached := cached) (zero := zero) index continued :=
  let first := continued.path.firstRetained 1
    ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩
    (junctionFirstReference (cached := cached) (zero := zero) index continued)
      (junctionFirstReference_refines (cached := cached) (zero := zero) index continued)
  let last := continued.path.secondRetained 1
    ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩
    (junctionLastReference (cached := cached) (zero := zero) index continued)
      (junctionLastReference_refines (cached := cached) (zero := zero) index continued)
  let equivalent := junctionEquivalent (cached := cached) (zero := zero) index continued first last
  ⟨⟨first, rfl⟩, ⟨last, rfl⟩, ⟨equivalent, rfl⟩⟩

namespace JunctionComparison

variable {cached} {index : Fin (parent :: parents).length}
    {continued : JunctionContinuation roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted index} (comparison : JunctionComparison (cached := cached) (zero := zero) index continued)

/-- The actual first comparison output retains its original firstRetained call on the SAME h-reference Owner. -/
theorem first_eq : comparison.1.val = continued.path.firstRetained 1
    ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩
    (junctionFirstReference (cached := cached) (zero := zero) index continued)
      (junctionFirstReference_refines (cached := cached) (zero := zero) index continued) :=
  comparison.1.property

/-- The actual second comparison output retains its separate original secondRetained call. -/
theorem last_eq : comparison.2.1.val = continued.path.secondRetained 1
    ⟨instZeroLEOneClass.zero_le_one, Order.Basic.le_refl 1⟩
    (junctionLastReference (cached := cached) (zero := zero) index continued)
      (junctionLastReference_refines (cached := cached) (zero := zero) index continued) :=
  comparison.2.1.property

/-- The actual endpoint comparison consumes these SAME two retained outputs and the SAME original final comparator. -/
theorem equivalent_eq : comparison.2.2.val =
    junctionEquivalent (cached := cached) (zero :=
      zero) index continued comparison.1.val comparison.2.1.val := comparison.2.2.property

end JunctionComparison

/-- Retain each actual complete endpoint comparison cache and its same-junction factory in original occurrence order. -/
@[expose] def BoundaryComparisons
    (continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted) :=
  DependentProduct (parent :: parents) (fun index =>
    {value : JunctionComparison (cached := cached) (zero := zero) index (continued.entry index) //
      value = junctionComparison (cached := cached) (zero := zero) index (continued.entry index)})

/-- Materialize each complete endpoint comparison cache once from the SAME given member and junction product. -/
def boundaryComparisons
    (continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted) :
    BoundaryComparisons (cached := cached) (zero := zero) continued :=
  DependentProduct.ofFn (parent :: parents)
    (fun index => ⟨junctionComparison (cached := cached) (zero := zero) index (continued.entry index), rfl⟩)

/-- The actual physical equality at an interior handoff retains its literal successor occurrence. -/
theorem interiorPoint (index : Fin parents.length) :
    (cached.finishVertex index.castSucc).1 = (cached.startVertex index.succ).1 :=
  (cached.followingPoint index.castSucc).trans
    (congrArg (fun position : Fin (parent :: parents).length => (cached.startVertex position).1)
      (followingIndex_interior parent parents index))

/-- Read the SAME interior comparator through the original finite successor-index equality. -/
def interiorEquivalent
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    (compared : BoundaryComparisons (cached := cached) (zero := zero) continued) (index : Fin parents.length) :
    NamedEquivalent (ownerName (cached.finishVertex index.castSucc).2) (ownerName (cached.startVertex index.succ).2) :=
  NamedEquivalent.transport rfl
    (congrArg (fun position : Fin (parent :: parents).length => ownerName (cached.startVertex position).2)
      (followingIndex_interior parent parents index))
    (DependentProduct.get (parent :: parents) compared index.castSucc).val.2.2.val

/-- Exactly the original nonfinal occurrences retain one actual stationary Owner join each. -/
@[expose] def InteriorJoins
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    (compared : BoundaryComparisons (cached := cached) (zero := zero) continued) :=
  DependentVector (fun index : Fin parents.length =>
    {value : OwnerJoin
        (castOwnerParameter (congrArg (Fibre.frameCurve cached.targetFrame).polynomial.eval
          (cached.interiorPoint index)) (cached.finishVertex index.castSucc).2)
        (cached.startVertex index.succ).2 //
      value = OwnerJoin.acquireAt (cached.interiorPoint index) (interiorEquivalent (cached := cached) (zero :=
        zero) compared index)})

/-- Acquire the genuine new interior join tails/comparisons once, preserving every original endpoint Owner. -/
def interiorJoins
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    (compared : BoundaryComparisons (cached := cached) (zero := zero) continued) : InteriorJoins (cached :=
      cached) (zero := zero) compared :=
  DependentVector.ofFnWithEq (fun index =>
    OwnerJoin.acquireAt (cached.interiorPoint index) (interiorEquivalent (cached := cached) (zero :=
      zero) compared index))

/-- Read a supplied retained interior join as its original same-coordinate OwnerLink. -/
def interiorLink
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    {compared : BoundaryComparisons (cached := cached) (zero := zero) continued}
      (joins : InteriorJoins (cached := cached) (zero := zero) compared)
    (index : Fin parents.length) :
    OwnerLink (Fibre.frameCurve cached.targetFrame).polynomial
      (cached.finishVertex index.castSucc).1 (cached.startVertex index.succ).1
      (cached.finishVertex index.castSucc).2 (cached.startVertex index.succ).2 :=
  OwnerLink.ofJoinAt (cached.interiorPoint index) (joins.get index).val

/-- The literal final source occurrence returns to the original first physical coordinate. -/
theorem finalPoint : (cached.finishVertex (Fin.last parents.length)).1 = (cached.startVertex 0).1 :=
  (cached.followingPoint (Fin.last parents.length)).trans
    (congrArg (fun position : Fin (parent :: parents).length => (cached.startVertex position).1)
      (followingIndex_last parent parents))

/-- Read the actual final/first root comparison without identifying either endpoint Owner. -/
def finalEquivalent
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    (compared : BoundaryComparisons (cached := cached) (zero := zero) continued) :
    NamedEquivalent (ownerName (cached.finishVertex (Fin.last parents.length)).2)
      (ownerName (cached.startVertex 0).2) :=
  NamedEquivalent.transport rfl
    (congrArg (fun position : Fin (parent :: parents).length => ownerName (cached.startVertex position).2)
      (followingIndex_last parent parents))
    (DependentProduct.get (parent :: parents) compared (Fin.last parents.length)).val.2.2.val

/-- The single separate closing join retains its actual original acquireAt factory. -/
@[expose] def ClosingJoin
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    (compared : BoundaryComparisons (cached := cached) (zero := zero) continued) :=
  {value : OwnerJoin
      (castOwnerParameter (congrArg (Fibre.frameCurve cached.targetFrame).polynomial.eval cached.finalPoint)
        (cached.finishVertex (Fin.last parents.length)).2) (cached.startVertex 0).2 //
    value = OwnerJoin.acquireAt cached.finalPoint (finalEquivalent (cached := cached) (zero := zero) compared)}

/-- Acquire the final/first Owner join once; it is not inserted as an interior arc. -/
def closingJoin
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    (compared : BoundaryComparisons (cached := cached) (zero := zero) continued) : ClosingJoin (cached :=
      cached) (zero := zero) compared :=
  ⟨OwnerJoin.acquireAt cached.finalPoint (finalEquivalent (cached := cached) (zero := zero) compared), rfl⟩

/-- Concatenate all actual given block paths using only the retained nonfinal joins. -/
def joinedPath
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    {compared : BoundaryComparisons (cached := cached) (zero := zero) continued}
      (joins : InteriorJoins (cached := cached) (zero := zero) compared) :
    OwnerPath (Fibre.frameCurve cached.targetFrame).polynomial
      (cached.startVertex 0).1 (cached.startVertex 0).2
      (cached.finishVertex (Fin.last parents.length)).1 (cached.finishVertex (Fin.last parents.length)).2 :=
  OwnerPath.concatenate parents.length (fun index => (cached.startVertex index).1)
    (fun index => (cached.finishVertex index).1) (fun index => (cached.startVertex index).2)
    (fun index => (cached.finishVertex index).2) (fun index => cached.blockPath index)
    (fun index => interiorLink (cached := cached) (zero := zero) joins index)

/-- The actual once-bound joined path is the original concatenation on its SAME supplied paths and links. -/
theorem joinedPath_eq
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    {compared : BoundaryComparisons (cached := cached) (zero := zero) continued}
    (joins : InteriorJoins (cached := cached) (zero := zero) compared) :
    joinedPath (cached := cached) (zero := zero) joins =
      OwnerPath.concatenate parents.length (fun index => (cached.startVertex index).1)
        (fun index => (cached.finishVertex index).1) (fun index => (cached.startVertex index).2)
        (fun index => (cached.finishVertex index).2) (fun index => cached.blockPath index)
        (fun index => interiorLink (cached := cached) (zero := zero) joins index) := by
  unfold joinedPath
  rfl

/-- The sewn open path retains all original block vertices and all interior handoff vertices in exact order. -/
theorem joinedPath_vertices
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    {compared : BoundaryComparisons (cached := cached) (zero := zero) continued}
      (joins : InteriorJoins (cached := cached) (zero := zero) compared) :
    (joinedPath (cached := cached) (zero := zero) joins).vertices = OwnerPath.interleaveVertices parents.length
      (fun index => (cached.blockPath index).vertices) (fun index => (cached.startVertex index.succ).1) := by
  unfold joinedPath
  exact OwnerPath.concatenate_vertices parents.length (fun index => (cached.startVertex index).1)
    (fun index => (cached.finishVertex index).1) (fun index => (cached.startVertex index).2)
    (fun index => (cached.finishVertex index).2) (fun index => cached.blockPath index)
    (fun index => interiorLink (cached := cached) (zero := zero) joins index)

/-- Reindex only the returning path's finish coordinate, retaining the complete original terminal Owner. -/
def returningPath
    (path : OwnerPath (Fibre.frameCurve cached.targetFrame).polynomial
      (cached.startVertex 0).1 (cached.startVertex 0).2
      (cached.finishVertex (Fin.last parents.length)).1 (cached.finishVertex (Fin.last parents.length)).2) :
    OwnerPath (Fibre.frameCurve cached.targetFrame).polynomial
      (cached.startVertex 0).1 (cached.startVertex 0).2 (cached.startVertex 0).1
      (castOwnerParameter (congrArg (Fibre.frameCurve cached.targetFrame).polynomial.eval cached.finalPoint)
        (cached.finishVertex (Fin.last parents.length)).2) :=
  path.castEndpoints rfl cached.finalPoint HEq.rfl
    (castOwnerParameter_heq (congrArg (Fibre.frameCurve cached.targetFrame).polynomial.eval cached.finalPoint)
      (cached.finishVertex (Fin.last parents.length)).2).symm

/-- Returning-coordinate transport keeps every original block and interior handoff vertex. -/
theorem returningPath_vertices
    (path : OwnerPath (Fibre.frameCurve cached.targetFrame).polynomial
      (cached.startVertex 0).1 (cached.startVertex 0).2
      (cached.finishVertex (Fin.last parents.length)).1 (cached.finishVertex (Fin.last parents.length)).2) :
    (cached.returningPath path).vertices = path.vertices := by
  unfold returningPath
  exact OwnerPath.castEndpoints_vertices rfl cached.finalPoint HEq.rfl
    (castOwnerParameter_heq (congrArg (Fibre.frameCurve cached.targetFrame).polynomial.eval cached.finalPoint)
      (cached.finishVertex (Fin.last parents.length)).2).symm path

/-- The whole given member/junction caches, actual new join caches, exact sewn path and one closed sampled realization.

Only the original nonfinal links enter the concatenation. The separately
stored final/first join is consumed by the original close operation, with
its real endpoint thresholds and new sampled trace retained in the result.
-/
@[expose] def Sewing
    (continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted) :=
  (_originals : {value : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage increment admitted ×
      JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted //
    value = (cached, continued)}) ×
  (compared : BoundaryComparisons (cached := cached) (zero := zero) continued) ×
  (joins : InteriorJoins (cached := cached) (zero := zero) compared) ×
  (closing : ClosingJoin (cached := cached) (zero := zero) compared) ×
  (path : {value : OwnerPath (Fibre.frameCurve cached.targetFrame).polynomial
      (cached.startVertex 0).1 (cached.startVertex 0).2
      (cached.finishVertex (Fin.last parents.length)).1 (cached.finishVertex (Fin.last parents.length)).2 //
    value = joinedPath (cached := cached) (zero := zero) joins}) ×
  {value : OwnerPath.ClosedRealization (cached.returningPath path.val) //
    value = (cached.returningPath path.val).close closing.val}

/-- Sew and close the GIVEN member using one GIVEN actual uniform-junction product.

The original source, zero/member Steps, materialized acquisitions and
parameter paths are projected unchanged. Each boundary comparator and
OwnerJoin is bound once. Closing samples the resulting retained paths and
the SAME closing join once; it does not reacquire a member or source mesh.
-/
def sewFromJunctions
    (continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted) :
    Sewing (cached := cached) (zero := zero) continued :=
  let compared : BoundaryComparisons (cached := cached) (zero := zero) continued :=
    boundaryComparisons (cached := cached) (zero := zero) continued
  let joins : InteriorJoins (cached := cached) (zero := zero) compared := interiorJoins (cached :=
    cached) (zero := zero) compared
  let closing : ClosingJoin (cached := cached) (zero := zero) compared := closingJoin (cached :=
    cached) (zero := zero) compared
  let path := joinedPath (cached := cached) (zero := zero) joins
  let result := (cached.returningPath path).close closing.val
  ⟨⟨(cached, continued), rfl⟩, compared, joins, closing, ⟨path, rfl⟩, ⟨result, rfl⟩⟩

/-- Construct one actual junction product, then sew the GIVEN member without rebuilding either member or source.

The given zero member supplies the original parameter-junction references.
The result retains their complete factory beside the actual sewn paths,
new joins and sampled closed realization. Repeated invocations remain
independent constructions; no family-wide memoization is asserted.
-/
def sew (zero : LocalMember source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage 0 zeroPaid) :
    (continued : {value : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage
      zero increment admitted // value = zero.junctionContinuations (roots := roots) (widths := widths)
        (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
        increment admitted}) × Sewing (cached := cached) (zero := zero) continued.val :=
  let continued := zero.junctionContinuations (roots := roots) (widths := widths)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    increment admitted
  ⟨⟨continued, rfl⟩, sewFromJunctions (cached := cached) (zero := zero) continued⟩

namespace Sewing

variable {cached}
    {continued : JunctionContinuations roots widths targetCurrent targetFloor targetRootStage zero increment admitted}
    (sewn : Sewing (cached := cached) (zero := zero) continued)

/-- The SAME complete member and uniform-junction product remain retained data. -/
theorem originals_eq : sewn.1.val = (cached, continued) := sewn.1.property

/-- Read the stored actual endpoint comparison bank without another junction continuation. -/
@[expose] def comparisons : BoundaryComparisons (cached := cached) (zero := zero) continued := sewn.2.1

/-- Read the stored exactly nonfinal join bank without acquiring a root tail again. -/
@[expose] def joins : InteriorJoins (cached := cached) (zero := zero) sewn.comparisons := sewn.2.2.1

/-- Read the separately retained single final/first closing join. -/
@[expose] def closing : ClosingJoin (cached := cached) (zero := zero) sewn.comparisons := sewn.2.2.2.1

/-- Read the SAME once-concatenated actual open block paths. -/
@[expose] def path : OwnerPath (Fibre.frameCurve cached.targetFrame).polynomial
    (cached.startVertex 0).1 (cached.startVertex 0).2
    (cached.finishVertex (Fin.last parents.length)).1 (cached.finishVertex (Fin.last parents.length)).2 :=
  sewn.2.2.2.2.1.val

/-- The whole sewn path is the original finite concatenation on these SAME stored interior joins. -/
theorem path_eq : sewn.path = joinedPath (cached := cached) (zero := zero) sewn.joins := sewn.2.2.2.2.1.property

/-- Read one GIVEN whole sewn path at a selected original block split, preserving that split's complete middle Owner.

Only splitAt on the SAME retained whole path executes. Its concatenation
and original block are linked by the original whole-path factories; those
factories are not evaluated to rebuild the concatenated tail.
-/
def splitBlock (outer : Fin (parent :: parents).length)
    (divided : OwnerPath.Split (blockPath (cached := cached) outer)) :
    OwnerPath.Split (Sewing.path (cached := cached) (zero := zero) sewn) :=
  OwnerPath.concatenateSplit parents.length (fun index => (startVertex (cached := cached) index).1)
    (fun index => (finishVertex (cached := cached) index).1)
    (fun index => (startVertex (cached := cached) index).2)
    (fun index => (finishVertex (cached := cached) index).2)
    (fun index => blockPath (cached := cached) index)
    (fun index => interiorLink (cached := cached) (zero := zero)
      (Sewing.joins (cached := cached) (zero := zero) sewn) index)
    ⟨Sewing.path (cached := cached) (zero := zero) sewn,
      (Sewing.path_eq (cached := cached) (zero := zero) sewn).trans
        (joinedPath_eq (cached := cached) (zero := zero)
          (Sewing.joins (cached := cached) (zero := zero) sewn))⟩ outer divided

/-- The actual whole-path split retains the SAME selected point and complete Owner of the given original block split. -/
theorem splitBlock_vertex (outer : Fin (parent :: parents).length)
    (divided : OwnerPath.Split (blockPath (cached := cached) outer)) :
    (splitBlock (cached := cached) (zero := zero) sewn outer divided).vertex = divided.vertex := by
  unfold splitBlock
  exact OwnerPath.concatenateSplit_vertex parents.length (fun index => (startVertex (cached := cached) index).1)
    (fun index => (finishVertex (cached := cached) index).1)
    (fun index => (startVertex (cached := cached) index).2)
    (fun index => (finishVertex (cached := cached) index).2)
    (fun index => blockPath (cached := cached) index)
    (fun index => interiorLink (cached := cached) (zero := zero)
      (Sewing.joins (cached := cached) (zero := zero) sewn) index)
    ⟨Sewing.path (cached := cached) (zero := zero) sewn,
      (Sewing.path_eq (cached := cached) (zero := zero) sewn).trans
        (joinedPath_eq (cached := cached) (zero := zero)
          (Sewing.joins (cached := cached) (zero := zero) sewn))⟩ outer divided

/-- Read the closed realization of the SAME returning-coordinate view, including its original sampled root list. -/
@[expose] def realization : OwnerPath.ClosedRealization (cached.returningPath sewn.path) :=
  sewn.2.2.2.2.2.val

/-- The complete closed realization uses the SAME stored closing join exactly once. -/
theorem realization_eq : sewn.realization = (cached.returningPath sewn.path).close sewn.closing.val :=
  sewn.2.2.2.2.2.property

/-- Every original block vertex and interior stationary contribution remains in the returned path, in order. -/
theorem vertices : (cached.returningPath sewn.path).vertices =
    OwnerPath.interleaveVertices parents.length (fun index => (cached.blockPath index).vertices)
      (fun index => (cached.startVertex index.succ).1) :=
  (cached.returningPath_vertices sewn.path).trans
    ((congrArg OwnerPath.vertices sewn.path_eq).trans (joinedPath_vertices (cached := cached) (zero :=
      zero) sewn.joins))

/-- Every retained endpoint comparator is its SAME full-parameter junction factory. -/
theorem comparison_eq (index : Fin (parent :: parents).length) :
    (DependentProduct.get (parent :: parents) sewn.comparisons index).val =
      junctionComparison (cached := cached) (zero := zero) index (continued.entry index) :=
  (DependentProduct.get (parent :: parents) sewn.comparisons index).property

/-- Every retained nonfinal join is its original acquireAt factory on the SAME cached endpoint comparison. -/
theorem join_eq (index : Fin parents.length) :
    (sewn.joins.get index).val =
      OwnerJoin.acquireAt (cached.interiorPoint index) (interiorEquivalent (cached := cached) (zero :=
        zero) sewn.comparisons index) :=
  (sewn.joins.get index).property

/-- The SAME final/first join uses the actual literal final occurrence, independently of the interior join bank. -/
theorem closing_eq : sewn.closing.val =
    OwnerJoin.acquireAt cached.finalPoint (finalEquivalent (cached := cached) (zero :=
      zero) sewn.comparisons) := sewn.closing.property

end Sewing

/-- Each actual retained child has its original ordered interval on its OWN shifted segment and spatial ambient. -/
theorem child_segmentSource (outer : Fin (parent :: parents).length)
    (inner : Fin (DependentProduct.get (parent :: parents) cached.member.blocks
      outer).shifted.parents.covered.parents.length) :
    Riemann.Paths.PreparedSegmentSources.SegmentSource
      (DependentProduct.get (parent :: parents) cached.member.blocks outer).shifted.segment
      ((DependentProduct.get (parent :: parents) cached.member.blocks outer).shifted.parents.covered.parents[
        inner.val]'inner.isLt) :=
  (DependentProduct.get (parent :: parents) cached.member.blocks outer).shifted.segmentSource inner rfl

/-- The original all-query map of each actual child keeps its exact source-parent interval and occurrence. -/
theorem child_point (outer : Fin (parent :: parents).length)
    (inner : Fin (DependentProduct.get (parent :: parents) cached.member.blocks
      outer).shifted.parents.covered.parents.length)
    (input : Rational) :
    ((DependentProduct.get (parent :: parents) cached.member.blocks outer).shifted.parents.covered.parents[
      inner.val]'inner.isLt).edge.point input =
      ((parent :: parents)[outer.val]'outer.isLt).edge.point
        (Riemann.Branches.PreparedSheetContinuation.parameterAt
          ((DependentProduct.get (parent :: parents) cached.member.blocks outer).shifted.parents.covered.parents[
            inner.val]'inner.isLt).edge.left
          ((DependentProduct.get (parent :: parents) cached.member.blocks outer).shifted.parents.covered.parents[
            inner.val]'inner.isLt).edge.request input) :=
  (DependentProduct.get (parent :: parents) cached.member.blocks outer).shifted.originalPoint_eq inner rfl input

/-- The actual member's global geometric child word is precisely the ordered flattening of these SAME block caches.

This is an original list-index readback, preserving repeated and stationary
occurrences. It identifies no root Owner or path representative by its
coordinates, and claims no equality with the new sewn root path.
-/
theorem childWords_eq : cached.member.geometry.parents =
    (ShiftedGeometry.blockWords source.prepared ranges allocation admitted widths cached.member.blocks).flatten :=
  (congrArg (fun value => value.parents) cached.member.geometry_eq).trans
    (ShiftedGeometry.build_parents source.prepared ranges allocation admitted widths cached.member.blocks chain roots)

end StageAttempt.Requested.LocalMember

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
