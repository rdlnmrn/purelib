module

public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
public import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
public import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.ContinuedInverseRootOverlap
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.Query
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Membership
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.PreparedRefinementRootChains

/-! # Signed model agreement through actual covered parent occurrences

Each original covering patch contains its whole parent. Operational root
links identify consecutive patch Points at the same retained junction.
The original nearest-sign cocycle then propagates one known model sign
through the entire literal ordered parent spine.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents

open Purelib.Data.Gaussian
open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample SignAlignment)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

/-- The actual continued model on two original Newton steps, with its retained box and overlap budget. -/
private def ready {polynomial : InverseRootPolynomial.Polynomial} {count : Nat}
    (patch : ContinuedNeighborhood polynomial count) : OverlapReady polynomial patch.base.box :=
  ⟨patch.base.refine 2, OverlapReady.two_steps_small patch.base.model⟩

/-- Compose two unflipped comparisons on the same actual three-model overlap. -/
private theorem nearest_trans {firstBox middleBox lastBox : Box}
    (first : OverlapReady curve.polynomial firstBox) (middle : OverlapReady curve.polynomial middleBox)
    (last : OverlapReady curve.polynomial lastBox) (point : Canonical)
    (firstInside : firstBox.Contains point) (middleInside : middleBox.Contains point)
    (lastInside : lastBox.Contains point)
    (firstNear : normSq (first.model.value.eval point - middle.model.value.eval point) ≤
      normSq (first.model.value.eval point + middle.model.value.eval point))
    (lastNear : normSq (middle.model.value.eval point - last.model.value.eval point) ≤
      normSq (middle.model.value.eval point + last.model.value.eval point)) :
    normSq (first.model.value.eval point - last.model.value.eval point) ≤
      normSq (first.model.value.eval point + last.model.value.eval point) := by
  let firstSample : OverlapSample first.model middle.model point :=
    ⟨_, rfl, _, rfl, ⟨false, _, rfl, by
      change Canonical.normSq (first.model.value.eval point - middle.model.value.eval point) ≤
        Canonical.normSq (first.model.value.eval point + middle.model.value.eval point)
      simpa only [Norm.Basic.normSq_eq_canonical] using firstNear⟩⟩
  let lastSample : OverlapSample middle.model last.model point :=
    ⟨_, rfl, _, rfl, ⟨false, _, rfl, by
      change Canonical.normSq (middle.model.value.eval point - last.model.value.eval point) ≤
        Canonical.normSq (middle.model.value.eval point + last.model.value.eval point)
      simpa only [Norm.Basic.normSq_eq_canonical] using lastNear⟩⟩
  let direct := OverlapSample.build first.model last.model point
  have flip : direct.alignment.flip = false :=
    (OverlapReady.cocycle first middle last firstInside middleInside lastInside
      firstSample lastSample direct).trans rfl
  have scalar := direct.alignment.nearest
  rewrite [direct.alignment.value_eq, flip] at scalar
  change Canonical.normSq (direct.leftValue - direct.rightValue) ≤
    Canonical.normSq (direct.leftValue + direct.rightValue) at scalar
  simpa only [direct.leftValue_eq, direct.rightValue_eq,
    Norm.Basic.normSq_eq_canonical] using scalar

/-- The retained start-point sign is unchanged at the literal endpoint of the same contained parent. -/
private theorem nearest_finish {modelBox : Box} (reference : OverlapReady curve.polynomial modelBox)
    {parent : CenteredEdge curve differential} (patch : PreparedPatch parent)
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (referenceFirst : modelBox.Contains (parent.edge.point 0))
    (referenceLast : modelBox.Contains (parent.edge.point 1))
    (near : normSq (reference.model.value.eval (parent.edge.point 0) -
      ((patch.neighborhood count).base.refine 2).value.eval (parent.edge.point 0)) ≤
      normSq (reference.model.value.eval (parent.edge.point 0) +
        ((patch.neighborhood count).base.refine 2).value.eval (parent.edge.point 0))) :
    normSq (reference.model.value.eval (parent.edge.point 1) -
      ((patch.neighborhood count).base.refine 2).value.eval (parent.edge.point 1)) ≤
      normSq (reference.model.value.eval (parent.edge.point 1) +
        ((patch.neighborhood count).base.refine 2).value.eval (parent.edge.point 1)) := by
  let edge : EdgeTransition reference.model ((patch.neighborhood count).base.refine 2)
      (parent.edge.point 0) (parent.edge.point 1) :=
    ⟨referenceFirst, referenceLast,
      (patch.neighborhood count).box_refines.contains (patch.start_inside count),
      (patch.neighborhood count).box_refines.contains finishInside,
      ⟨_, rfl, _, rfl, ⟨false, _, rfl, by
        change Canonical.normSq (reference.model.value.eval (parent.edge.point 0) -
          ((patch.neighborhood count).base.refine 2).value.eval (parent.edge.point 0)) ≤
          Canonical.normSq (reference.model.value.eval (parent.edge.point 0) +
            ((patch.neighborhood count).base.refine 2).value.eval (parent.edge.point 0))
        simpa only [Norm.Basic.normSq_eq_canonical] using near⟩⟩⟩
  have flip : (OverlapSample.build reference.model ((patch.neighborhood count).base.refine 2)
      (parent.edge.point 1)).alignment.flip = false := edge.flip_eq_finish.symm
  let direct := OverlapSample.build reference.model ((patch.neighborhood count).base.refine 2)
    (parent.edge.point 1)
  have scalar := direct.alignment.nearest
  rewrite [direct.alignment.value_eq, flip] at scalar
  change Canonical.normSq (direct.leftValue - direct.rightValue) ≤
    Canonical.normSq (direct.leftValue + direct.rightValue) at scalar
  simpa only [direct.leftValue_eq, direct.rightValue_eq,
    Norm.Basic.normSq_eq_canonical] using scalar

/-- Actual compared Points give the unflipped comparison of their same two-step model caches. -/
private theorem point_nearest {firstCount lastCount : Nat}
    {firstPatch : ContinuedNeighborhood curve.polynomial firstCount}
    {lastPatch : ContinuedNeighborhood curve.polynomial lastCount} {point : Canonical}
    (first : ContinuedNeighborhood.Point firstPatch point) (last : ContinuedNeighborhood.Point lastPatch point)
    (firstInside : firstPatch.box.Contains point) (lastInside : lastPatch.box.Contains point)
    (roots : NamedEquivalent first.certificate.value.name last.certificate.value.name) :
    normSq ((firstPatch.base.refine 2).value.eval point - (lastPatch.base.refine 2).value.eval point) ≤
      normSq ((firstPatch.base.refine 2).value.eval point + (lastPatch.base.refine 2).value.eval point) := by
  simpa only [Norm.Basic.normSq_eq_canonical] using
    first.equivalent_nearest last firstInside lastInside roots 2 2

/-- Propagate the original model sign through the literal covered parent and root-link spines.

Every head uses its original covering patch, and every junction consumes
its actual operational RootChain comparison. The initial sign and endpoint
root comparisons are retained input witnesses for this generic composition;
an original-model consumer must derive them from its seed and actual trace.
All auxiliary Point constructions occur only in this proposition's proof.
-/
theorem nearest_of_cover {modelBox : Box} (reference : OverlapReady curve.polynomial modelBox) :
    ∀ {parents : List (CenteredEdge curve differential)} (_covered : CoveredParents count parents)
      {start finish : LiftedPoint 2} (_chain : CenteredPathChain parents (start := start) (finish := finish))
      {firstName lastName : Named} (_roots : RootChain parents firstName lastName)
      (_contained : ∀ parent ∈ parents, modelBox.Contains (parent.edge.point 0) ∧
        modelBox.Contains (parent.edge.point 1))
      {initialCount : Nat} {initialPatch : ContinuedNeighborhood curve.polynomial initialCount}
      (initial : ContinuedNeighborhood.Point initialPatch start.coordinate)
      (_initialInside : initialPatch.box.Contains start.coordinate)
      (_referenceStart : modelBox.Contains start.coordinate)
      (_initialNear : normSq (reference.model.value.eval start.coordinate -
        (initialPatch.base.refine 2).value.eval start.coordinate) ≤
        normSq (reference.model.value.eval start.coordinate +
          (initialPatch.base.refine 2).value.eval start.coordinate))
      (_incoming : NamedEquivalent initial.certificate.value.name firstName)
      {finalCount : Nat} {finalPatch : ContinuedNeighborhood curve.polynomial finalCount}
      (actual : ContinuedNeighborhood.Point finalPatch finish.coordinate)
      (_actualInside : finalPatch.box.Contains finish.coordinate)
      (_outgoing : NamedEquivalent lastName actual.certificate.value.name),
      normSq (reference.model.value.eval finish.coordinate -
        (finalPatch.base.refine 2).value.eval finish.coordinate) ≤
        normSq (reference.model.value.eval finish.coordinate +
          (finalPatch.base.refine 2).value.eval finish.coordinate) := by
  intro parents covered
  induction covered with
  | nil =>
      intro start finish chain firstName lastName roots contained initialCount initialPatch initial initialInside
        referenceStart initialNear incoming finalCount finalPatch actual actualInside outgoing
      cases chain
      cases roots with
      | nil equivalent =>
          exact nearest_trans reference (ready initialPatch) (ready finalPatch) _ referenceStart
            (initialPatch.box_refines.contains initialInside) (finalPatch.box_refines.contains actualInside)
            initialNear (point_nearest initial actual initialInside actualInside
              (incoming.trans (equivalent.trans outgoing)))
  | @cons parent remaining patch finishInside covered ih =>
      intro start finish chain firstName lastName roots contained initialCount initialPatch initial initialInside
        referenceStart initialNear incoming finalCount finalPatch actual actualInside outgoing
      cases chain with
      | cons _ chainTail =>
          cases roots with
          | cons _ entry rootsTail =>
              have headInside := contained parent (List.mem_cons_self ..)
              let initialAt := ContinuedNeighborhood.Point.castPoint parent.edge.point_zero initial
              have initialAtInside : initialPatch.box.Contains (parent.edge.point 0) :=
                Eq.mpr (congrArg initialPatch.box.Contains parent.edge.point_zero) initialInside
              have initialAtNear : normSq (reference.model.value.eval (parent.edge.point 0) -
                  (initialPatch.base.refine 2).value.eval (parent.edge.point 0)) ≤
                  normSq (reference.model.value.eval (parent.edge.point 0) +
                    (initialPatch.base.refine 2).value.eval (parent.edge.point 0)) :=
                Eq.mpr (congrArg (fun point : Canonical =>
                  normSq (reference.model.value.eval point - (initialPatch.base.refine 2).value.eval point) ≤
                    normSq (reference.model.value.eval point + (initialPatch.base.refine 2).value.eval point))
                    parent.edge.point_zero) initialNear
              let first := ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (parent.edge.point 0)
                (patch.start_inside count)
              have incomingAt : NamedEquivalent initialAt.certificate.value.name firstName :=
                NamedEquivalent.transport
                  (ContinuedNeighborhood.Point.castPoint_name parent.edge.point_zero initial).symm rfl incoming
              let firstQuery := PreparedEdge.Query.build parent.edge 0 parent.edge.baseInside
              have firstRoots := patch.retainedQueryEquivalent count 0 parent.edge.baseInside firstQuery rfl
                (patch.start_inside count) first
              have nearStart := nearest_trans reference (ready initialPatch) (ready (patch.neighborhood count))
                (parent.edge.point 0) headInside.1 (initialPatch.box_refines.contains initialAtInside)
                ((patch.neighborhood count).box_refines.contains (patch.start_inside count)) initialAtNear
                (point_nearest initialAt first initialAtInside (patch.start_inside count)
                  (incomingAt.trans (entry.trans firstRoots)))
              have nearFinish := nearest_finish reference patch finishInside headInside.1 headInside.2 nearStart
              let last := ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (parent.edge.point 1)
                finishInside
              let tailPoint := ContinuedNeighborhood.Point.castPoint parent.edge.point_one.symm last
              have tailInside : (patch.neighborhood count).box.Contains
                  (parent.edge.segment.pointAt parent.edge.request.endpoint.parameter) :=
                Eq.mp (congrArg (patch.neighborhood count).box.Contains parent.edge.point_one) finishInside
              have tailReference : modelBox.Contains
                  (parent.edge.segment.pointAt parent.edge.request.endpoint.parameter) :=
                Eq.mp (congrArg modelBox.Contains parent.edge.point_one) headInside.2
              have tailNear : normSq (reference.model.value.eval
                    (parent.edge.segment.pointAt parent.edge.request.endpoint.parameter) -
                  ((patch.neighborhood count).base.refine 2).value.eval
                    (parent.edge.segment.pointAt parent.edge.request.endpoint.parameter)) ≤
                  normSq (reference.model.value.eval
                    (parent.edge.segment.pointAt parent.edge.request.endpoint.parameter) +
                    ((patch.neighborhood count).base.refine 2).value.eval
                      (parent.edge.segment.pointAt parent.edge.request.endpoint.parameter)) :=
                Eq.mp (congrArg (fun point : Canonical =>
                  normSq (reference.model.value.eval point -
                    ((patch.neighborhood count).base.refine 2).value.eval point) ≤
                    normSq (reference.model.value.eval point +
                      ((patch.neighborhood count).base.refine 2).value.eval point)) parent.edge.point_one) nearFinish
              let lastQuery := PreparedEdge.Query.build parent.edge 1 (by decide)
              have lastRoots := patch.retainedQueryEquivalent count 1 (by decide) lastQuery rfl finishInside last
              have tailRoots : NamedEquivalent tailPoint.certificate.value.name (parent.edge.rootName 1 (by decide)) :=
                NamedEquivalent.transport
                  (ContinuedNeighborhood.Point.castPoint_name parent.edge.point_one.symm last).symm rfl lastRoots.symm
              exact ih chainTail rootsTail (fun next member => contained next (List.mem_cons_of_mem parent member))
                tailPoint tailInside tailReference tailNear tailRoots actual actualInside outgoing

end Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents

end
