module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure
import Init.Data.List.Lemmas
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! The root-return join closes the retained paired radial boundary. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedClosedBoundary

open Purelib
open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
open Purelib.Data.Rat
open Purelib.Geometry.Path.Gaussian
open Purelib.Riemann.Integration
open Purelib.Riemann.Topology
open Purelib.Topology.Polygon
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request Plan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries (BoundaryBankRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts (ChartParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest (EndpointJoin
  JunctionRequest endpointJoin)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}

/-- The first actual parent in a nonempty direct chain begins at the original lifted start coordinate. -/
theorem first_coordinate {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {start finish : Lifted.Basic.LiftedPoint 2} (chain : PreparedDirectDyadicRefinements.DirectPathChain parents (start
      := start) (finish := finish))
    (positive : 0 < parents.length) : (parents[0]'positive).edge.point 0 = start.coordinate := by
  cases chain with
  | nil => exact (Nat.not_lt_zero _ positive).elim
  | cons parent _ => exact parent.edge.point_zero

/-- The last actual parent in a nonempty direct chain ends at the original lifted finish coordinate. -/
theorem last_coordinate {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {start finish : Lifted.Basic.LiftedPoint 2} (chain : PreparedDirectDyadicRefinements.DirectPathChain parents (start
      := start) (finish := finish))
    (positive : 0 < parents.length) :
    (parents[parents.length - 1]'(by omega0)).edge.point 1 = finish.coordinate := by
  induction chain with
  | nil => exact (Nat.not_lt_zero _ positive).elim
  | @cons parent remaining finish tail ih =>
      cases remaining with
      | nil => cases tail; exact parent.edge.point_one
      | cons next remaining => exact ih (Nat.zero_lt_succ _)

/-- The original root chain retains root equivalence from its initial owner to the first actual parent. -/
@[expose] def rootFirst : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    {first last : Gaussian.Name.Basic.Named} → PreparedRefinementRootChains.RootChain parents first last → (positive : 0
      < parents.length) →
    Gaussian.Equivalence.NamedEquivalent first ((parents[0]'positive).edge.rootName 0
      (parents[0]'positive).edge.baseInside)
  | _, _, _, .nil _, positive => (Nat.not_lt_zero _ positive).elim
  | _, _, _, .cons _ entry _, _ => entry

/-- The original root chain retains root equivalence from the last actual parent to its final owner. -/
@[expose] def rootLast : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    {first last : Gaussian.Name.Basic.Named} → (roots : PreparedRefinementRootChains.RootChain parents first last) →
    (positive : 0 < parents.length) →
    Gaussian.Equivalence.NamedEquivalent ((parents[parents.length - 1]'(by omega0)).edge.rootName 1 (by decide)) last
  | _, _, _, .nil _, positive => (Nat.not_lt_zero _ positive).elim
  | _, _, _, .cons _ _ (.nil returned), _ => returned
  | _, _, _, .cons _ _ tail@(.cons _ _ _), _ =>
    rootLast tail (Nat.zero_lt_succ _)

variable {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {parents : List
    (CenteredEdge curve differential)}
  {target requested : Coordinate} {minimum : Nat}
  {original : Request regular other parents
    target minimum} (request :
    BoundaryBankRequest original requested)

/-- The first bounded index of the retained nonempty original parent plan list. -/
@[expose] def firstParent (positive : 0 < original.plans.length) : Fin original.plans.length := ⟨0, positive⟩
/-- The last bounded index of the retained nonempty original parent plan list. -/
@[expose] def lastParent (positive : 0 < original.plans.length) : Fin original.plans.length := ⟨original.plans.length -
  1, by omega0⟩

/-- Join the actual last and first retained parents using the original physical closure and root-return evidence. -/
@[expose] def closingJoin (positive : 0 < original.plans.length)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain parents first last)
    (closed : start.coordinate = finish.coordinate) (returned : Gaussian.Equivalence.NamedEquivalent last first) :
    (BoundaryBankRequest.EndpointJoin request)
      (lastParent positive)
      (firstParent positive) := by
  have present : 0 < (original.plans.map Plan.parent).length := by rw [Data.List.Map.length_map]; exact positive
  have same : ((original.plans.map Plan.parent)[(original.plans.map Plan.parent).length - 1]'(by omega0)).edge.point 1 =
      ((original.plans.map Plan.parent)[0]'present).edge.point 0 := by
    obtain ⟨chain⟩ := chain
    have retained : PreparedDirectDyadicRefinements.DirectPathChain (original.plans.map Plan.parent) (start := start)
      (finish := finish) :=
      original.parents_eq.symm ▸ chain
    exact (last_coordinate retained present).trans
      (closed.symm.trans (first_coordinate retained
      present).symm)
  let retained : PreparedRefinementRootChains.RootChain (original.plans.map Plan.parent) first last :=
    original.parents_eq.symm ▸ roots
  let link := (rootLast retained present).trans
    (returned.trans (rootFirst retained present))
  simp only [Data.List.Map.length_map, -eq_self, -iff_self] at same link
  have lastMapped := Data.List.Map.getElem_map Plan.parent original.plans (original.plans.length - 1)
    (PairedClosedBoundary.lastParent positive).isLt (by
        rw [Data.List.Map.length_map];
        exact (PairedClosedBoundary.lastParent positive).isLt)
  have firstMapped := Data.List.Map.getElem_map Plan.parent original.plans 0 positive present
  rw [lastMapped, firstMapped] at same link
  apply BoundaryBankRequest.endpointJoin request
    (lastParent positive)
    (firstParent positive)
  · dsimp only [PairedParentCharts.ChartParent, PairedClosedBoundary.firstParent, PairedClosedBoundary.lastParent]
    convert same using 1; rfl
  · dsimp only [PairedParentCharts.ChartParent, PairedClosedBoundary.firstParent, PairedClosedBoundary.lastParent]
    convert link using 1; rfl

set_option genInjectivity false in
/-- The retained closing junction of the original parent boundary, with an explicit empty-bank case. -/
inductive ClosingPlan (tolerance : InverseRootPolynomial.Coordinate) where
  /-- The original plan bank is empty, so no closing junction is required. -/ | empty (absent : original.plans.length =
    0)
  /-- Retain the actual last-to-first endpoint join and its original coordinate comparison request. -/ | present
    (positive : 0 < original.plans.length)
      (joined : (BoundaryBankRequest.EndpointJoin request)
        (lastParent positive)
        (firstParent positive))
      (junction : (BoundaryBankRequest.JunctionRequest request)
        (lastParent positive)
        (firstParent positive) joined tolerance
        minimum)

constructive_injectivity ClosingPlan

/-- The actual closing request stage, or the original minimum when the retained parent bank is empty. -/
@[expose] def ClosingPlan.index {tolerance : InverseRootPolynomial.Coordinate} :
  (ClosingPlan request) tolerance → Nat
  | .empty _ => minimum
  | .present _ _ junction => junction.index

set_option genInjectivity false in
/-- The complete original internal and closing junction schedule.

Its common stage pays both retained request banks at the same positive junction tolerance. -/
structure ClosedRequest (junctionTarget : InverseRootPolynomial.Coordinate) where
  /-- The original request paying every actual internal parent junction. -/ linked :
    (PairedBoundaryClosure.LinkedRequest request) junctionTarget
  /-- The actual retained last-to-first closing request or its certified empty-bank case. -/ closing :
    (ClosingPlan request) junctionTarget
  /-- The retained complete junction tolerance is strictly positive. -/ positive : 0 < junctionTarget
  /-- The cached common stage paying the complete internal and closing junction requests. -/ index : Nat
  /-- The common stage is exactly the maximum of the original internal and closing schedules. -/ index_eq : index = max
    linked.index (closing.index request)

constructive_injectivity ClosedRequest

/-- Retain the original internal joins and root-return closing join, then cache their common paid stage. -/
@[expose] def ClosedRequest.build (junctionTarget : InverseRootPolynomial.Coordinate) (positive : 0 < junctionTarget)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain parents first last)
    (closed : start.coordinate = finish.coordinate) (returned : Gaussian.Equivalence.NamedEquivalent last first) :
    (ClosedRequest request) junctionTarget := by
  let linked := LinkedRequest.build request junctionTarget positive chain roots
  let closing : (ClosingPlan request) junctionTarget :=
    if present : 0 < original.plans.length then
    let joined := closingJoin request present chain
      roots closed returned
    .present present joined (JunctionRequest.build request
      (lastParent present)
      (firstParent present) joined junctionTarget
      positive minimum)
    else .empty (Nat.eq_zero_of_not_pos present)
  exact ⟨linked, closing, positive, max linked.index (closing.index request), rfl⟩

variable {request}

/-- The actual last-to-first paired radial edge area, or zero for the original empty bank. -/
@[expose] def ClosingPlan.connector {tolerance : InverseRootPolynomial.Coordinate} (closing :
  (ClosingPlan request) tolerance)
    (boundary : request.Evaluation) : Gaussian :=
  match closing with
  | .empty _ => 0
  | .present positive _ _ => Stokes.edgeArea
      ((Evaluation.radialValues boundary) ((Evaluation.lastCoordinate boundary)
        (lastParent positive)))
      ((Evaluation.radialValues boundary) ((Evaluation.firstCoordinate boundary)
        (firstParent positive)))

set_option genInjectivity false in
/-- The cached actual closing connector and radial boundary error with its retained strict tolerance bound. -/
structure ClosingPlan.Certificate {tolerance : InverseRootPolynomial.Coordinate} (closing :
  (ClosingPlan request) tolerance)
    (boundary : request.Evaluation) where
  /-- The cached actual last-to-first radial connector area. -/ connector : InverseRootPolynomial.Gaussian
  /-- The cached closing connector equals the actual retained last-to-first radial edge area. -/ connector_eq :
    connector = closing.connector boundary
  /-- The cached actual closing radial boundary error. -/ error : InverseRootPolynomial.Gaussian
  /-- The closing error is exactly the original outer radial boundary minus its retained closing connector. -/ error_eq
    : error = (Evaluation.outerBoundary boundary) - connector
  /-- The actual retained closing error satisfies the original strict junction tolerance. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq error < tolerance

constructive_injectivity ClosingPlan.Certificate

/-- Evaluate the retained closing junction against the actual acquired boundary at its paid floor and cache its
connector and error. -/
@[expose] def ClosingPlan.acquire {tolerance : InverseRootPolynomial.Coordinate} (closing :
  (ClosingPlan request) tolerance)
    (boundary : request.Evaluation) (later : closing.index request ≤ boundary.externalFloor)
    (positive : 0 < tolerance) (branch : HyperellipticReciprocal.originOrder curve = 1) : closing.Certificate boundary
      := by
  cases closing with
  | empty absent =>
      refine ⟨0, rfl, 0, ?_, ?_⟩
      · rw [(Evaluation.outerBoundary_empty boundary) absent, sub_self]
      · exact (Data.Gaussian.Norm.Basic.normSq_zero).trans_lt positive
  | present present joined junction =>
      let connector := Stokes.edgeArea
        ((Evaluation.radialValues boundary) ((Evaluation.lastCoordinate boundary)
          (lastParent present)))
        ((Evaluation.radialValues boundary) ((Evaluation.firstCoordinate boundary)
          (firstParent present)))
      let error := (Evaluation.junctionError boundary)
        (lastParent present)
        (firstParent present)
      have equal : error = (Evaluation.outerBoundary boundary) - connector := by
        rw [(Evaluation.outerBoundary_nonempty boundary) present]
        rfl
      exact ⟨connector, rfl, error, equal, junction.accurate boundary later branch⟩

/-- The complete original closed source boundary with restoration correction and all internal, parent and closing
connectors. -/
@[expose] def ClosedRequest.Boundary {junctionTarget : InverseRootPolynomial.Coordinate} (closed :
  (ClosedRequest request) junctionTarget)
    (boundary : request.Evaluation) : Gaussian :=
  boundary.sourceArea - boundary.correction + (Evaluation.internalConnectors boundary) +
    FiniteSum.Fin.sumFin (Evaluation.parentConnector boundary) + closed.closing.connector boundary

set_option genInjectivity false in
/-- The original linked acquisition and actual closing certificate with the complete closed area cached and bounded. -/
structure ClosedRequest.Certificate {junctionTarget : InverseRootPolynomial.Coordinate} (closed :
  (ClosedRequest request) junctionTarget) where
  /-- The acquired original linked parent boundary with its actual internal junction certificates. -/ retained :
    closed.linked.Certificate
  /-- The closing certificate consuming that exact retained original boundary acquisition. -/ closing :
    closed.closing.Certificate retained.boundary
  /-- The cached complete closed boundary area. -/ area : InverseRootPolynomial.Gaussian
  /-- The closed area cache is the original linked area minus its retained closing error. -/ area_eq : area =
    retained.area - closing.error
  /-- The area cache reads the complete original closed source-and-connector boundary. -/ boundary_eq : area =
    closed.Boundary retained.boundary
  /-- The actual closed area satisfies the combined original boundary and junction tolerance bound. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq area < 2 * (2 * (requested + junctionTarget) + junctionTarget)

constructive_injectivity ClosedRequest.Certificate

/-- Acquire the original linked boundary at the common stage, consume it for the closing certificate, and cache the
complete closed area. -/
@[expose] def ClosedRequest.acquire {junctionTarget : InverseRootPolynomial.Coordinate} (closed :
  (ClosedRequest request) junctionTarget)
    (branch : HyperellipticReciprocal.originOrder curve = 1) : closed.Certificate := by
  let retained := closed.linked.acquire closed.index ((Data.Nat.Order.le_max_left _ _).trans_eq closed.index_eq.symm)
    branch
  let closing := closed.closing.acquire retained.boundary
    ((Data.Nat.Order.le_max_right _ _).trans_eq closed.index_eq.symm) closed.positive branch
  let area := retained.area - closing.error
  have boundaryEq : area = closed.Boundary retained.boundary := by
    dsimp only [area, -eq_self, -iff_self]
    rw [retained.boundary_eq, closing.error_eq, closing.connector_eq]
    unfold Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.linkedBoundary
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedClosedBoundary.ClosedRequest.Boundary
    ring1
  have bound := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two retained.area closing.error).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct retained.bounded closing.bounded))
  exact ⟨retained, closing, area, rfl, boundaryEq, bound⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedClosedBoundary
