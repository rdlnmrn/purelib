module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentAccuracy
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Geometry.Path.Gaussian

open Purelib.Integration.Polynomial.Rectangle.Accuracy

open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment

open Purelib.LinearAlgebra.Grid

open Purelib.Riemann.Branches.RectangularSheetGauge

open Purelib.Riemann.Comparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularPrimitiveGluing

open Purelib.Riemann.Integration.RectangularPrimitiveModels

open Purelib.Riemann.Integration.RectangularSharedPrimitives

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests

open Purelib.Riemann.Topology.PreparedRootSafeCycleStates

@[expose] public section

/-!
# Automatic requested comparisons on an actual contained prepared mesh

All numerical accuracies are selected internally. The existing covered
parents, requests, and shared finite mesh are retained; no new path or root
owner is substituted. This is the local clear-face construction consumed
by the future global cut-surface assembly, not an A/B boundary identity.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Integration.PreparedParentSplitting (PreparedSplitMesh)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums (FragmentSum fragmentSum)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (ParentReached)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest IndicesAbove)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests (PeriodSample)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {columns rows : Nat} {geometry : Geometry
    columns rows}
  {patch : RectangularPatch models.bounds (models.frame.owners sheet)
    geometry}
  {differential : Differential genus} {cuts :
    GridCuts geometry}
  {parents : List (CenteredEdge curve differential)} {extra :
    List Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}

set_option genInjectivity false in
/-- The numerical fields are cached together with their actual request and mesh readback. Alternative generated caches
use these same exact contracts. -/
structure RequestedFragments (mesh : PreparedParentSplitting.PreparedSplitMesh cuts parents extra) (bounds :
  FragmentReadings.FragmentBounds patch differential)
    (globalBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
      (PreparedPrimitiveSamples.differentialNumerator differential)) (count : Nat) (target :
      InverseRootPolynomial.Coordinate) where
  /-- The cached fragment accuracy request on the original mesh's exact piece count. -/ budget :
    Fragment.FragmentAccuracy globalBounds columns mesh.splits.pieceCount (target / 4)
  /-- The retained controlled primitive request on the original parent list. -/ request :
    PreparedControlledPrimitiveRequests.ControlledSumRequest parents count (target / 4)
  /-- The original parent request floor pays the retained fragment budget's minimum stage. -/ minimum_le :
    budget.minimumIndex ≤ request.minimumIndex
  /-- The cached differential primitives on the original face patch refined at the requested grid stage. -/ primitives :
    RectangularPrimitiveModels.Primitives (Transitions.oriented (patch.sheets.refine budget.grid.index).transitions
    (patch.sheets.refine budget.grid.index).gauge) (PreparedPrimitiveSamples.differentialNumerator differential)
  /-- The retained primitive anchors for these exact original face polynomials. -/ anchors :
    RectangularPrimitiveGluing.PrimitiveAnchors primitives
  /-- The retained shared offsets on the actual primitive-anchor edge bank. -/ offsets : LinearAlgebra.Grid.Offsets
    anchors.edges
  /-- The cached shared primitive values on the original finite split surface. -/ readings :
    RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets mesh.mesh.surface
  /-- The cached original fragment sum tied to the retained mesh, readings and actual parent requests. -/ summary :
    FragmentSums.FragmentSum (gridRequest := budget.grid) bounds readings mesh.splits request.requests
  /-- The retained original fragment error sum is strictly below one quarter of the requested target. -/ bound_lt :
    summary.bound < target / 4

constructive_injectivity RequestedFragments

namespace RequestedFragments

variable {mesh : PreparedSplitMesh cuts parents extra} {bounds :
  FragmentBounds patch differential}
  {globalBounds : PrimitiveOverlapBounds face.clearance
    (Purelib.Riemann.Readings.PreparedPrimitiveSamples.differentialNumerator differential)} {count : Nat} {target :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- Every original retained request above a later polynomial floor is also above an earlier floor. -/
public theorem indices_of_le {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {tolerance
  : InverseRootPolynomial.Coordinate} {first last : Nat}
    (order : first ≤ last) (requests : UniformPreparedRequests.RequestedParents count tolerance parents)
    (later : PreparedControlledPrimitiveRequests.IndicesAbove last requests) :
      PreparedControlledPrimitiveRequests.IndicesAbove first requests := by
  induction requests with
  | nil => trivial
  | cons request remaining ih => exact ⟨order.trans later.1, ih later.2⟩

/-- Compare supplied primitive data with one retained prepared request. Its parent polynomial floor may pay several
different face budgets. The constructor reads both caches and never acquires a replacement request. -/
def ofPrimitives (mesh : PreparedParentSplitting.PreparedSplitMesh cuts parents extra) (bounds :
  FragmentReadings.FragmentBounds patch differential)
    (globalBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
      (PreparedPrimitiveSamples.differentialNumerator differential))
    (budget : Fragment.FragmentAccuracy globalBounds columns mesh.splits.pieceCount (target / 4))
    (request : PreparedControlledPrimitiveRequests.ControlledSumRequest parents count (target / 4)) (minimum :
      budget.minimumIndex ≤ request.minimumIndex)
    (primitives : RectangularPrimitiveModels.Primitives (Transitions.oriented (patch.sheets.refine
      budget.grid.index).transitions (patch.sheets.refine budget.grid.index).gauge)
      (PreparedPrimitiveSamples.differentialNumerator differential))
    (anchors : RectangularPrimitiveGluing.PrimitiveAnchors primitives) (offsets : LinearAlgebra.Grid.Offsets
      anchors.edges)
    (reached : ∀ parent ∈ parents, PreparedFaceTracePrefixes.ParentReached face.cell.box (models.frame.owners sheet)
      parent) :
    RequestedFragments mesh bounds globalBounds count
      target :=
  let readings := SharedPrimitiveValues.build anchors offsets mesh.mesh.surface
  let summary := FragmentSums.fragmentSum mesh bounds readings request.requests reached
  { budget := budget, request := request, minimum_le := minimum
    primitives := primitives, anchors := anchors, offsets := offsets, readings := readings, summary := summary
    bound_lt := summary.bound_lt rfl
      (indices_of_le minimum
      request.requests request.indices_ge) }

/-- The geometric cover is reused. Index selection precedes every polynomial construction; the final fold reads only
cached values and scalar charges. -/
def acquire (mesh : PreparedParentSplitting.PreparedSplitMesh cuts parents extra) (bounds :
  FragmentReadings.FragmentBounds patch differential)
    (globalBounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds face.clearance
      (PreparedPrimitiveSamples.differentialNumerator differential))
    (covered : UniformPreparedMesh.CoveredParents count parents) (proper : PreparedDyadicRefinements.AllParentsProper
      parents)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target)
    (reached : ∀ parent ∈ parents, PreparedFaceTracePrefixes.ParentReached face.cell.box (models.frame.owners sheet)
      parent) :
    RequestedFragments mesh bounds globalBounds count
      target :=
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let budget := FragmentAccuracy.build globalBounds columns mesh.splits.pieceCount (target / 4) quarterPositive
  let request := ControlledSumRequest.acquire covered proper (target / 4) quarterPositive budget.minimumIndex
  have minimumEq : request.minimumIndex = budget.minimumIndex := ControlledSumRequest.acquire_minimumIndex ..
  let sheets := patch.sheets.refine budget.grid.index
  let primitives := Primitives.build (Transitions.oriented sheets.transitions sheets.gauge)
    (PreparedPrimitiveSamples.differentialNumerator differential)
  let anchors := PrimitiveAnchors.build primitives
  let offsets := anchors.offsets
  ofPrimitives mesh bounds
    globalBounds budget request minimumEq.symm.le primitives anchors offsets reached

/-- The actual retained shared-fragment sum differs from the original controlled primitive request by less than one
quarter target. -/
theorem accurate (prepared : RequestedFragments mesh
  bounds globalBounds count target) :
    Data.Gaussian.Norm.Basic.normSq (prepared.summary.value - prepared.request.primitiveSum) < target / 4 :=
  prepared.summary.controlled_accurate.trans_lt prepared.bound_lt

/-- Exact shared-vertex telescoping retains the actual prepared endpoints; all analytic discrepancies have already been
paid in the requested bound. -/
theorem value_eq_increment (prepared :
  RequestedFragments mesh bounds globalBounds count
  target)
    {start finish : Lifted.Basic.LiftedPoint 2} (chain : PreparedDirectDyadicRefinements.CenteredPathChain parents
      (start := start) (finish := finish))
    (first last : Fin mesh.mesh.surface.mesh.vertices.length)
    (firstEq : mesh.mesh.surface.mesh.coordinate first = start.coordinate)
    (lastEq : mesh.mesh.surface.mesh.coordinate last = finish.coordinate) :
    prepared.summary.value = prepared.readings.values last - prepared.readings.values first :=
  prepared.summary.value_eq_increment chain first last firstEq lastEq

/-- Composition with the existing period sample has no numerical smallness premise or fixed error floor. The actual
parent geometry remains the index. -/
theorem period_accurate {source : Differentials.Basic.Differential genus} {root : Gaussian.Name.Basic.Named}
    {initial : PreparedRefinementRootEndpoints.RootClosedState curve source root} {targets : List
      (Differentials.Basic.Differential genus)}
    {mesh : PreparedParentSplitting.PreparedSplitMesh cuts (initial.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge differential)) extra}
    (prepared : RequestedFragments mesh bounds
      globalBounds count target) {minimumStage : Nat}
    (sample : PreparedPeriodPrimitiveRequests.PeriodSample initial targets differential prepared.request minimumStage) :
    Data.Gaussian.Norm.Basic.normSq (prepared.summary.value - sample.sample) < target := by
  have bounded := prepared.summary.period_accurate sample
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2) prepared.bound_lt
  have paid : 2 * (target / 4) + 2 * (target / 4) = target := by
    rw [show 2 * (target / 4) + 2 * (target / 4) = (target / 4) * 4 by ring1]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  exact bounded.trans ((Fraction.Order.Arithmetic.add_lt_add_right_direct scaled (2 * (target / 4))).trans_eq paid)

end RequestedFragments

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
