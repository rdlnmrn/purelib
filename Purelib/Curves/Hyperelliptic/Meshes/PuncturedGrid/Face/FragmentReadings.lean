module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedPathTrace
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Segment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Riemann.Comparison.RectangularSharedPrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Branches.ContainedPreparedPolynomialSheets
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition

open Purelib.Polynomial

open Purelib.Riemann.Branches.RectangularSheetGauge

open Purelib.Riemann.Comparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedParentSplitting

open Purelib.Riemann.Integration.RectangularSharedPrimitives

open Purelib.Riemann.Meshes

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.OwnerSeededInverseRoot

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

@[expose] public section

/-!
# Actual-request primitive readings on automatically split mesh fragments

Every fragment uses its cached cell and mesh vertices. Interior query traces
identify the actual request's sheet at the fragment start; the endpoint bounds
of the retained request imply containment throughout the original edge. Only
scalar residual charges and shared primitive values are read at runtime.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings

open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentPiece SegmentSplit)
open Purelib.Riemann.Integration.PreparedParentSplitting (ParentSplits PreparedSplitMesh prepared_point_eq)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (ParentReached)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {columns rows : Nat} {geometry : Geometry
    columns rows}
  {patch : RectangularPatch models.bounds (models.frame.owners sheet)
    geometry}
  {differential : Differential genus}

set_option genInjectivity false in
/-- One cache per coarse model cell, shared by all fragments and requests. The inverse ceiling is common because
restriction retains the clearance. -/
structure FragmentBounds (patch : RectangularPatch models.bounds (models.frame.owners sheet)
  geometry)
    (differential : Differential genus)
    (numeratorPolynomial : CoefficientPolynomial := differentialNumerator differential) where
  /-- The cached differential numerator ceiling at every original coarse model cell. -/ numerator :
    Data.Vector (Data.Vector InverseRootPolynomial.Coordinate (rows + 1)) (columns + 1)
  /-- Each cached numerator ceiling is the supplied numerator's finite polynomial bound on that cell. -/ numerator_eq
    : ∀ column row, numerator column row =
    Dense.Gaussian.Bounds.Box.denseEvalNormBound numeratorPolynomial (geometry.box column row)
  /-- The common inverse ceiling retained from the original face clearance. -/ inverse :
    InverseRootPolynomial.Coordinate
  /-- The common inverse ceiling is exactly one plus four divided by the original clearance bound. -/ inverse_eq :
    inverse = 1 + 4 / face.clearance.bound

constructive_injectivity FragmentBounds

namespace FragmentBounds

/-- Cache the supplied polynomial numerator ceiling on every retained coarse cell and the original inverse ceiling. -/
def buildNumerator (patch : RectangularPatch models.bounds (models.frame.owners sheet) geometry)
    (differential : Differential genus) (numerator : CoefficientPolynomial) :
    FragmentBounds patch differential (numeratorPolynomial := numerator) where
  numerator := Data.Vector.Basic.vectorOfFn fun column => Data.Vector.Basic.vectorOfFn fun row =>
    Dense.Gaussian.Bounds.Box.denseEvalNormBound numerator (geometry.box column row)
  numerator_eq := fun column row => by rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  inverse := 1 + 4 / face.clearance.bound
  inverse_eq := rfl

/-- Cache the original differential numerator through the same polynomial bound constructor. -/
def build (patch : RectangularPatch models.bounds (models.frame.owners sheet) geometry)
    (differential : Differential genus) : FragmentBounds patch differential :=
  buildNumerator patch differential (differentialNumerator differential)

/-- Read the same original cell's cached polynomial numerator and inverse ceiling as its overlap certificate. -/
def atCell {numeratorPolynomial : CoefficientPolynomial}
    (bounds : FragmentBounds patch differential (numeratorPolynomial := numeratorPolynomial))
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    PrimitiveOverlapBounds (face.clearance.restrict (patch.cell_refines column row)) numeratorPolynomial :=
  ⟨bounds.numerator column row, bounds.numerator_eq column row, bounds.inverse, bounds.inverse_eq⟩

/-- Charge the actual face refinement and a supplied original source residual with the retained polynomial ceilings. -/
def residualCharge {numeratorPolynomial : CoefficientPolynomial}
    (bounds : FragmentBounds patch differential (numeratorPolynomial := numeratorPolynomial))
    {first last : InverseRootPolynomial.Gaussian}
    (piece : SegmentPiece geometry first last)
    (sourceResidual : Coordinate) (index : Nat) : Coordinate :=
  12 * (quarterRadius (patch.transported.cell piece.column piece.row).model.bound (index + 2) + sourceResidual) *
    (bounds.numerator piece.column piece.row * bounds.inverse) * Basic.normSq (piece.lastPoint - piece.firstPoint)

/-- Compute the scalar residual charge for the actual retained fragment, original request index and shared grid stage.
-/
def charge (bounds : FragmentBounds patch differential)
  {parent : CenteredEdge curve differential}
    (piece : SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1))
    {count : Nat} {target : InverseRootPolynomial.Coordinate} (request : LocalRequest parent
      count target) (index : Nat) : Fraction.Rational :=
  bounds.residualCharge piece
    (quarterRadius request.neighborhood.base.model.bound request.request.index) index

/-- Every unit-interval point of the original prepared parent lies inside its retained request neighborhood. -/
private theorem request_contains {parent : CenteredEdge curve differential} {count : Nat}
  {target : InverseRootPolynomial.Coordinate}
    (request : LocalRequest parent count target) (fraction : InverseRootPolynomial.Coordinate)
      (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    request.neighborhood.box.Contains (parent.edge.point fraction) := by
  rw [PreparedParentSplitting.prepared_point_eq parent fraction, PreparedSegmentCuts.point_eq_line]
  have first : request.neighborhood.box.Contains (parent.edge.point 0) := by
    rw [request.neighborhood_eq]
    exact request.patch.start_inside count
  exact Rational.Box.contains_line first request.finishInside inside

/-- The comparison uses the request's original polynomial index and actual interior query root. Every local geometric
and sign premise is constructed. -/
theorem local_increment_le (bounds : FragmentBounds
  patch differential)
    {parent : CenteredEdge curve differential} (piece :
      SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1))
    {index : Nat} (primitives : Primitives (Transitions.oriented (patch.sheets.refine
      index).transitions
      (patch.sheets.refine index).gauge) (PreparedPrimitiveSamples.differentialNumerator differential))
    (reached : ParentReached face.cell.box (models.frame.owners sheet) parent)
    {count : Nat} {target : InverseRootPolynomial.Coordinate} (request : LocalRequest parent
      count target) :
    Basic.normSq ((primitives.value piece.column piece.row piece.lastPoint -
      primitives.value piece.column piece.row piece.firstPoint) -
      (request.request.model.primitive.value.eval piece.lastPoint - request.request.model.primitive.value.eval
        piece.firstPoint)) ≤
        bounds.charge piece request index := by
  have firstEq : piece.firstPoint = parent.edge.point piece.interval.lower :=
    piece.first_eq.trans (PreparedParentSplitting.prepared_point_eq parent _).symm
  have lastEq : piece.lastPoint = parent.edge.point piece.interval.upper :=
    piece.last_eq.trans (PreparedParentSplitting.prepared_point_eq parent _).symm
  have firstInside : 0 ≤ piece.interval.lower ∧ piece.interval.lower ≤ 1 :=
    ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩
  have lastInside : 0 ≤ piece.interval.upper ∧ piece.interval.upper ≤ 1 :=
    ⟨piece.within.1.trans piece.interval.ordered.le, piece.within.2⟩
  have rightStart := request_contains
    request piece.interval.lower firstInside
  have rightFinish := request_contains
    request piece.interval.upper lastInside
  rcases request with ⟨localPatch, neighborhood, neighborhoodEq, request, finishInside⟩
  subst neighborhood
  have bounded := TransportedFaceInverseModels.TransportedCell.prepared_subedge_primitive_increment_le
    (pairs := 0) (numerator := differentialNumerator differential)
    (patch.transported.cell piece.column piece.row) differential parent
    piece.interval.lower piece.interval.upper firstInside (firstEq ▸ piece.first_inside)
    localPatch count index request.index
      (by
        intro otherCount otherPatch otherInside otherSample roots otherIndex
        exact (patch.transported.cell piece.column piece.row).prepared_query_aligned
          (entered := TracedPath.build
            (Polynomial.Geometry.ClearPath.nil (polynomial := curve.polynomial)
              (ambient := face.cell.box) face.cell.box.anchor) (.nil face.cell.box.anchor) _)
          face.cell.box.contains_anchor differential (Branches.BranchIsolation.degreePositive curve)
          (LoopMonodromy.BranchCellBank.referenceAt bank _ (face.cell.anchor_mem face.member)).toLoop
          parent reached piece.interval.lower firstInside (firstEq ▸ piece.first_inside) index
          otherPatch otherInside otherSample roots otherIndex)
      (primitives.dense piece.column piece.row)
    (patch.primitive_coefficient_eq (pairs := 0)
      (entered := TracedPath.build
        (Polynomial.Geometry.ClearPath.nil (polynomial := curve.polynomial)
          (ambient := face.cell.box) face.cell.box.anchor)
        (.nil face.cell.box.anchor) _)
      face.cell.box.contains_anchor differential
      (Branches.BranchIsolation.degreePositive curve)
      (LoopMonodromy.BranchCellBank.referenceAt bank _
        (face.cell.anchor_mem face.member)).toLoop
      primitives piece.column piece.row)
    request.model (bounds.atCell piece.column piece.row)
    (lastEq ▸ piece.last_inside) rightStart rightFinish
  rewrite [PrimitiveOverlapBounds.weight_zero] at bounded
  rw [← firstEq, ← lastEq] at bounded
  exact bounded.trans_eq (by
    change _ = 12 * (Geometric.Basic.quarterRadius _ (index + 2) + Geometric.Basic.quarterRadius _ request.index) * _ *
      _
    rw [Model.refine_bound, SeededNeighborhood.refine,
      Model.refine_bound]
    rfl)

end FragmentBounds

variable {globalBounds : PrimitiveOverlapBounds face.clearance
  (PreparedPrimitiveSamples.differentialNumerator differential)}
  {tolerance : InverseRootPolynomial.Coordinate} {gridRequest :
    GridPrimitiveAccuracy globalBounds columns tolerance}
  {primitives : Primitives
    (Transitions.oriented
    (patch.sheets.refine gridRequest.index).transitions (patch.sheets.refine gridRequest.index).gauge)
    (PreparedPrimitiveSamples.differentialNumerator differential)}
  {anchors : PrimitiveAnchors primitives} {offsets :
    LinearAlgebra.Grid.Offsets anchors.edges}
  {cuts : GridCuts geometry} {parents : List
    (CenteredEdge curve differential)} {extra : List
    InverseRootPolynomial.Gaussian}
  {mesh : PreparedSplitMesh cuts parents extra}

set_option genInjectivity false in
/-- Cached shared reading and its error against the unchanged parent request, on one of the actual automatically
assigned fragments. -/
structure FragmentReading (bounds : FragmentBounds patch
  differential)
    (readings : SharedPrimitiveValues anchors offsets mesh.mesh.surface)
    {parent : CenteredEdge curve differential} {count : Nat} {target :
      InverseRootPolynomial.Coordinate}
    (request : LocalRequest parent count target)
    (piece : SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1)) where
  /-- The original fragment's retained endpoint indices in the shared split mesh. -/ contact : PreparedSplitMesh.Contact
    mesh piece
  /-- The cached difference of the two original shared primitive readings. -/ value : InverseRootPolynomial.Gaussian
  /-- The cached value is exactly the retained last reading minus the first reading. -/ value_eq : value =
    readings.values contact.last - readings.values contact.first
  /-- The cached error bound comparing this original shared reading with the retained request primitive. -/ charge :
    InverseRootPolynomial.Coordinate
  /-- The cached error combines the original shared-grid bound and twice the actual request comparison charge. -/
    charge_eq : charge = 32 * gridRequest.globalBound + 2 * bounds.charge piece request gridRequest.index
  /-- The retained shared fragment reading satisfies its cached error against the unchanged original request primitive.
  -/
  accurate : Basic.normSq (value - (request.request.model.primitive.value.eval
    piece.lastPoint -
    request.request.model.primitive.value.eval piece.firstPoint)) ≤ charge

constructive_injectivity FragmentReading

namespace FragmentReading

/-- Lookup and scalar arithmetic only: the auxiliary query traces and inverse-model comparisons occur in erased proofs,
not executable fields. -/
def build (bounds : FragmentBounds patch differential)
    (readings : SharedPrimitiveValues anchors offsets mesh.mesh.surface)
    {parent : CenteredEdge curve differential} {count : Nat} {target :
      InverseRootPolynomial.Coordinate}
    (request : LocalRequest parent count target)
    {split : SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1)} (member :
      ParentSplits.Member split mesh.splits)
    (piece : SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1)) (present :
      piece ∈ split.pieces)
    (reached : ParentReached face.cell.box (models.frame.owners sheet) parent) :
    FragmentReading (gridRequest := gridRequest) bounds
      readings request piece :=
  let contact := mesh.contact member piece present
  { contact := contact
    value := readings.values contact.last - readings.values contact.first
    value_eq := rfl
    charge := 32 * gridRequest.globalBound + 2 * bounds.charge piece request gridRequest.index
    charge_eq := rfl
    accurate := by
      have ownership := GridPrimitiveAccuracy.shared_local_increment_bound
        gridRequest readings patch.cell_refines piece.column piece.row
        contact.first contact.last (contact.first_eq.symm ▸ piece.first_inside) (contact.last_eq.symm ▸
          piece.last_inside)
      rw [contact.first_eq, contact.last_eq] at ownership
      have analytic := bounds.local_increment_le piece primitives reached request
      let localValue := primitives.value piece.column piece.row piece.lastPoint - primitives.value piece.column
        piece.row piece.firstPoint
      let actualValue := request.request.model.primitive.value.eval piece.lastPoint -
        request.request.model.primitive.value.eval piece.firstPoint
      have identity : readings.values contact.last - readings.values contact.first - actualValue =
          (readings.values contact.last - readings.values contact.first - localValue) + (localValue - actualValue) := by
            ring1
      change Basic.normSq (readings.values contact.last - readings.values contact.first -
        actualValue) ≤ _
      rw [identity]
      have triangle := Bounds.normSq_add_le_two
        (readings.values contact.last - readings.values contact.first - localValue) (localValue - actualValue)
      simp only [Basic.normSq_eq_canonical] at triangle ownership analytic
      rw [Basic.normSq_eq_canonical]
      exact triangle.trans
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct ownership analytic)
          (by decide : (0 : Fraction.Rational) ≤ 2)).trans_eq (by ring1)) }

end FragmentReading

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
