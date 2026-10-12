module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Segment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PreparedComparison
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.GluedPrimitives
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Riemann.Readings.UniformPreparedRequests
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition

open Purelib.Riemann.Branches.RectangularSheetGauge

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.OwnerSeededInverseRoot

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

@[expose] public section

/-! The retained fragment cell compares arbitrary fine queries with the
original parent primitive. No new subedge or primitive is prepared. -/
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentPiece)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.PreparedParentSplitting (prepared_point_eq)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (ParentReached)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
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
  {differential : Differential genus}

/-- The retained cell and original request residual charge per squared query displacement. -/
def queryDensity
    (bounds : FragmentReadings.FragmentBounds patch differential) (column : Fin (columns + 1)) (row : Fin (rows + 1))
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {count : Nat} {target :
      InverseRootPolynomial.Coordinate}
    (request : UniformPreparedRequests.LocalRequest parent count target) (index : Nat) : Fraction.Rational :=
  12 * (Geometric.Basic.quarterRadius (patch.transported.cell column row).model.bound (index + 2) +
    Geometric.Basic.quarterRadius request.neighborhood.base.model.bound request.request.index) *
      (bounds.numerator column row * bounds.inverse)

/-- The original residual and coefficient ceilings make the query discrepancy density nonnegative. -/
theorem queryDensity_nonnegative
    (bounds : FragmentReadings.FragmentBounds patch differential)
    (column : Fin (columns + 1)) (row : Fin (rows + 1))
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {count : Nat} {target :
      InverseRootPolynomial.Coordinate}
    (request : UniformPreparedRequests.LocalRequest parent count target) (index : Nat) :
    0 ≤ queryDensity bounds column row request index :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Geometric.Basic.quarterRadius_nonneg (patch.transported.cell column row).model.bound_nonnegative _)
        (Geometric.Basic.quarterRadius_nonneg request.neighborhood.base.model.bound_nonnegative _)))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (bounds.atCell column row).numeratorUpper_nonnegative
      (bounds.atCell column row).inverseUpper_positive.le)

/-- A fixed query density ceiling from the original coarse cell and shared coefficient bounds, independent of later
refinement. -/
def uniformQueryDensity
    (bounds : FragmentReadings.FragmentBounds patch differential)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) : Fraction.Rational :=
  12 * ((patch.transported.cell column row).model.bound + 1 / 16) *
    (bounds.numerator column row * bounds.inverse)

/-- Every original request and shared cell stage satisfies the retained uniform query density ceiling. -/
theorem queryDensity_uniform_le
    (bounds : FragmentReadings.FragmentBounds patch differential)
    (column : Fin (columns + 1)) (row : Fin (rows + 1))
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {count : Nat} {target :
      InverseRootPolynomial.Coordinate}
    (request : UniformPreparedRequests.LocalRequest parent count target) (index : Nat) :
    queryDensity bounds column row request index ≤
      uniformQueryDensity bounds column row := by
  have face := Geometric.Basic.quarterRadius_le_scale (patch.transported.cell column row).model.bound_nonnegative (index
    + 2)
  have source := (Geometric.Basic.quarterRadius_le_scale request.neighborhood.base.model.bound_nonnegative
    request.request.index).trans request.neighborhood.base.model.bound_small
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct face source) (by decide))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (bounds.atCell column row).numeratorUpper_nonnegative
      (bounds.atCell column row).inverseUpper_positive.le)

set_option genInjectivity false in
/-- A finite face-refinement request retains the irreducible contribution of the already chosen source primitive request
explicitly. -/
structure QueryTail (bounds : FragmentReadings.FragmentBounds patch differential)
    (column : Fin (columns + 1)) (row : Fin (rows + 1))
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {count : Nat} {target :
      InverseRootPolynomial.Coordinate}
    (request : UniformPreparedRequests.LocalRequest parent count target) (radius : InverseRootPolynomial.Coordinate)
      where
  /-- The cached face-refinement stage selected for the original requested radius. -/ index : Nat
  /-- The face stage is the first original model quarter-radius search result below the requested radius. -/ index_eq :
    index = Search.firstQuarterBelow (patch.transported.cell column row).model.bound 0 radius
  /-- The retained residual contribution of the already selected original source request. -/ sourceRadius :
    InverseRootPolynomial.Coordinate
  /-- The source contribution is exactly its original model quarter-radius at the retained request index. -/ source_eq :
    sourceRadius = Geometric.Basic.quarterRadius request.neighborhood.base.model.bound request.request.index
  /-- The cached query discrepancy density ceiling at all later face stages. -/ ceiling :
    InverseRootPolynomial.Coordinate
  /-- The ceiling combines the requested face radius and unchanged source residual with the original coefficient bounds.
  -/
  ceiling_eq : ceiling = 12 * (radius + sourceRadius) * (bounds.numerator column row * bounds.inverse)
  /-- Every later shared face stage satisfies the cached query density ceiling. -/ accurate : ∀ later, index ≤ later →
    queryDensity bounds column row request later ≤
    ceiling

constructive_injectivity QueryTail

/-- If the original source residual fits the requested radius, the retained query ceiling is at most twice the radius
contribution. -/
theorem QueryTail.ceiling_le {bounds : FragmentReadings.FragmentBounds patch differential}
    {column : Fin (columns + 1)} {row : Fin (rows + 1)}
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {count : Nat} {target radius :
      InverseRootPolynomial.Coordinate}
    {request : UniformPreparedRequests.LocalRequest parent count target} (tail :
      QueryTail bounds column row request radius)
    (sourceSmall : tail.sourceRadius ≤ radius) :
    tail.ceiling ≤ 24 * radius * (bounds.numerator column row * bounds.inverse) := by
  rw [tail.ceiling_eq]
  have nonnegative : 0 ≤ bounds.numerator column row * bounds.inverse :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (bounds.atCell column row).numeratorUpper_nonnegative
      (bounds.atCell column row).inverseUpper_positive.le
  have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (le_refl radius) sourceSmall) (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 12))
    nonnegative
  exact bounded.trans_eq (by ring1)

/-- The paid query-tail ceiling is bounded by the requested radius times the original uniform density scale. -/
theorem QueryTail.ceiling_le_uniform {bounds : FragmentReadings.FragmentBounds patch differential}
    {column : Fin (columns + 1)} {row : Fin (rows + 1)}
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {count : Nat} {target radius :
      InverseRootPolynomial.Coordinate}
    {request : UniformPreparedRequests.LocalRequest parent count target} (tail :
      QueryTail bounds column row request radius)
    (nonnegative : 0 ≤ radius) (sourceSmall : tail.sourceRadius ≤ radius) :
    tail.ceiling ≤ 32 * radius *
      uniformQueryDensity bounds column row := by
  have scaleNonnegative : 0 ≤ bounds.numerator column row * bounds.inverse :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (bounds.atCell column row).numeratorUpper_nonnegative
      (bounds.atCell column row).inverseUpper_positive.le
  have extra : 0 ≤ 384 * radius * (patch.transported.cell column row).model.bound *
      (bounds.numerator column row * bounds.inverse) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) nonnegative)
        (patch.transported.cell column row).model.bound_nonnegative) scaleNonnegative
  exact (tail.ceiling_le sourceSmall).trans ((le_add_of_nonneg_right extra).trans_eq (by
    unfold uniformQueryDensity
    have scalar : (384 : InverseRootPolynomial.Coordinate) * (1 / 16) = 24 := by decide +kernel
    symm
    calc
      _ = 384 * radius * (patch.transported.cell column row).model.bound * (bounds.numerator column row *
        bounds.inverse) +
          (384 * (1 / 16)) * radius * (bounds.numerator column row * bounds.inverse) := by ring1
      _ = _ := by rw [scalar]; ring1))

/-- Select a finite face-refinement stage while retaining the unchanged original source-request residual contribution
explicitly. -/
def queryTail (bounds : FragmentReadings.FragmentBounds patch differential)
    (column : Fin (columns + 1)) (row : Fin (rows + 1))
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {count : Nat} {target :
      InverseRootPolynomial.Coordinate}
    (request : UniformPreparedRequests.LocalRequest parent count target) (radius : InverseRootPolynomial.Coordinate)
      (positive : 0 < radius) :
    QueryTail bounds column row request radius := by
  let index := Search.firstQuarterBelow (patch.transported.cell column row).model.bound 0 radius
  let sourceRadius := Geometric.Basic.quarterRadius request.neighborhood.base.model.bound request.request.index
  let ceiling := 12 * (radius + sourceRadius) * (bounds.numerator column row * bounds.inverse)
  refine ⟨index, rfl, sourceRadius, rfl, ceiling, rfl, ?_⟩
  intro later after
  have chosen := Search.firstQuarterBelow_accurate
    (patch.transported.cell column row).model.bound
    (patch.transported.cell column row).model.bound_nonnegative 0 radius positive
  have small := (quarterRadius_antitone
    (patch.transported.cell column row).model.bound_nonnegative
    (after.trans (Nat.le_add_right later 2))).trans chosen.le
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct small (le_refl sourceRadius)) (by decide))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (bounds.atCell column row).numeratorUpper_nonnegative
      (bounds.atCell column row).inverseUpper_positive.le)

/-- Both query parameters may coincide or occur in either order. Closed containment is inherited from the actual
assigned fragment cell. -/
theorem query_increment_le (bounds : FragmentReadings.FragmentBounds patch differential)
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} (piece :
      RectangularSegmentSplitting.SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1))
    {index : Nat} (primitives : RectangularPrimitiveModels.Primitives (Transitions.oriented (patch.sheets.refine
      index).transitions (patch.sheets.refine index).gauge) (PreparedPrimitiveSamples.differentialNumerator
      differential))
    (reached : PreparedFaceTracePrefixes.ParentReached face.cell.box (models.frame.owners sheet) parent)
    {count : Nat} {target : InverseRootPolynomial.Coordinate} (request : UniformPreparedRequests.LocalRequest parent
      count target)
    (first last : InverseRootPolynomial.Coordinate)
    (firstInside : piece.interval.lower ≤ first ∧ first ≤ piece.interval.upper)
    (lastInside : piece.interval.lower ≤ last ∧ last ≤ piece.interval.upper) :
    Data.Gaussian.Norm.Basic.normSq ((primitives.value piece.column piece.row (parent.edge.point last) -
        primitives.value piece.column piece.row (parent.edge.point first)) -
      (request.request.model.primitive.value.eval (parent.edge.point last) -
        request.request.model.primitive.value.eval (parent.edge.point first))) ≤
      queryDensity bounds piece.column piece.row request
        index * Data.Gaussian.Norm.Basic.normSq (parent.edge.point last - parent.edge.point first) := by
  have unit (fraction : InverseRootPolynomial.Coordinate) (inside : piece.interval.lower ≤ fraction ∧ fraction ≤
    piece.interval.upper) :
      0 ≤ fraction ∧ fraction ≤ 1 := ⟨piece.within.1.trans inside.1, inside.2.trans piece.within.2⟩
  have cellInside (fraction : InverseRootPolynomial.Coordinate) (inside : piece.interval.lower ≤ fraction ∧ fraction ≤
    piece.interval.upper) :
      (geometry.box piece.column piece.row).Contains (parent.edge.point fraction) := by
    rw [PreparedParentSplitting.prepared_point_eq parent fraction]
    exact piece.contains_query fraction inside
  have requestInside (fraction : InverseRootPolynomial.Coordinate) (inside : piece.interval.lower ≤ fraction ∧ fraction
    ≤ piece.interval.upper) :
      request.neighborhood.box.Contains (parent.edge.point fraction) := by
    rw [PreparedParentSplitting.prepared_point_eq parent fraction, PreparedSegmentCuts.point_eq_line]
    have start : request.neighborhood.box.Contains (parent.edge.point 0) := by
      rw [request.neighborhood_eq]
      exact request.patch.start_inside count
    exact Rational.Box.contains_line start request.finishInside (unit fraction inside)
  have rightStart := requestInside first firstInside
  have rightFinish := requestInside last lastInside
  rcases request with ⟨localPatch, neighborhood, neighborhoodEq, request, finishInside⟩
  subst neighborhood
  have bounded := PreparedComparison.prepared_subedge_primitive_increment_le (patch.transported.cell piece.column
    piece.row)
    differential parent reached first last (unit first firstInside) (cellInside first firstInside)
    localPatch count index request.index (primitives.dense piece.column piece.row)
    (GluedPrimitives.primitive_coefficient_eq differential primitives piece.column piece.row)
    request.model (bounds.atCell piece.column piece.row)
    (cellInside last lastInside) rightStart rightFinish
  exact bounded.trans_eq (by
    change _ = 12 * (Geometric.Basic.quarterRadius _ (index + 2) + Geometric.Basic.quarterRadius _ request.index) * _ *
      _
    rw [Model.refine_bound,
      SeededNeighborhood.refine,
      Model.refine_bound]
    rfl)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries
