module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CornerRequests
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularSharedPrimitives
public import Purelib.Riemann.Integration.PreparedParentSplitSelection
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
public import Purelib.Curves.Legendre.Periods.Jets.Source.Stage
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Primitive
public import Purelib.Riemann.Readings.UniformPreparedRequests.Covered
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Algebra.FiniteSum.List.Basic
import Batteries.Data.List.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Riemann.Readings.RectangularPointReadings.Mesh
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Vector.Dependent
import Purelib.Data.Nat.Order
import Purelib.Curves.Legendre.Periods.Jets.Source.Cells
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Data.List.Append
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Tactic.Ring

/-! # Ordered retained primitive requests compared with their actual source bank

The request-patch view indexes the same original prepared source product.
Each local comparison consumes its original request, source model and
coefficient payment. The finite error sum preserves all original parents,
repeated occurrences and zero displacements in their literal list order.
-/

public section

attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianNormSqSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat.Fraction.Cast.Order (natCast_le_direct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementSum movementMass movementMass_eq)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledLocalRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (coefficientMaximum localCoefficient)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ)
open Purelib.Algebra.FiniteSum.Fin.Rational (sum_constant)
open Purelib.Algebra.FiniteSum.Rational.Order
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Normalization.RegularFaceInverseModels (Clearance Bounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Integration.PreparedParentSplitting (PreparedSplitMesh ParentSplits)
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentPiece GridCuts SegmentSplit)
open Purelib.Riemann.Branches
open Purelib.Riemann.Paths
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Approximation.Rational
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- The original source displacement-cost sum equals the same parent spine's geometric movement sum. -/
theorem displacementCost_eq_movementSum (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) :
    displacementCost parents = movementSum parents := by
  induction parents with
  | nil => rfl
  | cons parent remaining ih =>
      have head : PreparedParent.cost parent = parent.edge.pointMovement := by
        change Norm.Basic.normSq ((PreparedParent.finishPoint parent).coordinate -
          (PreparedParent.startPoint parent).coordinate) =
            Norm.Basic.normSq (parent.edge.point 1 - parent.edge.point 0)
        rewrite [parent.edge.point_one, parent.edge.point_zero]
        rfl
      rewrite [displacementCost_cons, movementSum, head, ih]
      rfl

/-- The original source count and displacement costs are the controlled request's same movement mass. -/
theorem countCost_eq_movementMass (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) :
    (parents.length : Rational) * displacementCost parents = movementMass parents := by
  rewrite [displacementCost_eq_movementSum, movementMass_eq]
  rfl

/-- Transport the entire retained source product only through equality of its original covered-spine index. -/
def castCovered {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {first last : CoveredParents count parents} (prepared : PreparedParents first floor targets)
    (same : first = last) : PreparedParents last floor targets :=
  Eq.mp (congrArg (fun covered => PreparedParents covered floor targets) same) prepared

/-- Covered-index transport keeps the whole original source product heterogeneously. -/
private theorem packaged_castCovered_heq {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {first last : CoveredParents count parents} (prepared : PreparedParents first floor targets)
    (same : first = last) : HEq (prepared.castCovered same) prepared := by
  cases same
  rfl

/-- Covered-index transport keeps the whole original source product heterogeneously. -/
theorem castCovered_heq {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {first last : CoveredParents count parents} (prepared : PreparedParents first floor targets)
    (same : first = last) : HEq (prepared.castCovered same) prepared :=
  packaged_castCovered_heq prepared same

/-- Reading the complete source path after covered-index transport retains the identical actual source cache. -/
private theorem packaged_sources_castCovered {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {first last : CoveredParents count parents} (prepared : PreparedParents first floor targets)
    (same : first = last) {start finish : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := start) (finish := finish)) :
    sources last (prepared.castCovered same) chain = sources first prepared chain := by
  cases same
  rfl

/-- Reading the complete source path after covered-index transport retains the identical actual source cache. -/
theorem sources_castCovered {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {first last : CoveredParents count parents} (prepared : PreparedParents first floor targets)
    (same : first = last) {start finish : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := start) (finish := finish)) :
    sources last (prepared.castCovered same) chain = sources first prepared chain :=
  packaged_sources_castCovered prepared same chain

/-- Read the primitive-minus-source errors from the same retained ordered request and preparation spines. -/
private def primitiveErrors {target : Rational} : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (requests : RequestedParents count target parents) →
    PreparedParents (parameter := parameter) (frame := frame) requests.covered floor targets → List Canonical
  | _, .nil => fun _ => []
  | parent :: _, .cons request tail => fun prepared =>
      let head := prepared.1
      let remaining := prepared.2
      (request.request.model.primitive.value.eval (parent.edge.point 1) -
        request.request.model.primitive.value.eval (parent.edge.point 0) -
          head.preparation.cell.models.valueZero.model.integralSample) :: primitiveErrors tail remaining

/-- The error list contains one entry for every original parent, with repetitions retained. -/
private theorem primitiveErrors_length {target : Rational} :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (requests : RequestedParents count target parents) →
    (prepared : PreparedParents (parameter := parameter) (frame := frame) requests.covered floor targets) →
    (primitiveErrors requests prepared).length = parents.length
  | _, .nil => fun _ => rfl
  | _, .cons _ tail => fun prepared => congrArg Nat.succ (primitiveErrors_length tail prepared.2)

/-- The error sum reads the original request increments and actual source value-zero path integral. -/
private theorem primitiveErrors_sum {target : Rational} :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (requests : RequestedParents count target parents) →
    (prepared : PreparedParents (parameter := parameter) (frame := frame) requests.covered floor targets) →
    {start finish : LiftedPoint 2} → (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    gaussianSum (primitiveErrors requests prepared) = gaussianSum requests.increments -
      (PathModel.mk ((sources requests.covered prepared chain).cells 0)).integralSample
  | _, .nil => fun prepared => by
      intro start finish chain
      cases prepared
      cases chain
      change (0 : Canonical) = 0 - 0
      ring1
  | parent :: _, .cons request tail => fun prepared => by
      intro start finish chain
      cases chain with
      | cons _ chain =>
        let head := prepared.1
        let remaining := prepared.2
        have tailSum := primitiveErrors_sum tail remaining chain
        change (request.request.model.primitive.value.eval (parent.edge.point 1) -
            request.request.model.primitive.value.eval (parent.edge.point 0) -
              head.preparation.cell.models.valueZero.model.integralSample) +
            gaussianSum (primitiveErrors tail remaining) =
          (request.request.model.primitive.value.eval (parent.edge.point 1) -
            request.request.model.primitive.value.eval (parent.edge.point 0)) + gaussianSum tail.increments -
            (head.preparation.cell.models.valueZero.model.integralSample +
              (PathModel.mk ((sources tail.covered remaining chain).cells 0)).integralSample)
        rewrite [tailSum]
        ring1

/-- Stored coefficient maxima pay all original local primitive/source errors in their exact parent order. -/
private theorem primitiveErrors_normSum_le {target coefficientTarget : Rational} (zero : basis.exponent = 0) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (requests : RequestedParents count target parents) →
    (prepared : PreparedParents (parameter := parameter) (frame := frame) requests.covered floor targets) →
    coefficientMaximum requests < coefficientTarget →
    gaussianNormSqSum (primitiveErrors requests prepared) ≤
      16 * (targets.localBound + coefficientTarget) * displacementCost parents
  | _, .nil => fun _ _ => by
      change (0 : Rational) ≤ 16 * (targets.localBound + coefficientTarget) * 0
      rewrite [Data.Rat.Fraction.Field.mul_zero_direct]
      exact Basic.le_refl 0
  | parent :: _, .cons request tail => fun prepared paid => by
      let head := prepared.1
      let remaining := prepared.2
      have headPaid : localCoefficient request < coefficientTarget :=
        (Basic.le_max_left _ _).trans_lt paid
      let controlled : ControlledLocalRequest parent count target coefficientTarget 0 :=
        ⟨request, headPaid, Nat.zero_le request.request.index⟩
      have headBound := PreparedParent.controlled_primitive_paid_le controlled head zero
      have tailBound := primitiveErrors_normSum_le zero tail remaining
        ((Basic.le_max_right _ _).trans_lt paid)
      change Canonical.normSq (request.request.model.primitive.value.eval (parent.edge.point 1) -
          request.request.model.primitive.value.eval (parent.edge.point 0) -
            head.preparation.cell.models.valueZero.model.integralSample) +
          gaussianNormSqSum (primitiveErrors tail remaining) ≤ _
      rewrite [← Norm.Basic.normSq_eq_canonical]
      exact (Arithmetic.add_le_add_direct headBound tailBound).trans_eq (by
        rewrite [displacementCost_cons]
        ring1)

/-- The same retained primitive bank and source path obey their paid count-and-movement comparison.

The original coefficient maximum is a certificate of the actual retained
requests, not a supplied final comparison. Finite summation charges the
original parent count once and retains every actual source integral sample.
-/
theorem primitive_error_le {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {target coefficientTarget : Rational} (requests : RequestedParents count target parents)
    (prepared : PreparedParents requests.covered floor targets) (zero : basis.exponent = 0)
    (paid : coefficientMaximum requests < coefficientTarget) {start finish : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := start) (finish := finish)) :
    Norm.Basic.normSq (gaussianSum requests.increments -
      (PathModel.mk ((sources requests.covered prepared chain).cells 0)).integralSample) ≤
        16 * (targets.localBound + coefficientTarget) * (parents.length : Rational) * displacementCost parents := by
  have original := Norm.Sum.Basic.normSq_gaussianSum_le (primitiveErrors requests prepared)
  rewrite [← Norm.Basic.normSq_eq_canonical] at original
  rewrite [primitiveErrors_sum requests prepared chain, primitiveErrors_length requests prepared] at original
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (primitiveErrors_normSum_le zero requests prepared paid)
    (Data.Rat.Fraction.Cast.Order.natCast_le_direct (m := 0) (n := parents.length) (Nat.zero_le parents.length))
  exact (original.trans scaled).trans_eq (by ring1)

section RectangularComparison

variable {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
variable {columns rows : Nat} {geometry : Geometry columns rows} {cuts : GridCuts geometry}

/-- The original rectangular segment split retained at every bounded occurrence of the same parent list. -/
abbrev RectangularSplits (cuts : GridCuts geometry) (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) :=
  DependentVector (fun index : Fin parents.length =>
    SegmentSplit cuts ((parents[index.val]'index.isLt).edge.point 0) ((parents[index.val]'index.isLt).edge.point 1))

namespace RectangularSplits

/-- Split every original parent once and store its whole ordered partition and original endpoints. -/
@[expose] def build (cuts : GridCuts geometry) (parents : List (CenteredEdge (Fibre.frameCurve frame) basis))
    (inside : ∀ index : Fin parents.length,
      RectangularSegmentSplitting.Geometry.Covers geometry ((parents[index.val]'index.isLt).edge.point 0) ∧
        RectangularSegmentSplitting.Geometry.Covers geometry ((parents[index.val]'index.isLt).edge.point 1)) :
    RectangularSplits cuts parents :=
  DependentVector.ofFn fun index => SegmentSplit.build cuts _ _ (inside index).1 (inside index).2

/-- Sum the same retained piece increments in their original parent and interval order.

Only the supplied primitive values are read. Every segment's stored piece
list is reused; no source request, grid cut or partition is reconstructed.
-/
@[expose] def integral (splits : RectangularSplits cuts parents)
    (values : Fin (columns + 1) → Fin (rows + 1) → Canonical → Canonical) : Canonical :=
  sumFin fun index : Fin parents.length =>
    let split := splits.get index
    sumFin fun position : Fin split.pieces.length =>
      let piece := split.pieces[position.val]'position.isLt
      values piece.column piece.row piece.lastPoint - values piece.column piece.row piece.firstPoint

/-- Sum the actual piece error payments with their retained segment counts and the original parent count. -/
@[expose] def error (splits : RectangularSplits cuts parents)
    (payment : ∀ index : Fin parents.length,
      SegmentPiece geometry ((parents[index.val]'index.isLt).edge.point 0)
        ((parents[index.val]'index.isLt).edge.point 1) → Rational) : Rational :=
  (parents.length : Rational) * sumFin fun index : Fin parents.length =>
    let split := splits.get index
    (split.count : Rational) * sumFin fun position : Fin split.pieces.length =>
      payment index (split.pieces[position.val]'position.isLt)

/-- Pointwise bounds on the retained fragments bound their original weighted error fold.

Only actual stored piece occurrences need comparison. The original parent
count, segment counts, partitions and index order remain the same.
-/
theorem error_mono (splits : RectangularSplits cuts parents)
    {left right : ∀ index : Fin parents.length,
      SegmentPiece geometry ((parents[index.val]'index.isLt).edge.point 0)
        ((parents[index.val]'index.isLt).edge.point 1) → Rational}
    (pointwise : ∀ index, ∀ position : Fin (splits.get index).pieces.length,
      left index ((splits.get index).pieces[position.val]'position.isLt) ≤
        right index ((splits.get index).pieces[position.val]'position.isLt)) :
    splits.error left ≤ splits.error right := by
  unfold error
  apply Arithmetic.mul_le_mul_of_nonneg_left_direct ?_
    (natCast_le_direct (m := 0) (n := parents.length) (Nat.zero_le parents.length))
  apply IndexedBudget.sumFin_le
  intro index
  apply Arithmetic.mul_le_mul_of_nonneg_left_direct ?_
    (natCast_le_direct (m := 0) (n := (splits.get index).count) (Nat.zero_le (splits.get index).count))
  exact IndexedBudget.sumFin_le (pointwise index)

/-- A constant fragment payment is bounded by the actual parent count and squared total fragment count.

The positional split view reads the original splitting bank's cached counts.
The square of their total bounds the sum of their squares; no parent or
fragment occurrence is removed or replaced by an enlarged synthetic count.
-/
theorem error_constant_le (bank : ParentSplits cuts parents) {payment : Rational}
    (nonnegative : 0 ≤ payment) :
    error (PreparedParentSplitSelection.indexed bank) (fun _ _ => payment) ≤
      (parents.length : Rational) *
        ((bank.pieceCount : Rational) * ((bank.pieceCount : Rational) * payment)) := by
  let splits : RectangularSplits cuts parents := PreparedParentSplitSelection.indexed bank
  let counts (index : Fin parents.length) : Rational := ((splits.get index).count : Rational)
  have positive : ∀ index, 0 ≤ counts index := fun index =>
    natCast_le_direct (m := 0) (n := (splits.get index).count) (Nat.zero_le _)
  have total : sumFin counts = (bank.pieceCount : Rational) :=
    PreparedParentSplitSelection.sum_counts bank
  have squares := sumFin_mul_le counts counts positive positive
  rewrite [total] at squares
  unfold error
  apply Arithmetic.mul_le_mul_of_nonneg_left_direct ?_
    (natCast_le_direct (m := 0) (n := parents.length) (Nat.zero_le _))
  calc
    _ = sumFin (fun index : Fin parents.length => (counts index * counts index) * payment) := by
      apply Algebra.FiniteSum.Fin.sumFin_congr
      intro index
      change ((splits.get index).count : Rational) *
        sumFin (fun _ : Fin (splits.get index).pieces.length => payment) =
          (counts index * counts index) * payment
      rewrite [sum_constant, ← (splits.get index).count_eq]
      change counts index * (counts index * payment) = _
      ring1
    _ = sumFin (fun index => counts index * counts index) * payment :=
      Algebra.FiniteSum.Fin.sumFin_mul_right _ _
    _ ≤ ((bank.pieceCount : Rational) * bank.pieceCount) * payment :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct squares nonnegative
    _ = _ := by ring1

/-- Reading one global function through the retained splits telescopes along the original parent chain.

Every stored split retains its original interval partition. The same
function cancels at every interior split point and original parent join,
preserving the actual chain endpoints.
-/
theorem integral_eq_increment (splits : RectangularSplits cuts parents)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain parents (start := start) (finish := finish))
    (value : Canonical → Canonical) :
    splits.integral (fun _ _ => value) = value finish.coordinate - value start.coordinate := by
  induction chain with
  | nil point =>
      cases splits
      change (0 : Canonical) = value point.coordinate - value point.coordinate
      ring1
  | cons parent tail ih =>
      cases splits with
      | cons split remaining =>
          have head : sumFin (fun position : Fin split.pieces.length =>
              let piece := split.pieces[position.val]'position.isLt
              value piece.lastPoint - value piece.firstPoint) =
              value (parent.edge.point 1) - value (parent.edge.point 0) :=
            (Norm.Sum.Indexed.sumFin_map split.pieces
              (fun piece => value piece.lastPoint - value piece.firstPoint)).trans (split.telescope value)
          unfold integral
          rewrite [sumFin_succ]
          change sumFin (fun position : Fin split.pieces.length =>
            let piece := split.pieces[position.val]'position.isLt
            value piece.lastPoint - value piece.firstPoint) + integral remaining (fun _ _ => value) = _
          rewrite [head, ih remaining, parent.edge.point_zero, parent.edge.point_one]
          ring1

/-- Paid mesh ownership errors bound the same retained split sums on a shared numerical primitive bank.

The supplied entry equalities identify the complete splits with the actual
mesh bank. Original contacts place their endpoints in that mesh, and the
existing grid request pays each shared-to-cell increment discrepancy.
Both actual split and parent counts remain in the finite error sum.
-/
theorem shared_bound {box : Box} {clearance : Clearance (Paths.polynomial parameter) box}
    {comparisonBounds : Bounds clearance} {seed : Owner ((Paths.polynomial parameter).eval box.anchor)}
    (common : RectangularPatch comparisonBounds seed geometry)
    {numerator : Polynomial} {pairs : Nat} {target : Rational}
    {bounds : PrimitiveOverlapBounds clearance numerator}
    (request : GridPrimitiveAccuracy bounds columns target pairs)
    {extra : List Canonical} (mesh : PreparedSplitMesh cuts parents extra)
    (splits : RectangularSplits cuts parents)
    (same : ∀ position, splits.get position = (PreparedParentSplitSelection.select mesh.splits position).split)
    {primitives : Primitives (RectangularSheetGauge.Transitions.oriented
      (common.sheets.refine request.index).transitions (common.sheets.refine request.index).gauge) numerator pairs}
    {anchors : PrimitiveAnchors primitives} {offsets : Offsets anchors.edges}
    (readings : SharedPrimitiveValues anchors offsets mesh.mesh.surface) :
    Norm.Basic.normSq (splits.integral (fun _ _ => readings.atPoint) - splits.integral primitives.value) ≤
      splits.error (fun _ _ => 16 * request.globalBound) := by
  unfold integral error
  apply Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin
  intro position
  dsimp only
  rewrite [(splits.get position).count_eq]
  apply Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin
  intro pieceIndex
  let piece := (splits.get position).pieces[pieceIndex.val]'pieceIndex.isLt
  let selected := PreparedParentSplitSelection.select mesh.splits position
  have present : piece ∈ selected.split.pieces :=
    Eq.mp (congrArg (fun split => piece ∈ split.pieces) (same position)) (List.getElem_mem pieceIndex.isLt)
  let contact := mesh.contact selected.member piece present
  have firstInside : (geometry.box piece.column piece.row).Contains
      (mesh.mesh.surface.mesh.coordinate contact.first) :=
    Eq.mpr (congrArg (geometry.box piece.column piece.row).Contains contact.first_eq) piece.first_inside
  have lastInside : (geometry.box piece.column piece.row).Contains
      (mesh.mesh.surface.mesh.coordinate contact.last) :=
    Eq.mpr (congrArg (geometry.box piece.column piece.row).Contains contact.last_eq) piece.last_inside
  change Norm.Basic.normSq ((readings.atPoint piece.lastPoint - readings.atPoint piece.firstPoint) -
    (primitives.value piece.column piece.row piece.lastPoint -
      primitives.value piece.column piece.row piece.firstPoint)) ≤ _
  rewrite [← contact.first_eq, ← contact.last_eq, readings.atPoint_coordinate, readings.atPoint_coordinate]
  rewrite [Norm.Basic.normSq_eq_canonical]
  exact RectangularSharedPrimitives.GridPrimitiveAccuracy.shared_local_increment_bound request
    readings common.cell_refines piece.column piece.row
    contact.first contact.last firstInside lastInside

end RectangularSplits

/-- The retained whole source integral obeys the sum of its actual rectangular fragment payments.

Each retained piece supplies alignment with its original parent's root.
The same cached splits and common primitive bank are read in original
occurrence order, and the existing source readback identifies the whole
integral with those exact retained cell samples. Both segment and parent counts remain
in the quantitative bound; no connector or physical contribution is erased.
-/
theorem rectangular_integral_le (covered : CoveredParents count parents)
    (prepared : PreparedParents covered floor targets)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain parents (start := start) (finish := finish))
    {box prefixAmbient : Box}
    {clearance : Clearance (Paths.polynomial parameter) box} {comparisonBounds : Bounds clearance}
    {pathStart : Canonical} {sourceOwner : Owner ((Paths.polynomial parameter).eval pathStart)}
    {prefixPath : ClearPath (Paths.polynomial parameter) prefixAmbient pathStart box.anchor}
    {entered : TracedPath prefixPath sourceOwner} (prefixInside : InBox box prefixPath)
    (reference : WindingOneLoop (Paths.polynomial parameter) pathStart)
    (common : RectangularPatch comparisonBounds entered.finishOwner geometry)
    (splits : RectangularSplits cuts parents) (channel : Fin 6) (index : Nat)
    (aligned : ∀ position : Fin parents.length,
      ∀ piece : SegmentPiece geometry ((parents[position.val]'position.isLt).edge.point 0)
        ((parents[position.val]'position.isLt).edge.point 1),
      piece ∈ (splits.get position).pieces →
      RootAligned ((Model.overlapRefine (common.transported.cell piece.column piece.row).model) index)
        piece.firstPoint ((parents[position.val]'position.isLt).edge.rootName piece.interval.lower
          ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩))
    (primitives : Primitives (RectangularSheetGauge.Transitions.oriented (common.sheets.refine index).transitions
      (common.sheets.refine index).gauge)
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (Specification.Table.forms parameter channel).denominatorPairs)
    (overlaps : ∀ position : Fin parents.length,
      ∀ piece : SegmentPiece geometry ((parents[position.val]'position.isLt).edge.point 0)
        ((parents[position.val]'position.isLt).edge.point 1),
      PrimitiveOverlapBounds
        (clearance.restrict (common.cell_refines piece.column piece.row))
        ((Specification.Table.forms parameter channel).numerator.scale
          (Specification.Table.forms parameter channel).scale)) :
    Norm.Basic.normSq (splits.integral primitives.value -
      (PathModel.mk ((sources covered prepared chain).cells channel)).integralSample) ≤
      splits.error (fun position piece =>
        12 * (((common.transported.cell piece.column piece.row).model.refine (index + 2)).bound +
          (((covered.entry position).1.neighborhood count).base.refine
            (prepared.entry position).preparation.attached.source.selection.stage).bound) *
          (overlaps position piece).weight (Specification.Table.forms parameter channel).denominatorPairs *
            Norm.Basic.normSq (piece.lastPoint - piece.firstPoint)) := by
  rewrite [integralSample_eq_sumFin covered prepared chain channel]
  apply Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin
  intro position
  rewrite [(prepared.entry position).preparation.cell_eq]
  exact (prepared.entry position).rectangular_split_le prefixInside reference common
    (splits.get position) channel index
    (by
      intro piece member otherCount otherPatch otherInside otherSample roots otherIndex
      exact aligned position piece member otherPatch otherInside otherSample roots otherIndex)
    primitives (overlaps position)

/-- The original source sample is paid against the actual endpoints of its retained shared mesh readings.

The same saved parent splits and cell primitives supply the source bound.
Their mesh contacts supply the separate ownership bound, and the original
centered chain telescopes the shared readings at its actual endpoints.
Both payments retain the original parent and piece counts and source stages.
-/
theorem rectangular_endpoint_le (covered : CoveredParents count parents)
    (prepared : PreparedParents covered floor targets)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain parents (start := start) (finish := finish))
    {box prefixAmbient : Box}
    {clearance : Clearance (Paths.polynomial parameter) box} {comparisonBounds : Bounds clearance}
    {pathStart : Canonical} {sourceOwner : Owner ((Paths.polynomial parameter).eval pathStart)}
    {prefixPath : ClearPath (Paths.polynomial parameter) prefixAmbient pathStart box.anchor}
    {entered : TracedPath prefixPath sourceOwner} (prefixInside : InBox box prefixPath)
    (reference : WindingOneLoop (Paths.polynomial parameter) pathStart)
    (common : RectangularPatch comparisonBounds entered.finishOwner geometry)
    {extra : List Canonical} (mesh : PreparedSplitMesh cuts parents extra)
    (splits : RectangularSplits cuts parents)
    (same : ∀ position, splits.get position = (PreparedParentSplitSelection.select mesh.splits position).split)
    (channel : Fin 6) {target : Rational}
    {bounds : PrimitiveOverlapBounds clearance
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)}
    (request : GridPrimitiveAccuracy bounds columns target
      (Specification.Table.forms parameter channel).denominatorPairs)
    (aligned : ∀ position : Fin parents.length,
      ∀ piece : SegmentPiece geometry ((parents[position.val]'position.isLt).edge.point 0)
        ((parents[position.val]'position.isLt).edge.point 1),
      piece ∈ (splits.get position).pieces →
      RootAligned ((Model.overlapRefine (common.transported.cell piece.column piece.row).model) request.index)
        piece.firstPoint ((parents[position.val]'position.isLt).edge.rootName piece.interval.lower
          ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩))
    (primitives : Primitives (RectangularSheetGauge.Transitions.oriented
      (common.sheets.refine request.index).transitions (common.sheets.refine request.index).gauge)
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (Specification.Table.forms parameter channel).denominatorPairs)
    {anchors : PrimitiveAnchors primitives} {offsets : Offsets anchors.edges}
    (readings : SharedPrimitiveValues anchors offsets mesh.mesh.surface)
    (first last : Fin mesh.mesh.surface.mesh.vertices.length)
    (first_eq : mesh.mesh.surface.mesh.coordinate first = start.coordinate)
    (last_eq : mesh.mesh.surface.mesh.coordinate last = finish.coordinate)
    (overlaps : ∀ position : Fin parents.length,
      ∀ piece : SegmentPiece geometry ((parents[position.val]'position.isLt).edge.point 0)
        ((parents[position.val]'position.isLt).edge.point 1),
      PrimitiveOverlapBounds (clearance.restrict (common.cell_refines piece.column piece.row))
        ((Specification.Table.forms parameter channel).numerator.scale
          (Specification.Table.forms parameter channel).scale)) :
    Norm.Basic.normSq ((readings.values last - readings.values first) -
      (PathModel.mk ((sources covered prepared chain).cells channel)).integralSample) ≤
      2 * (splits.error (fun _ _ => 16 * request.globalBound) +
        splits.error (fun position piece =>
          12 * (((common.transported.cell piece.column piece.row).model.refine (request.index + 2)).bound +
            (((covered.entry position).1.neighborhood count).base.refine
              (prepared.entry position).preparation.attached.source.selection.stage).bound) *
            (overlaps position piece).weight (Specification.Table.forms parameter channel).denominatorPairs *
              Norm.Basic.normSq (piece.lastPoint - piece.firstPoint))) := by
  have sourceBound := rectangular_integral_le covered prepared chain prefixInside reference common splits channel
    request.index aligned primitives overlaps
  have meshBound := splits.shared_bound common request mesh same readings
  have endpoints := splits.integral_eq_increment chain readings.atPoint
  have firstRead : readings.atPoint start.coordinate = readings.values first :=
    (congrArg readings.atPoint first_eq).symm.trans (readings.atPoint_coordinate first)
  have lastRead : readings.atPoint finish.coordinate = readings.values last :=
    (congrArg readings.atPoint last_eq).symm.trans (readings.atPoint_coordinate last)
  rewrite [firstRead, lastRead] at endpoints
  let sample := (PathModel.mk ((sources covered prepared chain).cells channel)).integralSample
  have identity : (readings.values last - readings.values first) - sample =
      (splits.integral (fun _ _ => readings.atPoint) - splits.integral primitives.value) +
        (splits.integral primitives.value - sample) := by
    rewrite [endpoints]
    ring1
  change Norm.Basic.normSq ((readings.values last - readings.values first) - sample) ≤ _
  rewrite [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct meshBound sourceBound) (by decide))

end RectangularComparison

section CornerComparison

open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments (AssignedSegments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments (Comparisons)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh (SegmentComparison)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Paths.PreparedSegmentParentBanks.PreparedPath.CoveredSegments (parents)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments
  (ParentCaches)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Algebra.FiniteSum.List.Basic (scalarSum)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
variable {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
variable {bank : BranchCellBank (Fibre.frameCurve frame) branches higher}
variable {frames : RootFrames bank.grid} {vertices : VertexBank bank.grid} {edges : RootEdgeBank frames}
variable {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces} {ambient : Box}
variable {domains : FaceDomainBank frames faces.regulars} {index : Nat} {parentSheet : Fin 2}
variable {numerator : Polynomial} {pairs : Nat}

/-- An actual routed segment's source sample is paid against the canonical bank's same oriented face increment.

The saved comparison supplies its face-domain and sheet equalities. The
original cache transports retain the canonical bank, and its corner
coordinates identify both actual segment endpoints. The mesh and source
payments keep all parent occurrences, inverse powers and source stages.
The default overlap family restricts the request's retained face bounds to
each actual fragment, preserving its original inverse ceiling.
-/
theorem segment_integral_le
    {segmentAmbient : Box} {segmentStart segmentFinish : Canonical}
    {segment : ClearPath.ClearSegment (Paths.polynomial parameter) segmentAmbient segmentStart segmentFinish}
    {segmentOwner : Owner ((Paths.polynomial parameter).eval segmentStart)}
    (placement : SegmentFace mesh segment) (piece : CoveredSegment segment segmentOwner)
    (compared : SegmentComparison placement piece basis parentSheet)
    (domains : FaceDomainBank frames faces.regulars)
    (same : compared.domains = domains.atRoute placement.location)
    (sources : PreparedParents compared.entered.cache.covered floor targets) (channel : Fin 6) :
    let form := Specification.Table.forms parameter channel
    ∀ {target : Rational}
      {bounds : PrimitiveOverlapBounds placement.face.clearance (form.numerator.scale form.scale)}
      (request : GridPrimitiveAccuracy bounds compared.entered.domain.steps target form.denominatorPairs)
      (shared : FacePrimitiveBank basis request.index domains (form.numerator.scale form.scale) form.denominatorPairs)
      (overlaps : optParam (∀ position : Fin compared.entered.cache.parents.length,
        ∀ fragment : SegmentPiece compared.entered.domain.geometry
          ((compared.entered.cache.parents[position.val]'position.isLt).edge.point 0)
          ((compared.entered.cache.parents[position.val]'position.isLt).edge.point 1),
        PrimitiveOverlapBounds (placement.face.clearance.restrict
          (compared.entered.domain.patch.cell_refines fragment.column fragment.row))
          (form.numerator.scale form.scale))
        (fun _ fragment => bounds.restrict
          (compared.entered.domain.patch.cell_refines fragment.column fragment.row))),
    let splits : RectangularSplits compared.entered.domain.cuts compared.entered.cache.parents :=
      PreparedParentSplitSelection.indexed compared.entered.mesh.splits
    Norm.Basic.normSq (shared.edgeIncrement placement.location -
      (PathModel.mk ((PreparedParents.sources compared.entered.cache.covered sources
        compared.entered.cache.centeredChain).cells channel)).integralSample) ≤
      2 * (16 * request.globalBound +
        2 * (splits.error (fun _ _ => 16 * request.globalBound) +
          splits.error (fun position fragment =>
            12 * (((compared.entered.domain.patch.transported.cell fragment.column fragment.row).model.refine
                (request.index + 2)).bound +
              (((compared.entered.cache.covered.entry position).1.neighborhood 1).base.refine
                (sources.entry position).preparation.attached.source.selection.stage).bound) *
              (overlaps position fragment).weight form.denominatorPairs *
                Norm.Basic.normSq (fragment.lastPoint - fragment.firstPoint)))) := by
  intro form target bounds request shared overlaps splits
  let data := compared.sharedData shared same
  let readings := PointReadings.OnMesh.build data.corners compared.entered.mesh.mesh.surface
  let face := placement.face
  let anchorTrace := TracedPath.build
    (ClearPath.nil (polynomial := (Fibre.frameCurve frame).polynomial) (ambient := face.cell.box) face.cell.box.anchor)
    (.nil face.cell.box.anchor) (compared.domains.models.frame.owners compared.entered.entry.sheet)
  have sourceBound := rectangular_endpoint_le compared.entered.cache.covered sources
    compared.entered.cache.centeredChain (entered := anchorTrace) face.cell.box.contains_anchor
    (LoopMonodromy.BranchCellBank.referenceAt bank _
      (face.cell.anchor_mem face.member)).toLoop compared.entered.domain.patch compared.entered.mesh splits
    (PreparedParentSplitSelection.indexed_get compared.entered.mesh.splits) channel request
    (by
      intro position fragment _member otherCount otherPatch otherInside otherSample roots otherIndex
      exact compared.entered.parent_piece_aligned position fragment request.index
        otherPatch otherInside otherSample roots otherIndex)
    data.primitives readings.shared compared.entered.first compared.entered.last
    compared.entered.first_eq compared.entered.last_eq overlaps
  have firstEq : compared.entered.mesh.mesh.surface.mesh.coordinate compared.entered.first =
      Face.Corners.FaceCorners.point face.cell.box placement.location.corners.start :=
    compared.entered.first_eq.trans (placement.start_eq.symm.trans
      (congrArg Prod.fst placement.location.corner_coordinates).symm)
  have lastEq : compared.entered.mesh.mesh.surface.mesh.coordinate compared.entered.last =
      Face.Corners.FaceCorners.point face.cell.box placement.location.corners.finish :=
    compared.entered.last_eq.trans (placement.finish_eq.symm.trans
      (congrArg Prod.snd placement.location.corner_coordinates).symm)
  have pointBound := RectangularPointReadings.GridPrimitiveAccuracy.point_increment_bound request data.corners
    readings.shared compared.entered.domain.patch.cell_refines placement.location.corners.start
    placement.location.corners.finish compared.entered.first compared.entered.last firstEq lastEq
  rewrite [← Norm.Basic.normSq_eq_canonical] at pointBound
  have corners : data.corners.values =
      ((shared.atRoute placement.location).atSheet placement.location.sheet).corners.values :=
    compared.sharedData_corners shared same
  rewrite [corners] at pointBound
  change Norm.Basic.normSq (shared.edgeIncrement placement.location -
    (readings.shared.values compared.entered.last - readings.shared.values compared.entered.first)) ≤ _ at pointBound
  let sample := (PathModel.mk ((PreparedParents.sources compared.entered.cache.covered sources
    compared.entered.cache.centeredChain).cells channel)).integralSample
  let endpoint := readings.shared.values compared.entered.last - readings.shared.values compared.entered.first
  have identity : shared.edgeIncrement placement.location - sample =
      (shared.edgeIncrement placement.location - endpoint) + (endpoint - sample) := by ring1
  change Norm.Basic.normSq (shared.edgeIncrement placement.location - sample) ≤ _
  rewrite [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct pointBound sourceBound) (by decide))

/-- The retained face weight bounds the actual segment's complete grid and source payment.

The request restricts its own face bound to each stored fragment. Its same
odd-power weight bounds all those local weights, while the original refined
models, source stages, displacements and error-fold counts are retained.
-/
theorem segment_integral_le_face
    {segmentAmbient : Box} {segmentStart segmentFinish : Canonical}
    {segment : ClearPath.ClearSegment (Paths.polynomial parameter) segmentAmbient segmentStart segmentFinish}
    {segmentOwner : Owner ((Paths.polynomial parameter).eval segmentStart)}
    (placement : SegmentFace mesh segment) (piece : CoveredSegment segment segmentOwner)
    (compared : SegmentComparison placement piece basis parentSheet)
    (domains : FaceDomainBank frames faces.regulars)
    (same : compared.domains = domains.atRoute placement.location)
    (sources : PreparedParents compared.entered.cache.covered floor targets) (channel : Fin 6) :
    let form := Specification.Table.forms parameter channel
    ∀ {target : Rational}
      {bounds : PrimitiveOverlapBounds placement.face.clearance (form.numerator.scale form.scale)}
      (request : GridPrimitiveAccuracy bounds compared.entered.domain.steps target form.denominatorPairs)
      (shared : FacePrimitiveBank basis request.index domains (form.numerator.scale form.scale) form.denominatorPairs),
    let splits : RectangularSplits compared.entered.domain.cuts compared.entered.cache.parents :=
      PreparedParentSplitSelection.indexed compared.entered.mesh.splits
    Norm.Basic.normSq (shared.edgeIncrement placement.location -
      (PathModel.mk ((PreparedParents.sources compared.entered.cache.covered sources
        compared.entered.cache.centeredChain).cells channel)).integralSample) ≤
      2 * (16 * request.globalBound +
        2 * (splits.error (fun _ _ => 16 * request.globalBound) +
          splits.error (fun position fragment =>
            12 * (((compared.entered.domain.patch.transported.cell fragment.column fragment.row).model.refine
                (request.index + 2)).bound +
              (((compared.entered.cache.covered.entry position).1.neighborhood 1).base.refine
                (sources.entry position).preparation.attached.source.selection.stage).bound) *
              bounds.weight form.denominatorPairs *
                Norm.Basic.normSq (fragment.lastPoint - fragment.firstPoint)))) := by
  intro form target bounds request shared splits
  have localBound := segment_integral_le placement piece compared domains same sources channel request shared
  apply localBound.trans
  apply Arithmetic.mul_le_mul_of_nonneg_left_direct ?_ (by decide)
  apply Arithmetic.add_le_add_direct (Basic.le_refl _) ?_
  apply Arithmetic.mul_le_mul_of_nonneg_left_direct ?_ (by decide)
  apply Arithmetic.add_le_add_direct (Basic.le_refl _) ?_
  apply splits.error_mono
  intro position pieceIndex
  let fragment := (splits.get position).pieces[pieceIndex.val]'pieceIndex.isLt
  have residualNonnegative : 0 ≤
      12 * (((compared.entered.domain.patch.transported.cell fragment.column fragment.row).model.refine
          (request.index + 2)).bound +
        (((compared.entered.cache.covered.entry position).1.neighborhood 1).base.refine
          (sources.entry position).preparation.attached.source.selection.stage).bound) :=
    Arithmetic.mul_nonneg_direct (by decide)
      (Arithmetic.add_le_add_direct
        ((compared.entered.domain.patch.transported.cell fragment.column fragment.row).model.refine
          (request.index + 2)).bound_nonnegative
        (((compared.entered.cache.covered.entry position).1.neighborhood 1).base.refine
          (sources.entry position).preparation.attached.source.selection.stage).bound_nonnegative)
  exact Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (bounds.restrict_weight_le
        (compared.entered.domain.patch.cell_refines fragment.column fragment.row) form.denominatorPairs)
      residualNonnegative)
    (Norm.Basic.normSq_nonneg _)

/-- A paid fragment request bounds its segment's source discrepancy with the original parent-count factor.

The retained source floor is at least one stage beyond the request's grid
index. Model refinement, the actual fragment boxes and the same cached
fragment allocation pay all grid and source terms. No local residual or
displacement comparison is supplied by the caller.
-/
theorem segment_integral_le_accuracy
    {segmentAmbient : Box} {segmentStart segmentFinish : Canonical}
    {segment : ClearPath.ClearSegment (Paths.polynomial parameter) segmentAmbient segmentStart segmentFinish}
    {segmentOwner : Owner ((Paths.polynomial parameter).eval segmentStart)}
    (placement : SegmentFace mesh segment) (piece : CoveredSegment segment segmentOwner)
    (compared : SegmentComparison placement piece basis parentSheet)
    (domains : FaceDomainBank frames faces.regulars)
    (same : compared.domains = domains.atRoute placement.location)
    (sources : PreparedParents compared.entered.cache.covered floor targets) (channel : Fin 6) :
    let form := Specification.Table.forms parameter channel
    ∀ {target : Rational}
      {bounds : PrimitiveOverlapBounds placement.face.clearance (form.numerator.scale form.scale)}
      (budget : FragmentAccuracy bounds compared.entered.domain.steps
        compared.entered.mesh.splits.pieceCount target form.denominatorPairs)
      (_floorAfter : budget.grid.index + 1 ≤ floor)
      (shared : FacePrimitiveBank basis budget.grid.index domains
        (form.numerator.scale form.scale) form.denominatorPairs),
    Norm.Basic.normSq (shared.edgeIncrement placement.location -
      (PathModel.mk ((PreparedParents.sources compared.entered.cache.covered sources
        compared.entered.cache.centeredChain).cells channel)).integralSample) ≤
      2 * ((compared.entered.cache.parents.length : Rational) + 1) * target := by
  intro form target bounds budget floorAfter shared
  let bank := compared.entered.mesh.splits
  let splits : RectangularSplits compared.entered.domain.cuts compared.entered.cache.parents :=
    PreparedParentSplitSelection.indexed bank
  let N : Rational := compared.entered.cache.parents.length
  let F : Rational := bank.pieceCount
  let q := Geometric.Basic.quarterRadius (1 / 16) budget.grid.index
  let g := budget.grid.globalBound
  let f := budget.perFragment
  let c := 12 * q * bounds.weight form.denominatorPairs * placement.face.cell.box.diagonalSq
  have nNonnegative : 0 ≤ N := natCast_le_direct (m := 0) (n := compared.entered.cache.parents.length)
    (Nat.zero_le _)
  have fCountNonnegative : 0 ≤ F := natCast_le_direct (m := 0) (n := bank.pieceCount) (Nat.zero_le _)
  have qNonnegative : 0 ≤ q := Geometric.Basic.quarterRadius_nonneg (by decide) _
  have cNonnegative : 0 ≤ c := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide) qNonnegative)
      (bounds.weight_nonnegative _)) placement.face.cell.box.diagonalSq_nonneg
  have gNonnegative : 0 ≤ g := by
    change 0 ≤ budget.grid.globalBound
    rewrite [budget.grid.globalBound_eq_quarter]
    exact Geometric.Basic.quarterRadius_nonneg budget.grid.scale_nonnegative _
  let payment (position : Fin compared.entered.cache.parents.length)
      (fragment : SegmentPiece compared.entered.domain.geometry
        ((compared.entered.cache.parents[position.val]'position.isLt).edge.point 0)
        ((compared.entered.cache.parents[position.val]'position.isLt).edge.point 1)) : Rational :=
      12 * (((compared.entered.domain.patch.transported.cell fragment.column fragment.row).model.refine
          (budget.grid.index + 2)).bound +
        (((compared.entered.cache.covered.entry position).1.neighborhood 1).base.refine
          (sources.entry position).preparation.attached.source.selection.stage).bound) *
          bounds.weight form.denominatorPairs *
            Norm.Basic.normSq (fragment.lastPoint - fragment.firstPoint)
  have uniform (position : Fin compared.entered.cache.parents.length)
      (fragment : SegmentPiece compared.entered.domain.geometry
        ((compared.entered.cache.parents[position.val]'position.isLt).edge.point 0)
        ((compared.entered.cache.parents[position.val]'position.isLt).edge.point 1)) :
      payment position fragment ≤ c := by
    let gridModel := (compared.entered.domain.patch.transported.cell fragment.column fragment.row).model
    let sourceModel := ((compared.entered.cache.covered.entry position).1.neighborhood 1).base.model
    have gridBound := (gridModel.refine_bound (budget.grid.index + 2)).trans_le
      (Geometric.Basic.quarterRadius_scale_mono gridModel.bound_small _)
    have sourceBound :=
      (sourceModel.refine_bound (sources.entry position).preparation.attached.source.selection.stage).trans_le
        (Geometric.Basic.quarterRadius_scale_mono sourceModel.bound_small _)
    have gridStage := Geometric.Basic.quarterRadius_antitone
      (by decide : (0 : Rational) ≤ 1 / 16) (Nat.le_succ (budget.grid.index + 1))
    have sourceStage := Geometric.Basic.quarterRadius_antitone
      (by decide : (0 : Rational) ≤ 1 / 16)
      (floorAfter.trans (sources.entry position).floor_le_model_stage)
    have combined :
        Geometric.Basic.quarterRadius (1 / 16) (budget.grid.index + 1) +
          Geometric.Basic.quarterRadius (1 / 16) (budget.grid.index + 1) ≤ q := by
      calc
        _ = Geometric.Basic.quarterRadius (1 / 32) budget.grid.index := by
          simp only [Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ]
          have coefficient : (2 : Rational) * (1 / 16) * (1 / 4) = 1 / 32 := by
            change ((2 : Nat) : Rational) *
                (((1 : Nat) : Rational) / ((16 : Nat) : Rational)) *
                (((1 : Nat) : Rational) / ((4 : Nat) : Rational)) =
              ((1 : Nat) : Rational) / ((32 : Nat) : Rational)
            rewrite [Data.Rat.Fraction.Cast.natCast_eq_fromInt 2,
              Data.Rat.Fraction.Cast.natCast_eq_fromInt 1,
              Data.Rat.Fraction.Cast.natCast_eq_fromInt 16,
              Data.Rat.Fraction.Cast.natCast_eq_fromInt 4,
              Data.Rat.Fraction.Cast.natCast_eq_fromInt 32]
            decide +kernel
          calc
            _ = (2 * (1 / 16 : Rational) * (1 / 4)) * (1 / 4) ^ budget.grid.index := by ring1
            _ = _ := congrArg (fun value : Rational => value * (1 / 4) ^ budget.grid.index) coefficient
        _ ≤ _ := Geometric.Basic.quarterRadius_scale_mono (by decide) _
    have residual := (Arithmetic.add_le_add_direct
      (gridBound.trans gridStage) (sourceBound.trans sourceStage)).trans combined
    have weighted := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct residual (by decide : (0 : Rational) ≤ 12))
      (bounds.weight_nonnegative form.denominatorPairs)
    have endpoints := Box.normSq_sub_le_diagonalSq
      ((compared.entered.domain.patch.cell_refines fragment.column fragment.row).contains fragment.last_inside)
      ((compared.entered.domain.patch.cell_refines fragment.column fragment.row).contains fragment.first_inside)
    exact Arithmetic.mul_le_mul_direct weighted endpoints (Norm.Basic.normSq_nonneg _)
      (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide) qNonnegative)
        (bounds.weight_nonnegative _))
  have sourceFold := (splits.error_mono (left := payment) (right := fun _ _ => c)
    (fun position index => uniform position ((splits.get position).pieces[index.val]'index.isLt))).trans
      (RectangularSplits.error_constant_le bank cNonnegative)
  have gridFold := RectangularSplits.error_constant_le bank
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 16) gNonnegative)
  have fragmentPositive : 0 < f := budget.perFragment_positive
  have halfBound : f / 2 ≤ f := Field.divide_le_self fragmentPositive.le (by decide)
  have gridPaid : 64 * g ≤ f := by
    calc
      _ = (32 * g) * 2 := by ring1
      _ ≤ _ := (Field.le_div_iff_pos (by decide : (0 : Rational) < 2)).mp budget.ownership_accurate.le
  have cornerPaid : 32 * g ≤ f :=
    (Arithmetic.mul_le_mul_of_nonneg_right_direct
      (natCast_le_direct (m := 32) (n := 64) (by decide +kernel)) gNonnegative).trans gridPaid
  have delayed := Geometric.Basic.quarterRadius_antitone
    (by decide : (0 : Rational) ≤ 1 / 16) budget.grid_ge
  have analyticPaid : 4 * c ≤ f := by
    calc
      _ = 48 * Geometric.Basic.quarterRadius (1 / 16) budget.grid.index *
          bounds.weight form.denominatorPairs * placement.face.cell.box.diagonalSq := by
        change 4 * (12 * q * bounds.weight form.denominatorPairs * placement.face.cell.box.diagonalSq) = _
        ring1
      _ ≤ 48 * Geometric.Basic.quarterRadius (1 / 16) budget.minimumIndex *
          bounds.weight form.denominatorPairs * placement.face.cell.box.diagonalSq :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Arithmetic.mul_le_mul_of_nonneg_right_direct
            (Arithmetic.mul_le_mul_of_nonneg_left_direct delayed
              (natCast_le_direct (m := 0) (n := 48) (Nat.zero_le _)))
            (bounds.weight_nonnegative _)) placement.face.cell.box.diagonalSq_nonneg
      _ ≤ _ := budget.analytic_accurate.le.trans halfBound
  have combinedPaid : 64 * g + 4 * c ≤ 2 * f :=
    (Arithmetic.add_le_add_direct gridPaid analyticPaid).trans_eq (by ring1)
  have countsPaid := budget.full_count_accurate.le
  rewrite [Budget.Aggregate.countCoordinate_eq] at countsPaid
  have singlePaid : f ≤ target := by
    change budget.perFragment ≤ target
    rewrite [budget.perFragment_eq]
    exact Budget.Aggregate.perTerm_le budget.target_positive.le _
  have original := segment_integral_le_face placement piece compared domains same sources channel budget.grid shared
  calc
    _ ≤ 2 * (16 * g + 2 *
        (N * (F * (F * (16 * g))) + N * (F * (F * c)))) := by
      apply original.trans
      apply Arithmetic.mul_le_mul_of_nonneg_left_direct ?_ (by decide)
      apply Arithmetic.add_le_add_direct (Basic.le_refl _) ?_
      apply Arithmetic.mul_le_mul_of_nonneg_left_direct ?_ (by decide)
      exact Arithmetic.add_le_add_direct gridFold sourceFold
    _ = 32 * g + N * (F * (F * (64 * g + 4 * c))) := by ring1
    _ ≤ f + N * (F * (F * (2 * f))) :=
      Arithmetic.add_le_add_direct cornerPaid
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Arithmetic.mul_le_mul_of_nonneg_left_direct combinedPaid fCountNonnegative) fCountNonnegative)
          nNonnegative)
    _ = f + (2 * N) * (F * (F * f)) := by ring1
    _ ≤ target + (2 * N) * target := Arithmetic.add_le_add_direct singlePaid
      (Arithmetic.mul_le_mul_of_nonneg_left_direct countsPaid
        (Arithmetic.mul_nonneg_direct (by decide) nNonnegative))
    _ = target + (2 * N) * target + 0 := by ring1
    _ ≤ target + (2 * N) * target + target :=
      Arithmetic.add_le_add_direct (Basic.le_refl _) budget.target_positive.le
    _ = _ := by ring1

/-- Read the canonical corner increment minus the original source sample at every retained segment occurrence.

The supplied comparison spine determines each exact parent cache and source
product. The fold reads the same finite face bank and saved source cells in
their original order, including repeated segments and zero displacements.
-/
@[expose] def cornerSourceErrors (shared : FacePrimitiveBank basis index domains numerator pairs) (channel : Fin 6) :
    ∀ {start finish : Canonical} {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
      {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
      {pieces : CoveredSegments prepared} (assigned : AssignedSegments mesh pieces)
      (compared : Comparisons basis parentSheet assigned),
      OnSegments floor targets pieces (Comparisons.parentCaches basis parentSheet assigned compared) → List Canonical
  | _, _, _, _, _, _, .nil _ _, _, _ => []
  | _, _, _, _, _, _, .cons placement remaining, compared, saved =>
      let cache := compared.1.entered.cache
      (shared.edgeIncrement placement.location -
        (PathModel.mk (cells (parents := cache.parents) (covered := cache.covered) saved.1 channel)).integralSample) ::
        cornerSourceErrors shared channel remaining compared.2 saved.2
termination_by structural _ _ _ _ _ _ assigned _ _ => assigned

/-- The source-error list has one entry for each exact retained covered segment. -/
theorem cornerSourceErrors_length (shared : FacePrimitiveBank basis index domains numerator pairs) (channel : Fin 6) :
    ∀ {start finish : Canonical} {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
      {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
      {pieces : CoveredSegments prepared} (assigned : AssignedSegments mesh pieces)
      (compared : Comparisons basis parentSheet assigned)
      (saved : OnSegments floor targets pieces (Comparisons.parentCaches basis parentSheet assigned compared)),
      (cornerSourceErrors shared channel assigned compared saved).length = pieces.count
  | _, _, _, _, _, _, .nil _ _, _, _ => rfl
  | _, _, _, _, _, _, .cons _ remaining, compared, saved => by
      change (cornerSourceErrors shared channel remaining compared.2 saved.2).length + 1 = 1 + _
      rewrite [cornerSourceErrors_length shared channel remaining compared.2 saved.2]
      exact Nat.add_comm _ _
termination_by structural _ _ _ _ _ _ assigned _ _ => assigned

/-- Summing the retained errors gives the canonical corner sum minus the same complete original source-cell sample.

Each head separates by the original path-sample append law. The tail keeps
its supplied comparison caches and saved source preparations; no numerical
producer or observation is reconstructed while reading either side.
-/
theorem cornerSourceErrors_sum (shared : FacePrimitiveBank basis index domains numerator pairs) (channel : Fin 6) :
    ∀ {start finish : Canonical} {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
      {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
      {pieces : CoveredSegments prepared} (assigned : AssignedSegments mesh pieces)
      (compared : Comparisons basis parentSheet assigned)
      (saved : OnSegments floor targets pieces (Comparisons.parentCaches basis parentSheet assigned compared)),
      gaussianSum (cornerSourceErrors shared channel assigned compared saved) =
        gaussianSum (CornerRequests.AssignedSegments.cornerIncrements shared assigned) -
          (PathModel.mk (segmentCells pieces (Comparisons.parentCaches basis parentSheet assigned compared)
            saved channel).flatten).integralSample
  | _, _, _, _, _, _, .nil _ _, _, _ => by
      change (0 : Canonical) = 0 - 0
      exact (Basic.sub_self _).symm
  | _, _, _, _, _, _, .cons placement remaining, compared, saved => by
      change (shared.edgeIncrement placement.location - (PathModel.mk (cells saved.1 channel)).integralSample) +
        gaussianSum (cornerSourceErrors shared channel remaining compared.2 saved.2) =
          (shared.edgeIncrement placement.location +
            gaussianSum (CornerRequests.AssignedSegments.cornerIncrements shared remaining)) -
              (PathModel.mk (cells saved.1 channel ++
                (segmentCells _ (Comparisons.parentCaches basis parentSheet remaining compared.2)
                  saved.2 channel).flatten)).integralSample
      rewrite [PathModel.integralSample_mk_append,
        cornerSourceErrors_sum shared channel remaining compared.2 saved.2]
      ring1
termination_by structural _ _ _ _ _ _ assigned _ _ => assigned

/-- The canonical corner/source discrepancy is bounded by segment count times the retained squared-error sum.

Both readings use the same supplied source product and canonical face bank.
The finite sum estimate retains the actual per-occurrence residuals; local
request payments can subsequently bound those same computed errors.
-/
theorem cornerSource_le (shared : FacePrimitiveBank basis index domains numerator pairs) (channel : Fin 6)
    {start finish : Canonical} {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
    {pieces : CoveredSegments prepared} (assigned : AssignedSegments mesh pieces)
    (compared : Comparisons basis parentSheet assigned)
    (saved : OnSegments floor targets pieces (Comparisons.parentCaches basis parentSheet assigned compared)) :
    Norm.Basic.normSq (gaussianSum (CornerRequests.AssignedSegments.cornerIncrements shared assigned) -
      (PathModel.mk (segmentCells pieces (Comparisons.parentCaches basis parentSheet assigned compared)
        saved channel).flatten).integralSample) ≤
      (pieces.count : Rational) * gaussianNormSqSum (cornerSourceErrors shared channel assigned compared saved) := by
  have estimate := Norm.Sum.Basic.normSq_gaussianSum_le (cornerSourceErrors shared channel assigned compared saved)
  rewrite [← Norm.Basic.normSq_eq_canonical, cornerSourceErrors_sum,
    cornerSourceErrors_length] at estimate
  exact estimate

/-- Ordered local payments bound the discrepancy of the same canonical corner bank and retained source cells.

The paired-list witness pays every actual computed residual at its original
occurrence. Its scalar sum preserves all individual source, grid and corner
payments; the original segment count supplies the aggregate norm factor.
-/
theorem cornerSource_le_payments (shared : FacePrimitiveBank basis index domains numerator pairs) (channel : Fin 6)
    {start finish : Canonical} {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
    {pieces : CoveredSegments prepared} (assigned : AssignedSegments mesh pieces)
    (compared : Comparisons basis parentSheet assigned)
    (saved : OnSegments floor targets pieces (Comparisons.parentCaches basis parentSheet assigned compared))
    (payments : List Rational)
    (paid : List.Forall₂ (fun error payment => Norm.Basic.normSq error ≤ payment)
      (cornerSourceErrors shared channel assigned compared saved) payments) :
    Norm.Basic.normSq (gaussianSum (CornerRequests.AssignedSegments.cornerIncrements shared assigned) -
      (PathModel.mk (segmentCells pieces (Comparisons.parentCaches basis parentSheet assigned compared)
        saved channel).flatten).integralSample) ≤
      (pieces.count : Rational) * scalarSum payments :=
  (cornerSource_le shared channel assigned compared saved).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (Norm.Sum.Bounds.normSum_le_scalarSum paid)
      (natCast_le_direct (m := 0) (n := pieces.count) (Nat.zero_le pieces.count)))

/-- A common fragment allocation bounds every actual source error using the retained whole-parent count. -/
private theorem cornerSourceErrors_bounded (channel : Fin 6) (target : Rational)
    (nonnegative : 0 ≤ target) (parentCount : Nat) :
    ∀ {start finish : Canonical} {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
      {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
      {pieces : CoveredSegments prepared} (assigned : AssignedSegments mesh pieces)
      (compared : Comparisons basis parentSheet assigned)
      (_uses : Comparisons.UsesDomains domains basis parentSheet assigned compared)
      (_count : (ParentCaches.parents (Comparisons.parentCaches basis parentSheet assigned compared)).length ≤
        parentCount)
      (budgets : PrimitiveBudgets.Budgets basis parentSheet target assigned compared
        (some (Specification.Table.forms parameter channel)))
      (_below : PrimitiveBudgets.Budgets.IndicesBelow basis parentSheet index assigned compared budgets)
      (saved : OnSegments (index + 1) targets pieces
        (Comparisons.parentCaches basis parentSheet assigned compared))
      (shared : FacePrimitiveBank basis index domains
        ((Specification.Table.forms parameter channel).numerator.scale
          (Specification.Table.forms parameter channel).scale)
        (Specification.Table.forms parameter channel).denominatorPairs),
      ∀ error ∈ cornerSourceErrors shared channel assigned compared saved,
        Norm.Basic.normSq error ≤ 2 * ((parentCount : Rational) + 1) * target
  | _, _, _, _, _, _, .nil _ _, _, _, _, _, _, _, _, _, member => nomatch member
  | _, _, _, _, _, _, .cons placement remaining, compared, uses, countBound, budgets, below, saved, shared,
      error, member => by
      change (compared.1.entered.cache.parents ++
        ParentCaches.parents (Comparisons.parentCaches basis parentSheet remaining compared.2)).length ≤
          parentCount at countBound
      rewrite [Data.List.Append.length_append] at countBound
      have headCount := (Nat.le_add_right compared.1.entered.cache.parents.length _).trans countBound
      have tailCount := (Nat.le_add_left
        (ParentCaches.parents (Comparisons.parentCaches basis parentSheet remaining compared.2)).length _).trans
          countBound
      change error ∈ (shared.edgeIncrement placement.location -
        (PathModel.mk (cells saved.1 channel)).integralSample) ::
          cornerSourceErrors shared channel remaining compared.2 saved.2 at member
      cases member with
      | head =>
          have localBound := segment_integral_le_accuracy placement _ compared.1 domains uses.1 saved.1 channel
            (budgets.1.atGridIndex index below.1) (Nat.le_refl _) shared
          rewrite [sources_cells] at localBound
          have quarterNonnegative := Field.div_nonneg_direct nonnegative (by decide : (0 : Rational) ≤ 4)
          have countNonnegative := natCast_le_direct (m := 0) (n := parentCount) (Nat.zero_le _)
          have factorNonnegative : (0 : Rational) ≤ 2 * ((parentCount : Rational) + 1) :=
            Arithmetic.mul_nonneg_direct (by decide)
              (Arithmetic.add_le_add_direct countNonnegative (by decide : (0 : Rational) ≤ 1))
          exact localBound.trans ((Arithmetic.mul_le_mul_of_nonneg_right_direct
            (Arithmetic.mul_le_mul_of_nonneg_left_direct
              (Arithmetic.add_le_add_direct
                (natCast_le_direct (m := compared.1.entered.cache.parents.length) (n := parentCount) headCount)
                (Basic.le_refl 1)) (by decide : (0 : Rational) ≤ 2))
            quarterNonnegative).trans
              (Arithmetic.mul_le_mul_of_nonneg_left_direct
                (Field.divide_le_self nonnegative (by decide : (1 : Rational) ≤ 4)) factorNonnegative))
      | tail _ member =>
          exact cornerSourceErrors_bounded channel target nonnegative parentCount remaining compared.2
            uses.2 tailCount budgets.2 below.2 saved.2 shared error member
termination_by structural _ _ _ _ _ _ assigned _ _ _ _ _ _ _ _ _ => assigned

/-- A common grid stage and source floor pay the whole retained path to any positive accuracy.

The local target uses the original total parent count and segment count.
The supplied fragment budgets may be raised to one common bank index;
their actual source products share its successor floor. Uniform local
payments and the original finite-sum estimate then give the strict target
bound, including empty paths and repeated segment occurrences.
-/
theorem cornerSource_lt_accuracy (channel : Fin 6) {target : Rational} (positive : 0 < target)
    {start finish : Canonical} {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
    {pieces : CoveredSegments prepared} (assigned : AssignedSegments mesh pieces)
    (compared : Comparisons basis parentSheet assigned)
    (uses : Comparisons.UsesDomains domains basis parentSheet assigned compared) :
    let form := Specification.Table.forms parameter channel
    let parentCount := (ParentCaches.parents (Comparisons.parentCaches basis parentSheet assigned compared)).length
    let localTarget := Budget.Weighted.allowance (Budget.Aggregate.perTerm target pieces.count)
      (2 * (Budget.Aggregate.countCoordinate parentCount + 1))
    ∀ (budgets : PrimitiveBudgets.Budgets basis parentSheet localTarget assigned compared (some form))
      (_below : PrimitiveBudgets.Budgets.IndicesBelow basis parentSheet index assigned compared budgets)
      (saved : OnSegments (index + 1) targets pieces
        (Comparisons.parentCaches basis parentSheet assigned compared))
      (shared : FacePrimitiveBank basis index domains (form.numerator.scale form.scale) form.denominatorPairs),
    Norm.Basic.normSq (gaussianSum (CornerRequests.AssignedSegments.cornerIncrements shared assigned) -
      (PathModel.mk (segmentCells pieces (Comparisons.parentCaches basis parentSheet assigned compared)
        saved channel).flatten).integralSample) < target := by
  intro form parentCount localTarget budgets below saved shared
  have countNonnegative : (0 : Rational) ≤ Budget.Aggregate.countCoordinate parentCount := by
    rewrite [Budget.Aggregate.countCoordinate_eq]
    exact natCast_le_direct (m := 0) (n := parentCount) (Nat.zero_le _)
  have weightNonnegative : (0 : Rational) ≤ 2 * (Budget.Aggregate.countCoordinate parentCount + 1) :=
    Arithmetic.mul_nonneg_direct (by decide)
      (Arithmetic.add_le_add_direct countNonnegative (by decide : (0 : Rational) ≤ 1))
  have localPositive : 0 < localTarget := Budget.Weighted.allowance_positive
    (Budget.Aggregate.perTerm_positive positive pieces.count) weightNonnegative
  have uniform := cornerSourceErrors_bounded channel localTarget localPositive.le parentCount
    assigned compared uses (Nat.le_refl _) budgets below saved shared
  have errors := Norm.Sum.Bounds.normSum_le (cornerSourceErrors shared channel assigned compared saved)
    (2 * ((parentCount : Rational) + 1) * localTarget) uniform
  rewrite [cornerSourceErrors_length] at errors
  have weighted : 2 * ((parentCount : Rational) + 1) * localTarget ≤
      Budget.Aggregate.perTerm target pieces.count := by
    calc
      _ = (2 * (Budget.Aggregate.countCoordinate parentCount + 1)) * localTarget :=
        congrArg (fun count : Rational => 2 * (count + 1) * localTarget)
          (Budget.Aggregate.countCoordinate_eq parentCount).symm
      _ ≤ _ := Budget.Weighted.mul_allowance_le
        (Budget.Aggregate.perTerm_positive positive pieces.count).le weightNonnegative
  have segmentNonnegative := natCast_le_direct (m := 0) (n := pieces.count) (Nat.zero_le _)
  exact ((cornerSource_le shared channel assigned compared saved).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct errors segmentNonnegative)).trans_lt
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct weighted segmentNonnegative) segmentNonnegative).trans_lt
          (Budget.Aggregate.count_mul_perTerm_lt positive pieces.count))

namespace CornerComparison

/-- Allocate a local source target using the retained parent count and path segment count. -/
@[expose] def localTarget (target : Rational) (parents segments : Nat) : Rational :=
  Budget.Weighted.allowance (Budget.Aggregate.perTerm target segments)
    (2 * (Budget.Aggregate.countCoordinate parents + 1))

/-- A positive whole-path target gives a positive local source allocation at every retained count. -/
theorem localTarget_positive {target : Rational} (positive : 0 < target) (parents segments : Nat) :
    0 < localTarget target parents segments := by
  have nonnegative : (0 : Rational) ≤ Budget.Aggregate.countCoordinate parents := by
    rewrite [Budget.Aggregate.countCoordinate_eq]
    exact natCast_le_direct (m := 0) (n := parents) (Nat.zero_le _)
  exact Budget.Weighted.allowance_positive (Budget.Aggregate.perTerm_positive positive segments)
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 2)
      (Arithmetic.add_le_add_direct nonnegative (by decide : (0 : Rational) ≤ 1)))

end CornerComparison

set_option genInjectivity false in
/-- One retained source product and six canonical corner banks paid at a common grid stage.

The original comparison spine fixes every parent cache and face-domain
owner. Each requested positive target retains its actual fragment budgets.
One common source floor and the same saved observations pay all six forms;
the banks retain each original numerator, scale and odd denominator power.
-/
structure CornerComparison (requests : Data.Vector {value : Rational // 0 < value} 6) (minimum : Nat)
    {start finish : Canonical} {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
    {pieces : CoveredSegments prepared} (assigned : AssignedSegments mesh pieces)
    (compared : Comparisons basis parentSheet assigned) where
  /-- The actual odd-power scalar budget product for each original form and positive target. -/
  budgets : DependentVector (fun channel : Fin 6 => PrimitiveBudgets.Budgets basis parentSheet
    (CornerComparison.localTarget (requests channel).val
      (ParentCaches.parents (Comparisons.parentCaches basis parentSheet assigned compared)).length pieces.count)
    assigned compared (some (Specification.Table.forms parameter channel)))
  /-- The common grid index retained by every bank and source preparation. -/ index : Nat
  /-- The chosen grid stage respects the requested initial floor. -/ minimum_le_index : minimum ≤ index
  /-- Every original segment and form budget fits this same grid stage. -/
  indicesBelow : ∀ channel : Fin 6,
    PrimitiveBudgets.Budgets.IndicesBelow basis parentSheet index assigned compared (budgets.get channel)
  /-- The original source preparations shared by all six selectors at the successor floor. -/
  saved : OnSegments (index + 1) targets pieces (Comparisons.parentCaches basis parentSheet assigned compared)
  /-- The retained six-form numerical banks on the same original face-domain bank and grid stage. -/
  numerics : DependentVector (fun channel : Fin 6 =>
    let form := Specification.Table.forms parameter channel
    FacePrimitiveBank basis index domains (form.numerator.scale form.scale) form.denominatorPairs)
  /-- Each same-bank corner reading pays its requested accuracy against the same saved source sample. -/
  accurate : ∀ channel : Fin 6,
    Norm.Basic.normSq
      (gaussianSum (CornerRequests.AssignedSegments.cornerIncrements (numerics.get channel) assigned) -
        (PathModel.mk (segmentCells pieces (Comparisons.parentCaches basis parentSheet assigned compared)
          saved channel).flatten).integralSample) < (requests channel).val

constructive_injectivity CornerComparison

namespace CornerComparison

variable {requests : Data.Vector {value : Rational // 0 < value} 6} {minimum : Nat}
variable {start finish : Canonical} {path : ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
variable {owner : Owner ((Fibre.frameCurve frame).polynomial.eval start)} {prepared : PreparedPath path owner}
variable {pieces : CoveredSegments prepared} {assigned : AssignedSegments mesh pieces}
variable {compared : Comparisons basis parentSheet assigned}

/-- Certify six supplied banks and one actual saved source product from their retained fragment budgets.

All input cache values are stored directly. The common grid and source floor
pay the six actual samples without another preparation, source lookup or
face-bank construction.
-/
@[expose] def ofSources
    (uses : Comparisons.UsesDomains domains basis parentSheet assigned compared)
    (budgets : DependentVector (fun channel : Fin 6 => PrimitiveBudgets.Budgets basis parentSheet
      (localTarget (requests channel).val
        (ParentCaches.parents (Comparisons.parentCaches basis parentSheet assigned compared)).length pieces.count)
      assigned compared (some (Specification.Table.forms parameter channel))))
    (index : Nat) (minimum_le_index : minimum ≤ index)
    (below : ∀ channel : Fin 6,
      PrimitiveBudgets.Budgets.IndicesBelow basis parentSheet index assigned compared (budgets.get channel))
    (saved : OnSegments (index + 1) targets pieces (Comparisons.parentCaches basis parentSheet assigned compared))
    (numerics : DependentVector (fun channel : Fin 6 =>
      let form := Specification.Table.forms parameter channel
      FacePrimitiveBank basis index domains (form.numerator.scale form.scale) form.denominatorPairs)) :
    CornerComparison (domains := domains) (targets := targets) requests minimum assigned compared :=
  ⟨budgets, index, minimum_le_index, below, saved, numerics, fun channel =>
    cornerSource_lt_accuracy channel (requests channel).property assigned compared uses
      (budgets.get channel) (below channel) saved (numerics.get channel)⟩

/-- Compute the six scalar plans, common grid stage, original source products and paid corner banks.

The total parent and segment counts and form table are retained outside the channel
builders. The maximum of the actual stored budgets selects one grid index;
one preparation traversal produces the six shared source observations at
its successor floor. Every numerical bank uses the same original domains.
-/
def build (requests : Data.Vector {value : Rational // 0 < value} 6) (minimum : Nat)
    (assigned : AssignedSegments mesh pieces) (compared : Comparisons basis parentSheet assigned)
    (uses : Comparisons.UsesDomains domains basis parentSheet assigned compared) :
    CornerComparison (domains := domains) (targets := targets) requests minimum assigned compared := by
  let caches := Comparisons.parentCaches basis parentSheet assigned compared
  let parentCount := (ParentCaches.parents caches).length
  let segmentCount := pieces.count
  let forms := Specification.Table.forms parameter
  let budgets := DependentVector.ofFn (fun channel : Fin 6 =>
    PrimitiveBudgets.Budgets.build basis parentSheet
      (localTarget (requests channel).val parentCount segmentCount)
      (localTarget_positive (requests channel).property parentCount segmentCount)
      assigned compared (some (forms channel)))
  let index := max minimum (budgets.maximum
    (fun _ row => PrimitiveBudgets.Budgets.maximum basis parentSheet assigned compared row))
  have below (channel : Fin 6) :
      PrimitiveBudgets.Budgets.IndicesBelow basis parentSheet index assigned compared (budgets.get channel) := by
    apply PrimitiveBudgets.Budgets.indicesBelow_of_maximum_le basis parentSheet index assigned compared
      (budgets.get channel)
    exact (budgets.get_le_maximum
      (fun _ row => PrimitiveBudgets.Budgets.maximum basis parentSheet assigned compared row) channel).trans
        (Data.Nat.Order.le_max_right _ _)
  let saved := OnSegments.prepare (index + 1) targets pieces caches
  let numerics := FacePrimitiveBank.ofForms basis index domains forms
  exact ofSources uses budgets index (Data.Nat.Order.le_max_left _ _) below saved numerics

/-- Attach the six paid corner banks to the same original source Stage and its saved global source product.

The original parent list and its segment-cache identity determine views
of the supplied source product. Both input owners survive: the returned
Stage is the supplied whole value, and the corner record stores the actual
numerical banks and exact split source views. Point-found and positional
completions provide the same source-ownership law. The six bounds require
no new source preparation or caller-supplied sample inequality.
-/
def ofStage {sourceParents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {point : LiftedPoint 2}
    (covered : CoveredParents 1 sourceParents)
    (chain : CenteredPathChain sourceParents (start := point) (finish := point))
    (same : sourceParents = parents basis parentSheet pieces)
    (cache_eq : ParentCaches.build basis parentSheet pieces sourceParents same covered =
      Comparisons.parentCaches basis parentSheet assigned compared)
    (uses : Comparisons.UsesDomains domains basis parentSheet assigned compared)
    (budgets : DependentVector (fun channel : Fin 6 => PrimitiveBudgets.Budgets basis parentSheet
      (localTarget (requests channel).val
        (ParentCaches.parents (Comparisons.parentCaches basis parentSheet assigned compared)).length pieces.count)
      assigned compared (some (Specification.Table.forms parameter channel))))
    (gridIndex : Nat) (minimum_le_index : minimum ≤ gridIndex)
    (below : ∀ channel : Fin 6,
      PrimitiveBudgets.Budgets.IndicesBelow basis parentSheet gridIndex assigned compared (budgets.get channel))
    {sourceIndex : Nat}
    (saved : PreparedParents covered (gridIndex + 1) (CellEndpoints.Targets.build chain.path sourceIndex))
    (originalStage : Stage parameter ⟨point, chain.path⟩ sourceIndex)
    (exactSources : originalStage.sources = sources covered saved chain)
    (numerics : DependentVector (fun channel : Fin 6 =>
      let form := Specification.Table.forms parameter channel
      FacePrimitiveBank basis gridIndex domains (form.numerator.scale form.scale) form.denominatorPairs)) :
    let views := segmentSources pieces sourceParents same covered saved
    let transported := views.castCaches cache_eq
    let expected := ofSources uses budgets gridIndex minimum_le_index below transported numerics
    (original : {actual : Stage parameter ⟨point, chain.path⟩ sourceIndex // actual = originalStage}) ×
      {corners : CornerComparison (domains := domains)
          (targets := CellEndpoints.Targets.build chain.path sourceIndex) requests minimum assigned compared //
        corners = expected ∧ ∀ channel : Fin 6,
          Norm.Basic.normSq
            (gaussianSum (CornerRequests.AssignedSegments.cornerIncrements (corners.numerics.get channel) assigned) -
              (PathModel.mk (original.val.sources.cells channel)).integralSample) < (requests channel).val} := by
  intro views transported expected
  refine ⟨⟨originalStage, rfl⟩, ⟨expected, rfl, ?_⟩⟩
  intro channel
  have estimate := expected.accurate channel
  change Norm.Basic.normSq
    (gaussianSum (CornerRequests.AssignedSegments.cornerIncrements (numerics.get channel) assigned) -
      (PathModel.mk (segmentCells pieces (Comparisons.parentCaches basis parentSheet assigned compared)
        transported channel).flatten).integralSample) < (requests channel).val at estimate
  have lists := (congrArg List.flatten (OnSegments.castCaches_cells views cache_eq channel)).trans
    ((segmentSources_cells pieces sourceParents same covered saved channel).trans
      (sources_cells covered saved chain channel).symm)
  have stageCells := congrArg (fun sources => sources.cells channel) exactSources
  have originalCells := lists.trans stageCells.symm
  rewrite [originalCells] at estimate
  exact estimate

end CornerComparison

end CornerComparison

/-- The exact per-parent source comparison caches on the given requests' original patches.

The factory is independent of the proof spelling of the unique genus-one
holomorphic exponent. Each actual comparison retains its source model and
original primitive; empty words have only their empty product.
-/
@[expose] def RequestComparisons {target : Rational} :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (requests : RequestedParents count target parents) →
    PreparedParents (parameter := parameter) (frame := frame) requests.covered floor targets → Type
  | _, .nil, _prepared => PUnit
  | _, .cons request tail, prepared =>
      {value : Primitive.Comparison prepared.1.preparation.cell.models.valueZero.model //
        ∀ zero : basis.exponent = 0, value = prepared.1.primitiveComparison zero request.patchPrimitive} ×
        RequestComparisons tail prepared.2

/-- Compile each same retained primitive once against its actual source model, then retain the original tail. -/
def compareRequests {target : Rational} :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (requests : RequestedParents count target parents) →
    (prepared : PreparedParents (parameter := parameter) (frame := frame) requests.covered floor targets) →
      RequestComparisons requests prepared
  | _, .nil, _prepared => PUnit.unit
  | _, .cons request tail, prepared =>
      have zero : basis.exponent = 0 := by
        change basis.index.val = 0
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ basis.index.isLt)
      let first : {value : Primitive.Comparison prepared.1.preparation.cell.models.valueZero.model //
          ∀ zero : basis.exponent = 0, value = prepared.1.primitiveComparison zero request.patchPrimitive} :=
        ⟨prepared.1.primitiveComparison zero request.patchPrimitive, fun _ => rfl⟩
      let following := compareRequests tail prepared.2
      (first, following)

/-- The exact old inverse-error and source-allocation charges in literal original request order.

This scalar reads only actual request bounds/indices and physical parent
costs. It is available after target selection and before source observations.
It grants no smaller allowance to an unchanged old model.
-/
@[expose] def requestChargeSum (sourceAllowance : Rational) {target : Rational} :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    RequestedParents count target parents → Rational
  | _, .nil => 0
  | parent :: _, .cons request tail =>
      16 * (sourceAllowance + quarterRadius request.neighborhood.inverseErrorScale request.request.index) *
        PreparedParent.cost parent + requestChargeSum sourceAllowance tail

/-- The original error list obeys the exact computed local request charges without a paid-floor premise. -/
private theorem primitiveErrors_normSum_le_requestCharge {target : Rational} (zero : basis.exponent = 0) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (requests : RequestedParents count target parents) →
    (prepared : PreparedParents (parameter := parameter) (frame := frame) requests.covered floor targets) →
    gaussianNormSqSum (primitiveErrors requests prepared) ≤ requestChargeSum targets.localBound requests
  | _, .nil => fun _ => Data.Rat.Fraction.Order.Basic.le_refl 0
  | parent :: _, .cons request tail => fun prepared => by
      let head := prepared.1
      let remaining := prepared.2
      have headBound := PreparedParent.local_primitive_error_le
        (parameter := parameter) (frame := frame) (basis := basis) (floor := floor) (targets := targets)
        request head zero
      have following : gaussianNormSqSum (primitiveErrors tail remaining) ≤
          requestChargeSum targets.localBound tail :=
        primitiveErrors_normSum_le_requestCharge zero tail remaining
      change Canonical.normSq (request.request.model.primitive.value.eval (parent.edge.point 1) -
          request.request.model.primitive.value.eval (parent.edge.point 0) -
            head.preparation.cell.models.valueZero.model.integralSample) +
          gaussianNormSqSum (primitiveErrors tail remaining) ≤
        16 * (targets.localBound + quarterRadius request.neighborhood.inverseErrorScale request.request.index) *
          PreparedParent.cost parent + requestChargeSum targets.localBound tail
      rewrite [← Norm.Basic.normSq_eq_canonical]
      exact Arithmetic.add_le_add_direct headBound following

/-- The actual primitive/source error is paid by the original count and every actual retained inverse-error charge.

No coefficient-target hypothesis or old-stage upgrade is required. The
bound retains the actual old request index independently of source Targets,
model floor and programme indices, including zero-displacement occurrences.
-/
theorem request_error_le {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {target : Rational} (requests : RequestedParents count target parents)
    (prepared : PreparedParents requests.covered floor targets) {start finish : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := start) (finish := finish)) :
    Norm.Basic.normSq (gaussianSum requests.increments -
      (PathModel.mk ((sources requests.covered prepared chain).cells 0)).integralSample) ≤
        (parents.length : Rational) * requestChargeSum targets.localBound requests := by
  have zero : basis.exponent = 0 := by
    change basis.index.val = 0
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ basis.index.isLt)
  have original := Norm.Sum.Basic.normSq_gaussianSum_le (primitiveErrors requests prepared)
  rewrite [← Norm.Basic.normSq_eq_canonical, primitiveErrors_sum requests prepared chain,
    primitiveErrors_length requests prepared] at original
  exact original.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (primitiveErrors_normSum_le_requestCharge zero requests prepared)
    (Data.Rat.Fraction.Cast.Order.natCast_le_direct (m := 0) (n := parents.length) (Nat.zero_le parents.length)))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
