module
import Purelib.Algebra.NatCast
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings
public import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Init.Data.List.Lemmas
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
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

/-!
# Aggregate comparisons on automatically split prepared requests

Every retained fragment contributes its own ownership and analytic charge.
Finite Cauchy--Schwarz uses the full fragment count, not the original parent
count. Exact geometric telescoping then recovers the unchanged actual request
sum. Assembly consumes cached readings and scalar charges only.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums

public section

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings

open Purelib.Data.Rat

open Purelib.Geometry.Path.Gaussian

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedParentSplitting

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularPrimitiveBoundary

open Purelib.Riemann.Topology.PreparedRootSafeCycleStates

open Purelib.Algebra
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.RegularFaceInverseModels
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentPiece SegmentSplit)
open Purelib.Riemann.Integration.PreparedParentSplitting (ParentSplits PreparedSplitMesh)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Meshes.RectangularFaceModels (RectangularPatch)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentReadings (FragmentBounds FragmentReading)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (ParentReached)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests (PeriodSample)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Approximation.Rational.Budget.Aggregate (countCoordinate countCoordinate_eq)

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
  {differential : Differential genus} {bounds :
    FragmentBounds patch differential}
  {globalBounds : PrimitiveOverlapBounds face.clearance
    (Purelib.Riemann.Readings.PreparedPrimitiveSamples.differentialNumerator differential)}
  {tolerance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {gridRequest :
    GridPrimitiveAccuracy globalBounds columns tolerance}
  {primitives : Primitives
    (Purelib.Riemann.Branches.RectangularSheetGauge.Transitions.oriented (patch.sheets.refine
    gridRequest.index).transitions (patch.sheets.refine gridRequest.index).gauge)
    (Purelib.Riemann.Readings.PreparedPrimitiveSamples.differentialNumerator differential)}
  {anchors : PrimitiveAnchors primitives} {offsets :
    LinearAlgebra.Grid.Offsets anchors.edges}
  {cuts : GridCuts geometry} {meshParents : List
    (CenteredEdge curve differential)} {extra : List
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {mesh : PreparedSplitMesh cuts meshParents extra}
  {count : Nat} {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- Gaussian summation preserves concatenation of the two original finite lists. -/
private theorem sum_append (first last : List InverseRootPolynomial.Gaussian) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (first ++ last) = Data.Gaussian.Norm.Sum.Basic.gaussianSum first
      + Data.Gaussian.Norm.Sum.Basic.gaussianSum last := by
  induction first with
  | nil =>
    change Data.Gaussian.Norm.Sum.Basic.gaussianSum last = 0 + Data.Gaussian.Norm.Sum.Basic.gaussianSum last;
      ring1
  | cons first rest ih =>
      change first + Data.Gaussian.Norm.Sum.Basic.gaussianSum (rest ++ last) = (first +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum rest) + Data.Gaussian.Norm.Sum.Basic.gaussianSum last
      rw [ih]
      ring1

/-- The sum of squared Gaussian norms preserves finite-list concatenation. -/
private theorem normSum_append (first last : List InverseRootPolynomial.Gaussian) :
    Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum (first ++ last) = Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum
      first + Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum last := by
  induction first with
  | nil =>
    change Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum last = 0 + Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum
      last; ring1
  | cons first rest ih =>
      change Data.Gaussian.Basic.Canonical.normSq first + Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum (rest ++ last)
        =
        (Data.Gaussian.Basic.Canonical.normSq first + Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum rest) +
          Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum last
      rw [ih]
      ring1

set_option genInjectivity false in
/-- Retain the readings of every piece of one actual request.

Each reading is indexed by the original request and its segment piece. The dependent tail preserves the order of the
supplied split without choosing new parents or reevaluating cached observations. -/
inductive FragmentReadings (bounds : FragmentReadings.FragmentBounds patch differential)
    (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets mesh.mesh.surface)
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} (request :
      UniformPreparedRequests.LocalRequest parent count target) :
    List (RectangularSegmentSplitting.SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1)) → Type 2
  /-- The empty original fragment or request spine retains no readings. -/ | nil :
    FragmentReadings bounds readings request []
  /-- Retain the original head reading or fragment bank together with the exact remaining dependent tail. -/ | cons
    {piece : RectangularSegmentSplitting.SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1)}
      {pieces : List (RectangularSegmentSplitting.SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1))}
      (reading : FragmentReadings.FragmentReading (gridRequest := gridRequest) bounds readings request piece)
      (tail : FragmentReadings bounds readings
        request pieces) : FragmentReadings bounds
        readings request (piece :: pieces)

constructive_injectivity FragmentReadings

namespace FragmentReadings

variable {readings : SharedPrimitiveValues anchors offsets
  mesh.mesh.surface}
  {parent : CenteredEdge curve differential} {request :
    LocalRequest parent count target}

/-- Read and certify every original fragment against its unchanged actual request using the retained shared mesh values.

The supplied membership and reachability witnesses refer to the original split and face. Structural recursion retains
the same head certificate and dependent tail in the supplied piece order. -/
@[expose] def build (bounds : FragmentReadings.FragmentBounds patch differential) (readings :
  RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets mesh.mesh.surface)
    (request : UniformPreparedRequests.LocalRequest parent count target) {split :
      RectangularSegmentSplitting.SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1)}
    (member : ParentSplits.Member split mesh.splits)
    (pieces : List (RectangularSegmentSplitting.SegmentPiece geometry (parent.edge.point 0) (parent.edge.point 1)))
    (included : ∀ piece ∈ pieces, piece ∈ split.pieces)
    (reached : PreparedFaceTracePrefixes.ParentReached face.cell.box (models.frame.owners sheet) parent) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings (gridRequest := gridRequest) bounds
      readings request pieces :=
  match pieces with
  | [] => .nil
  | piece :: rest =>
      .cons (FragmentReading.build bounds readings request member piece (included _ List.mem_cons_self)
        reached)
        (build bounds readings
          request member rest (fun piece present => included piece (List.mem_cons_of_mem _ present))
          reached)

/-- Read the cached shared primitive increments in the exact original fragment order.

Each head contributes its retained value without reevaluating a primitive. The remaining values follow the original
dependent reading spine. -/
@[expose] def values : {pieces : List (RectangularSegmentSplitting.SegmentPiece geometry (parent.edge.point 0)
  (parent.edge.point 1))} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings (gridRequest := gridRequest) bounds
      readings request pieces → List InverseRootPolynomial.Gaussian
  | _, .nil => []
  | _, .cons reading tail => reading.value :: tail.values

/-- Sum the cached ownership and analytic charges over the original fragment occurrences.

The ordered spine supplies each original scalar charge once. This fold retains repeated occurrences and reads the same
cached head and tail. -/
@[expose] def chargeSum : {pieces : List (RectangularSegmentSplitting.SegmentPiece geometry (parent.edge.point 0)
  (parent.edge.point 1))} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings (gridRequest := gridRequest) bounds
      readings request pieces → InverseRootPolynomial.Coordinate
  | _, .nil => 0
  | _, .cons reading tail => reading.charge + tail.chargeSum

/-- Sum only the original request-to-cell analytic charges over the retained fragments.

The retained request and piece indices determine every charge. Structural recursion sums those original scalar
observations without changing their bounds or geometric owners. -/
@[expose] def analyticChargeSum : {pieces : List (RectangularSegmentSplitting.SegmentPiece geometry (parent.edge.point
  0) (parent.edge.point 1))} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings (gridRequest := gridRequest) bounds
      readings request pieces → InverseRootPolynomial.Coordinate
  | _, .nil => 0
  | piece :: _, .cons _ tail => bounds.charge piece request gridRequest.index + tail.analyticChargeSum

/-- Read each cached shared fragment value minus its unchanged original request primitive increment. -/
private def errors : {pieces : List (RectangularSegmentSplitting.SegmentPiece geometry (parent.edge.point 0)
  (parent.edge.point 1))} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings (gridRequest := gridRequest) bounds
      readings request pieces → List InverseRootPolynomial.Gaussian
  | _, .nil => []
  | piece :: _, .cons reading tail =>
      (reading.value - (request.request.model.primitive.value.eval piece.lastPoint -
        request.request.model.primitive.value.eval piece.firstPoint)) ::
          errors tail

variable {pieces : List (SegmentPiece geometry (parent.edge.point 0)
  (parent.edge.point 1))}

/-- The retained value list has exactly the original full fragment count.

Each retained reading contributes one cached value. Structural induction on the original piece spine preserves its exact
length. -/
theorem values_length (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings
  (gridRequest := gridRequest) bounds readings request pieces) :
    entries.values.length = pieces.length := by
  induction entries with
  | nil => rfl
  | cons reading tail ih => exact congrArg Nat.succ ih

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings
/-- Separate the total fragment charge into the original shared-grid cost and twice the actual analytic charge sum.

The displayed full fragment count weights the shared-grid charge. Structural induction on the retained readings adds the
original analytic charges without changing their factors. -/
theorem chargeSum_eq (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings
  (gridRequest := gridRequest) bounds readings request pieces) :
    entries.chargeSum = 32 * Aggregate.countCoordinate pieces.length * gridRequest.globalBound + 2 *
      entries.analyticChargeSum := by
  simp only [Aggregate.countCoordinate_eq]
  induction entries with
  | nil => change (0 : InverseRootPolynomial.Coordinate) = 32 * 0 * gridRequest.globalBound + 2 * 0; ring1
  | cons reading tail ih =>
      simp only [chargeSum,
        analyticChargeSum,
        reading.charge_eq, List.length_cons, NatCast.add, Nat.cast_one, ih]
      ring1

/-- The cached fragment values are exactly the differences of the retained shared endpoint readings.

Each entry uses its original contact equalities to identify the two cached endpoint observations. List-constructor
congruence retains the unchanged ordered tail. -/
private theorem values_eq (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings
  (gridRequest := gridRequest) bounds readings request pieces) :
    entries.values = pieces.map (fun piece => (SharedPrimitiveValues.atPoint readings) piece.lastPoint -
      (SharedPrimitiveValues.atPoint readings) piece.firstPoint) := by
  induction entries with
  | nil => rfl
  | cons reading tail ih =>
      rewrite [values, List.map_cons, ih, reading.value_eq, ← reading.contact.last_eq, ← reading.contact.first_eq,
        SharedPrimitiveValues.atPoint_coordinate readings, SharedPrimitiveValues.atPoint_coordinate readings]
      exact Eq.refl _

end

/-- The cached shared readings telescope over the original retained fragment or parent chain. -/
theorem sum_eq_increment {split : RectangularSegmentSplitting.SegmentSplit cuts (parent.edge.point 0) (parent.edge.point
  1)}
    (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings (gridRequest := gridRequest)
      bounds readings request split.pieces) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum entries.values = (SharedPrimitiveValues.atPoint readings)
      (parent.edge.point 1) - (SharedPrimitiveValues.atPoint readings) (parent.edge.point 0) := by
  rw [entries.values_eq]
  exact split.telescope (SharedPrimitiveValues.atPoint readings)

/-- There is one original request discrepancy for each retained fragment occurrence.

Each retained reading contributes one discrepancy. Structural induction follows the same original piece spine and
preserves its length. -/
private theorem errors_length (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings
  (gridRequest := gridRequest) bounds readings request pieces) :
    (errors entries).length = pieces.length
      := by
  induction entries with
  | nil => rfl
  | cons reading tail ih => exact congrArg Nat.succ ih

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings in
/-- The finite fragment-error sum is the shared reading sum minus the unchanged original request increment sum. -/
private theorem errors_sum (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings
  (gridRequest := gridRequest) bounds readings request pieces) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (errors entries) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum entries.values - Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (pieces.map fun piece =>
      request.request.model.primitive.value.eval piece.lastPoint - request.request.model.primitive.value.eval
        piece.firstPoint) := by
  induction entries with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons reading tail ih =>
    simp only [errors, values,
      List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih]; ring1

/-- The sum of squared retained fragment errors is bounded by their actual cached charge sum. -/
private theorem errors_bounded (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings
  (gridRequest := gridRequest) bounds readings request pieces) :
    Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum
      (errors entries) ≤ entries.chargeSum
      := by
  induction entries with
  | nil => exact le_rfl
  | cons reading tail ih =>
      have scalar := reading.accurate
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact Fraction.Order.Arithmetic.add_le_add_direct scalar ih

end FragmentReadings

set_option genInjectivity false in
/-- The dependent spine retains the original requests and their actual splits, including repeated parent occurrences.

The head couples one retained fragment bank to its original split and request. Its dependent tail keeps the remaining
parent occurrences in their supplied order. -/
inductive SplitReadings (bounds : FragmentReadings.FragmentBounds patch differential)
    (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets mesh.mesh.surface) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
      PreparedParentSplitting.ParentSplits cuts parents →
      UniformPreparedRequests.RequestedParents count target parents → Type 2
  /-- The empty original fragment or request spine retains no readings. -/ | nil :
    SplitReadings bounds readings .nil .nil
  /-- Retain the original head reading or fragment bank together with the exact remaining dependent tail. -/ | cons
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {parents : List
    (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      {split : RectangularSegmentSplitting.SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1)} {splits :
        PreparedParentSplitting.ParentSplits cuts parents}
      {request : UniformPreparedRequests.LocalRequest parent count target} {requests :
        UniformPreparedRequests.RequestedParents count target parents}
      (entries : FragmentReadings (gridRequest :=
        gridRequest) bounds readings request split.pieces)
      (tail : SplitReadings bounds readings splits
        requests) :
      SplitReadings bounds readings (.cons split
        splits) (.cons request requests)

constructive_injectivity SplitReadings

namespace SplitReadings

variable {readings : SharedPrimitiveValues anchors offsets
  mesh.mesh.surface}

/-- Assemble the original request-aligned fragment reading banks, preserving repeated parent occurrences and exact split
identities.

Each supplied request is coupled to its original parent split. The inclusion and face-reachability witnesses pass to the
dependent tail while the head consumes the retained shared readings. -/
@[expose] def build (bounds : FragmentReadings.FragmentBounds patch differential) (readings :
  RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets mesh.mesh.surface)
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (splits :
      PreparedParentSplitting.ParentSplits cuts parents)
    (requests : UniformPreparedRequests.RequestedParents count target parents)
    (included : ∀ {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} (split :
      RectangularSegmentSplitting.SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1)),
      ParentSplits.Member split splits → ParentSplits.Member split mesh.splits)
    (reached : ∀ parent ∈ parents, PreparedFaceTracePrefixes.ParentReached face.cell.box (models.frame.owners sheet)
      parent) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings (gridRequest := gridRequest) bounds
      readings splits requests :=
  match splits, requests with
  | .nil, .nil => .nil
  | .cons split tail, .cons request requests =>
      .cons (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings.build bounds readings request
        (included split (.here tail)) split.pieces (fun _ member => member)
        (reached _ List.mem_cons_self))
        (build bounds readings tail
          requests (fun part member => included part (.there split member))
          (fun parent member => reached parent (List.mem_cons_of_mem _ member)))
termination_by structural splits

/-- Read the cached shared primitive increments in the exact original fragment order.

Each head contributes its retained value without reevaluating a primitive. The remaining values follow the original
dependent reading spine. -/
@[expose] def values : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {splits :
  PreparedParentSplitting.ParentSplits cuts parents} →
    {requests : UniformPreparedRequests.RequestedParents count target parents} →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings (gridRequest := gridRequest) bounds
      readings splits requests → List InverseRootPolynomial.Gaussian
  | _, _, _, .nil => []
  | _, _, _, .cons entries tail => entries.values ++ tail.values

/-- Sum the cached ownership and analytic charges over the original fragment occurrences.

The ordered spine supplies each original scalar charge once. This fold retains repeated occurrences and reads the same
cached head and tail. -/
@[expose] def chargeSum : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {splits :
  PreparedParentSplitting.ParentSplits cuts parents} →
    {requests : UniformPreparedRequests.RequestedParents count target parents} →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings (gridRequest := gridRequest) bounds
      readings splits requests → InverseRootPolynomial.Coordinate
  | _, _, _, .nil => 0
  | _, _, _, .cons entries tail => entries.chargeSum + tail.chargeSum

/-- Sum only the original request-to-cell analytic charges over the retained fragments.

The retained request and piece indices determine every charge. Structural recursion sums those original scalar
observations without changing their bounds or geometric owners. -/
@[expose] def analyticChargeSum : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
  {splits : PreparedParentSplitting.ParentSplits cuts parents} →
    {requests : UniformPreparedRequests.RequestedParents count target parents} →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings (gridRequest := gridRequest) bounds
      readings splits requests → InverseRootPolynomial.Coordinate
  | _, _, _, .nil => 0
  | _, _, _, .cons entries tail => entries.analyticChargeSum + tail.analyticChargeSum

/-- Read each cached shared fragment value minus its unchanged original request primitive increment. -/
private def errors : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {splits :
  PreparedParentSplitting.ParentSplits cuts parents} →
    {requests : UniformPreparedRequests.RequestedParents count target parents} →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings (gridRequest := gridRequest) bounds
      readings splits requests → List InverseRootPolynomial.Gaussian
  | _, _, _, .nil => []
  | _, _, _, .cons entries tail => Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings.errors
    entries ++ errors tail

variable {parents : List (CenteredEdge curve differential)}
  {splits : ParentSplits cuts parents}
  {requests : RequestedParents count target parents}

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings
/-- The retained value list has exactly the original full fragment count.

The dependent reading spine follows the supplied split occurrences. Each head contributes its original number of pieces,
and concatenation adds the retained counts. -/
theorem values_length (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings (gridRequest
  := gridRequest) bounds readings splits requests) :
    entries.values.length = splits.pieceCount := by
  induction entries with
  | nil => rfl
  | @cons parent parents split splits request requests entries tail ih =>
      rewrite [values, Append.length_append, entries.values_length, ih, ParentSplits.pieceCount, split.count_eq]
      exact Eq.refl _

/-- Separate the total fragment charge into the original shared-grid cost and twice the actual analytic charge sum.

The displayed full fragment count weights the shared-grid charge. Structural induction on the retained readings adds the
original analytic charges without changing their factors. -/
theorem chargeSum_eq (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings (gridRequest
  := gridRequest) bounds readings splits requests) :
    entries.chargeSum = 32 * Aggregate.countCoordinate splits.pieceCount * gridRequest.globalBound + 2 *
      entries.analyticChargeSum := by
  induction entries with
  | nil =>
    change (0 : InverseRootPolynomial.Coordinate) = 32 * Aggregate.countCoordinate 0 * gridRequest.globalBound + 2 * 0;
      rw [Aggregate.countCoordinate_eq]; ring1
  | @cons parent parents split splits request requests entries tail ih =>
      simp only [chargeSum, analyticChargeSum,
        entries.chargeSum_eq, ih, ParentSplits.pieceCount,
        split.count_eq, Aggregate.countCoordinate_eq, NatCast.add]
      ring1

/-- The cached shared readings telescope over the original retained fragment or parent chain. -/
theorem sum_eq_increment (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings
  (gridRequest := gridRequest) bounds readings splits requests)
    {start finish : Lifted.Basic.LiftedPoint 2} (chain : PreparedDirectDyadicRefinements.CenteredPathChain parents
      (start := start) (finish := finish)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum entries.values = (SharedPrimitiveValues.atPoint readings)
      finish.coordinate - (SharedPrimitiveValues.atPoint readings) start.coordinate := by
  induction chain with
  | nil point => cases splits; cases requests; cases entries; change (0 : InverseRootPolynomial.Gaussian) = _ - _; ring1
  | cons parent tail ih =>
      cases splits with
      | cons split splits =>
          cases requests with
          | cons request requests =>
              cases entries with
              | cons entries rest =>
                  rw [values, Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.sum_append,
                    entries.sum_eq_increment, ih rest, parent.edge.point_zero, parent.edge.point_one]
                  ring1

end

/-- There is one original request discrepancy for each retained fragment occurrence.

Each retained fragment supplies one discrepancy. The dependent split spine concatenates these error lists in the
original parent order, preserving their total piece count. -/
private theorem errors_length (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings
  (gridRequest := gridRequest) bounds readings splits requests) :
    (errors entries).length =
      splits.pieceCount := by
  induction entries with
  | nil => rfl
  | @cons parent parents split splits request requests entries tail ih =>
      rewrite [errors, Append.length_append,
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings.errors_length, ih,
        ParentSplits.pieceCount, split.count_eq]
      exact Eq.refl _

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings in
/-- The finite fragment-error sum is the shared reading sum minus the unchanged original request increment sum. -/
private theorem errors_sum (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings
  (gridRequest := gridRequest) bounds readings splits requests) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (errors entries) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum entries.values - Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (splits.increments requests) := by
  induction entries with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons entries tail ih =>
      simp only [errors, values,
        ParentSplits.increments, Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.sum_append,
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentReadings.errors_sum, ih]
      ring1

/-- The sum of squared retained fragment errors is bounded by their actual cached charge sum. -/
private theorem errors_bounded (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings
  (gridRequest := gridRequest) bounds readings splits requests) :
    Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum
      (errors entries) ≤ entries.chargeSum :=
      by
  induction entries with
  | nil => exact le_rfl
  | cons entries tail ih =>
    rw [errors,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.normSum_append]; exact add_le_add
      entries.errors_bounded ih

/-- The cached aggregate differs from the unchanged original request increment sum by at most its retained bound. -/
theorem accurate (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings (gridRequest :=
  gridRequest) bounds readings splits requests) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum entries.values -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments) ≤
      Aggregate.countCoordinate splits.pieceCount * entries.chargeSum := by
  rw [← splits.sum_eq requests, ← entries.errors_sum, Aggregate.countCoordinate_eq]
  have bounded := Data.Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le
    (errors entries)
  rw [entries.errors_length] at bounded
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact bounded.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct entries.errors_bounded
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))

end SplitReadings

set_option genInjectivity false in
/-- Cached reduction against the original actual requests. Generated summaries may use the same exact data equations and
accuracy certificate.

The record retains the reading spine, ordered value list, count and charge total together with their exact equations.
Its discrepancy bound refers to these same caches and original requests. -/
structure FragmentSum (bounds : FragmentReadings.FragmentBounds patch differential)
    (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets mesh.mesh.surface)
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (splits :
      PreparedParentSplitting.ParentSplits cuts parents)
    (requests : UniformPreparedRequests.RequestedParents count target parents) where
  /-- The retained readings indexed by the original splits and unchanged actual requests. -/ entries :
    SplitReadings (gridRequest := gridRequest) bounds
    readings splits requests
  /-- The cached ordered list of actual shared fragment values. -/ values : List InverseRootPolynomial.Gaussian
  /-- The cached list is exactly the values of the retained original reading spine. -/ values_eq : values =
    entries.values
  /-- The cached full count of original fragment occurrences. -/ fragmentCount : Nat
  /-- The cached count is exactly the original retained splits' piece count. -/ fragmentCount_eq : fragmentCount =
    splits.pieceCount
  /-- The cached Gaussian sum of the original shared fragment readings. -/ value : InverseRootPolynomial.Gaussian
  /-- The cached aggregate is exactly the finite sum of its retained value list. -/ value_eq : value =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum values
  /-- The cached total of the original fragment charges. -/ chargeSum : InverseRootPolynomial.Coordinate
  /-- The cached total is exactly the charge sum of the retained original reading spine. -/ chargeSum_eq : chargeSum =
    entries.chargeSum
  /-- The cached full-fragment-count discrepancy bound. -/ bound : InverseRootPolynomial.Coordinate
  /-- The cached bound multiplies the exact original fragment count by the retained total charge. -/ bound_eq : bound =
    Aggregate.countCoordinate fragmentCount * chargeSum
  /-- The cached aggregate differs from the unchanged original request increment sum by at most its retained bound. -/
    accurate : Data.Gaussian.Norm.Basic.normSq (value - Data.Gaussian.Norm.Sum.Basic.gaussianSum
    requests.increments) ≤ bound

constructive_injectivity FragmentSum

namespace FragmentSum

variable {readings : SharedPrimitiveValues anchors offsets
  mesh.mesh.surface}
  {parents : List (CenteredEdge curve differential)} {splits :
    ParentSplits cuts parents}
  {requests : RequestedParents count target parents}

/-- Fold cached values and charges, without evaluating request polynomials or recomputing mesh geometry, roots, or
analytic comparisons.

The resulting record retains the original reading spine and its exact value-list, count and charge equations. Its
discrepancy proof uses those same caches and original request increments. -/
@[expose] def build (entries : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings (gridRequest :=
  gridRequest) bounds readings splits requests) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentSum (gridRequest := gridRequest) bounds readings
      splits requests :=
  let values := entries.values
  let fragmentCount := values.length
  let chargeSum := entries.chargeSum
  { entries := entries, values := values, values_eq := rfl
    fragmentCount := fragmentCount, fragmentCount_eq := entries.values_length
    value := Data.Gaussian.Norm.Sum.Basic.gaussianSum values, value_eq := rfl
    chargeSum := chargeSum, chargeSum_eq := rfl
    bound := Aggregate.countCoordinate fragmentCount * chargeSum, bound_eq := rfl
    accurate := by
      change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum entries.values -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments) ≤
        Aggregate.countCoordinate entries.values.length * entries.chargeSum
      rw [entries.values_length]
      exact entries.accurate }

/-- The cached aggregate value is exactly the difference of the original shared readings at the retained chain
endpoints. -/
theorem value_eq_increment (summary : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentSum
  (gridRequest := gridRequest) bounds readings splits requests)
    {start finish : Lifted.Basic.LiftedPoint 2} (chain : PreparedDirectDyadicRefinements.CenteredPathChain parents
      (start := start) (finish := finish))
    (first last : Fin mesh.mesh.surface.mesh.vertices.length)
    (firstEq : mesh.mesh.surface.mesh.coordinate first = start.coordinate)
    (lastEq : mesh.mesh.surface.mesh.coordinate last = finish.coordinate) :
    summary.value = readings.values last - readings.values first := by
  rw [summary.value_eq, summary.values_eq, summary.entries.sum_eq_increment chain, ← firstEq, ← lastEq,
    SharedPrimitiveValues.atPoint_coordinate readings, SharedPrimitiveValues.atPoint_coordinate readings]

/-- The aggregate discrepancy bound retains the full actual fragment count in both grid and analytic charge factors. -/
theorem bound_eq_full_count (summary : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentSum
  (gridRequest := gridRequest) bounds readings splits requests) :
    summary.bound = Aggregate.countCoordinate splits.pieceCount *
      (32 * Aggregate.countCoordinate splits.pieceCount * gridRequest.globalBound + 2 *
        summary.entries.analyticChargeSum) := by
  rw [summary.bound_eq, summary.fragmentCount_eq, summary.chargeSum_eq, summary.entries.chargeSum_eq]

/-- The actual retained fragment count is bounded by the original parent count and coarse-grid dimensions. -/
theorem fragmentCount_le (summary : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentSum (gridRequest
  := gridRequest) bounds readings splits requests) :
    summary.fragmentCount ≤ parents.length * (columns + rows + 5) := by
  rw [summary.fragmentCount_eq]
  exact splits.pieceCount_le

/-- The retained aggregate discrepancy bound is nonnegative. -/
theorem bound_nonnegative (summary : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentSum
  (gridRequest := gridRequest) bounds readings splits requests) :
    0 ≤ summary.bound := (Data.Gaussian.Norm.Basic.normSq_nonneg _).trans summary.accurate

/-- The cached fragment aggregate satisfies its original bound against the retained controlled primitive request. -/
theorem controlled_accurate {request : PreparedControlledPrimitiveRequests.ControlledSumRequest parents count target}
    (summary : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentSum (gridRequest := gridRequest)
      bounds readings splits request.requests) :
    Data.Gaussian.Norm.Basic.normSq (summary.value - request.primitiveSum) ≤ summary.bound := by
  rw [request.primitiveSum_eq, request.increments_eq]
  exact summary.accurate

/-- The cached fragment aggregate and actual original period sample satisfy the combined fragment and sampling error
bound. -/
theorem period_accurate {source : Differentials.Basic.Differential genus} {root : Gaussian.Name.Basic.Named}
    {initial : PreparedRefinementRootEndpoints.RootClosedState curve source root} {targets : List
      (Differentials.Basic.Differential genus)}
    {splits : PreparedParentSplitting.ParentSplits cuts (initial.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge differential))}
    {request : PreparedControlledPrimitiveRequests.ControlledSumRequest (initial.state.parents.map
      (PreparedEdgeRecasting.recastCenteredEdge differential)) count target}
    (summary : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentSum (gridRequest := gridRequest)
      bounds readings splits request.requests) {minimumStage : Nat}
    (sample : PreparedPeriodPrimitiveRequests.PeriodSample initial targets differential request minimumStage) :
    Data.Gaussian.Norm.Basic.normSq (summary.value - sample.sample) < 2 * summary.bound + 2 * target := by
  have identity : summary.value - sample.sample =
      (summary.value - request.primitiveSum) + (request.primitiveSum - sample.sample) := by ring1
  rw [identity]
  have firstBound := summary.controlled_accurate
  have lastBound := sample.accurate
  have triangle := Data.Gaussian.Norm.Bounds.normSq_add_le_two
    (summary.value - request.primitiveSum) (request.primitiveSum - sample.sample)
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at triangle firstBound
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact triangle.trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      (by decide : (0 : Fraction.Rational) < 2)
      ((Fraction.Order.Arithmetic.add_le_add_direct firstBound le_rfl).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct lastBound summary.bound))).trans_eq (by ring1))

end FragmentSum

/-- Total assembly for all actual contained parents, including those that cross coarse-cell boundaries. No caller cell
assignment is required.

The supplied split mesh and reachability witnesses determine the original fragment readings. Their dependent reading
banks are folded into one cached summary with the exact original requests. -/
@[expose] def fragmentSum (mesh : PreparedParentSplitting.PreparedSplitMesh cuts meshParents extra) (bounds :
  FragmentReadings.FragmentBounds patch differential)
    (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets mesh.mesh.surface)
    (requests : UniformPreparedRequests.RequestedParents count target meshParents)
    (reached : ∀ parent ∈ meshParents, PreparedFaceTracePrefixes.ParentReached face.cell.box (models.frame.owners sheet)
      parent) :
    FragmentSum (gridRequest := gridRequest) bounds readings
      mesh.splits requests :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.FragmentSum.build
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums.SplitReadings.build bounds readings mesh.splits
    requests (fun _ member => member)
    reached)

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentSums
