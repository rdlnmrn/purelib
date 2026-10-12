module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Vector.Dependent
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Readings.PrimitiveAreaBounds

public import Purelib.Approximation.Budget.RequestedLengthBudget
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FamilyBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JunctionOwnerBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Integration.Path.NoisyPathArea
public import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorSides
import Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryQueryBounds
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Polynomial.Dense.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RegularClosedBoundary
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Riemann.RootContinuation.NewtonRetainedExteriorSources
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-! A sufficient physical depth for the same retained exterior source bank. -/
namespace Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorSides (ComponentSourceArea ComponentPhysicalArea
  ComponentCountError ComponentTotalError RetainedExteriorSideEstimate RetainedExteriorPieceEstimate
  RetainedExteriorComponentEstimate)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece (junctionCount)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (maximum maximum_nonnegative
  le_maximum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation (occurrenceAt)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FamilyBounds (PreOwnerQueries)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest (OwnerRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (FragmentAreaBudget)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {first second : Fin genus}
  {target radius : Fraction.Rational} {floor : Nat}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- A retained depth after which the original component source area meets the requested squared-norm bound.

Every later refinement reuses the same original closed comparison; the certificate quantifies over the actual refined
preparation and retained source reading. -/
@[expose] def ComponentDepthPlan
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (PeriodMatrix.standardDifferential second) (requested / 4) minimum) :=
  { depth : Nat // ∀ later, depth ≤ later →
    Data.Gaussian.Norm.Basic.normSq (ComponentSourceArea (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth
      prepared
      later) componentIndex comparison) < requested }

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- The original squared dyadic mesh rate equals the corresponding quarter-radius sequence. -/
theorem physical_rate (count : Nat) (magnitude : Fraction.Rational) (depth : Nat) :
    (count : Fraction.Rational)^2 * (16 * magnitude^2 * ((1 / 2 : Fraction.Rational)^depth)^2) =
      Geometric.Basic.quarterRadius ((count : Fraction.Rational)^2 * (16 * magnitude^2)) depth := by
  rw [← pow_mul, Nat.mul_comm depth 2, pow_mul, show (1 / 2 : Fraction.Rational)^2 = 1 / 4 by decide,
    Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

open Purelib.Algebra in
open Purelib.Data.Rat in
/-- The quarter-target source budget and one-sixteenth mesh error fit strictly within the original positive request. -/
theorem pay {requested error : Fraction.Rational} (positive : 0 < requested) (small : error ≤ requested / 16) :
    2 * (requested / 4 + error + (requested / 4) / 128) < requested := by
  have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (le_refl (requested / 4)) small)
      (le_refl ((requested / 4) / 128))) (by decide : (0 : Fraction.Rational) ≤ 2)
  have coefficient : (2 : Fraction.Rational) * (1 / 4 + 1 / 16 + (1 / 4) / 128) < 1 := by decide +kernel
  have paid := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct coefficient positive
  have scalar : 2 * (requested / 4 + requested / 16 + (requested / 4) / 128) =
      (2 * (1 / 4 + 1 / 16 + (1 / 4) / 128)) * requested := by
    simp only [Field.ExplicitField.div_eq_mul_inv, -eq_self, -iff_self]
    ring1
  exact bounded.trans_lt (scalar.trans_lt (paid.trans_eq (one_mul _)))

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Find a finite depth that pays the original component source bound at every later refinement.

The quarter-radius search starts from the retained physical depth and preserves the original source magnitude, parent
count and closed comparison. -/
@[expose] def componentDepthPlan
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length)
    {requested : Fraction.Rational} {minimum : Nat}
    (comparison :
      (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
      (PeriodMatrix.standardDifferential second) (requested / 4) minimum)
    (positive : 0 < requested) : ComponentDepthPlan prepared componentIndex comparison := by
  let scale := (comparison.original.plans.length : Fraction.Rational)^2 * (16 * comparison.sourceMagnitude^2)
  have nonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  let depth := Geometric.Search.firstQuarterBelow scale prepared.paid.cut.exterior.prepared.energy.depth (requested /
    16)
  have accurate := Geometric.Search.firstQuarterBelow_accurate scale nonnegative
    prepared.paid.cut.exterior.prepared.energy.depth (requested / 16)
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel : (0 : Fraction.Rational) < 16))
  refine ⟨depth, fun later order => ?_⟩
  let refined := NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared later
  have decreasing := quarterRadius_antitone nonnegative (order.trans
    (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth_ge prepared later))
  have physical := (physical_rate comparison.original.plans.length comparison.sourceMagnitude
    refined.paid.cut.exterior.prepared.energy.depth).trans_le (decreasing.trans accurate.le)
  have bound := (NewtonRequestedExteriorSides.retained_exterior_component_source_bound refined componentIndex
    comparison).2
  exact bound.trans_lt (pay positive physical)

open Purelib.Data.Rat in
/-- The exact original component's closed comparison at one quarter of the local target and retained source floor. -/
@[expose] def SourceReferenceAt
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (localTarget : Fraction.Rational) (minimum : Nat) (componentIndex : Fin
      prepared.exterior.prepared.components.length) :=
  (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared.ClosedBoundaryComparison
    (PeriodMatrix.standardDifferential second) (localTarget / 4) minimum

open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Read the original component source areas after refining the retained preparation to the requested depth. -/
@[expose] def SourceAreasAtDepth
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {localTarget : Fraction.Rational} {minimum : Nat}
    (references : Vector.DependentVector (SourceReferenceAt prepared localTarget minimum)) (depth : Nat) : List
      Basic.Canonical :=
  let refined := NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared depth
  List.ofFn (fun i => ComponentSourceArea refined i (references.get i))

open Purelib.Curves.Hyperelliptic in
/-- The original component's paired source geometry for the second retained differential. -/
@[expose] def SourceGeometryAt
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (componentIndex : Fin prepared.exterior.prepared.components.length) :=
  Meshes.PuncturedGrid.Exterior.BoundaryQueryBounds.SurfacePreparation.SourceGeometry
    (prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt).prepared
    (PeriodMatrix.standardDifferential second)

open Purelib.Data in
open Purelib.Data.Rat in
/-- Each retained source reference uses the exact right-hand chart and slope of its cached geometry. -/
@[expose] def SourceReferenceGeometry
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (geometry : Vector.DependentVector (SourceGeometryAt prepared))
    {localTarget : Fraction.Rational} {minimum : Nat}
    (references : Vector.DependentVector (SourceReferenceAt prepared localTarget minimum)) : Prop :=
  ∀ i, (references.get i).original.right = (geometry.get i).right ∧
    (references.get i).original.slope = (geometry.get i).slope

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
/-- Dependent source-owner queries indexed by the original component's boundary occurrences. -/
@[expose] def ComponentQueriesAt
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (localTarget : Fraction.Rational) (componentIndex : Fin prepared.exterior.prepared.components.length) :=
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  Vector.DependentVector (fun outer : Fin component.prepared.occurrences.length =>
    Meshes.PuncturedGrid.Exterior.FamilyBounds.PreOwnerQueries
      (Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer)
      (PeriodMatrix.standardDifferential second) localTarget)

open Purelib.Data in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Original occurrence queries with separate retained source and face-stage maxima.

The dependent rows preserve component and occurrence indices, while the source floor and face index bound their
respective original query requirements. -/
structure SourceQueryRequests
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (localTarget : Fraction.Rational) (minimum : Nat) where
  /-- The dependent cached request rows at the original component and occurrence indices. -/ rows :
    Vector.DependentVector (ComponentQueriesAt prepared localTarget)
  /-- The retained source-reference floor covering the requested minimum and every source query. -/ sourceMinimum : Nat
  /-- The requested original minimum lies below the retained source-reference floor. -/ minimum_le : minimum ≤
    sourceMinimum
  /-- Every exact original occurrence query's source floor lies below the retained common floor. -/ source_le : ∀
    component outer, ((rows.get component).get outer).sourceMinimum ≤ sourceMinimum
  /-- The retained common face-reading stage for the original queries. -/ faceIndex : Nat
  /-- Every original occurrence query's face stage lies below the retained common stage. -/ face_le : ∀ component outer,
    ((rows.get component).get outer).faceIndex ≤ faceIndex

constructive_injectivity SourceQueryRequests

section
open Purelib.Curves.Hyperelliptic
open Purelib.Data
open Purelib.Data.Rat
/-- Acquire the original occurrence queries and retain their exact source-floor and face-index maxima. -/
@[expose] def sourceQueryRequests
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (localTarget : Fraction.Rational) (minimum : Nat) : SourceQueryRequests prepared localTarget minimum :=
  let rows : Vector.DependentVector (ComponentQueriesAt prepared localTarget) := Vector.DependentVector.ofFn (fun i =>
    let component := prepared.exterior.prepared.components[i.val]'i.isLt
    Vector.DependentVector.ofFn (fun outer => Meshes.PuncturedGrid.Exterior.FamilyBounds.PreOwnerQueries.build
      (Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer)
      (PeriodMatrix.standardDifferential second) localTarget))
  let sourceMinimum := max minimum (rows.maximum (fun _ row => row.maximum (fun _ query => query.sourceMinimum)))
  let faceIndex := rows.maximum (fun _ row => row.maximum (fun _ query => query.faceIndex))
  ⟨rows, sourceMinimum, Data.Nat.Order.le_max_left _ _, (fun component outer =>
    (((rows.get component).get_le_maximum (fun _ query => query.sourceMinimum) outer).trans
      (rows.get_le_maximum (fun _ row => row.maximum (fun _ query => query.sourceMinimum)) component)).trans
        (Data.Nat.Order.le_max_right _ _)),
    faceIndex, fun component outer =>
      ((rows.get component).get_le_maximum (fun _ query => query.faceIndex) outer).trans
        (rows.get_le_maximum (fun _ row => row.maximum (fun _ query => query.faceIndex)) component)⟩

/-- Original reference traces satisfy separate trace, density, total-error and area-error bounds at later face stages.

Every bound retains the exact occurrence, parent piece and reference owner; area payment also requires the supplied
unit-length and tolerance conditions. -/
@[expose] def SourceTraceBounds
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {localTarget : Fraction.Rational} {minimum : Nat}
    (references : Vector.DependentVector (SourceReferenceAt prepared localTarget minimum)) {density fragmentTarget :
      Fraction.Rational}
    (budget : Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget density fragmentTarget) (faceIndex :
      Nat) : Prop :=
  ∀ componentIndex : Fin prepared.exterior.prepared.components.length,
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    let comparison := references.get componentIndex
    ∀ outer : Fin component.prepared.occurrences.length,
      let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
        outer
      ∀ (i : Fin comparison.original.plans.length)
        (piece :
          SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison.Piece
          comparison occurrence i)
        (index : Nat), faceIndex ≤ index →
        comparison.traceError occurrence i piece index ≤ budget.tolerance ∧
        comparison.traceDensity occurrence i piece index ≤ density ∧
        (∀ length tolerance, comparison.ownedTotalError occurrence i piece index length tolerance ≤
          2 * (tolerance + budget.tolerance)) ∧
        ∀ length tolerance, (0 ≤ length ∧ length ≤ 1) → 0 ≤ tolerance → tolerance ≤ budget.tolerance →
          comparison.ownedAreaError occurrence i piece index length localTarget tolerance ≤ fragmentTarget

/-- Dependent paired-owner requests indexed by the original component's boundary occurrences. -/
@[expose] def ComponentOwnersAt
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (tolerance : Fraction.Rational) (componentIndex : Fin prepared.exterior.prepared.components.length) :=
  let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
  Vector.DependentVector (fun outer : Fin component.prepared.occurrences.length =>
    Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest
      (Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer)
      (PeriodMatrix.standardDifferential second) tolerance)

end

open Purelib.Data in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Original paired-owner request rows with a common retained reading stage. -/
structure SourceOwnerRequests
    (prepared : BoundaryPreparation preparation first second target radius floor) (tolerance : Fraction.Rational) where
  /-- The dependent cached request rows at the original component and occurrence indices. -/ rows :
    Vector.DependentVector (ComponentOwnersAt prepared tolerance)
  /-- The retained common stage covering the exact cached requests. -/ index : Nat
  /-- Every original paired-owner request is available at the retained common stage. -/ later : ∀ component outer,
    ((rows.get component).get outer).index ≤ index

constructive_injectivity SourceOwnerRequests

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
/-- Acquire the exact original paired-owner requests and retain their maximum reading stage. -/
@[expose] def sourceOwnerRequests
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (tolerance : Fraction.Rational) (positive : 0 < tolerance) : SourceOwnerRequests prepared tolerance :=
  let rows : Vector.DependentVector (ComponentOwnersAt prepared tolerance) := Vector.DependentVector.ofFn (fun i =>
    let component := prepared.exterior.prepared.components[i.val]'i.isLt
    Vector.DependentVector.ofFn (fun outer => Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest.build
      (Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences outer)
      (PeriodMatrix.standardDifferential second) tolerance positive))
  ⟨rows, rows.maximum (fun _ row => row.maximum (fun _ owner => owner.index)), fun component outer =>
    ((rows.get component).get_le_maximum (fun _ owner => owner.index) outer).trans
      (rows.get_le_maximum (fun _ row => row.maximum (fun _ owner => owner.index)) component)⟩

open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Paths in
/-- The length-error budget at the retained preparation's original physical dyadic count. -/
@[expose] def SourceReadingBudget
    (refined : BoundaryPreparation preparation first second target radius floor) (allowance : Fraction.Rational) :=
  NoisyPathArea.LengthErrorBudget
    (RectangularDyadicPairedTrace.dyadicCount refined.paid.cut.exterior.prepared.energy.depth) allowance

open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Transport a length-error budget across an exact count equality while retaining padding and tolerance. -/
@[expose] def reindexReadingBudget {count otherCount : Nat} {allowance : Fraction.Rational}
    (budget : NoisyPathArea.LengthErrorBudget count allowance) (equal : count = otherCount) :
    NoisyPathArea.LengthErrorBudget otherCount allowance :=
  { padding := budget.padding
    padding_positive := budget.padding_positive
    paid := equal ▸ budget.paid
    tolerance := budget.tolerance
    tolerance_positive := budget.tolerance_positive
    tolerance_eq := budget.tolerance_eq }

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Every original side satisfies its retained area and total estimate at all later reading stages. -/
@[expose] def SourceSideBounds
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {localTarget : Fraction.Rational} {minimum : Nat}
    (references : Vector.DependentVector (SourceReferenceAt prepared localTarget minimum))
    (depth : Nat) (tolerance : Fraction.Rational) (readingIndex : Nat) : Prop :=
  ∀ componentIndex : Fin prepared.exterior.prepared.components.length,
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ (outer : Fin component.prepared.occurrences.length) {index : Nat} (cache :
      Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index),
      readingIndex ≤ index → RetainedExteriorSideEstimate (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth
        prepared depth) componentIndex
        (references.get componentIndex) outer cache localTarget tolerance

open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Every original physical piece meets the separate retained area and total targets at later stages. -/
@[expose] def SourcePieceBounds
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {localTarget : Fraction.Rational} {minimum : Nat}
    (references : Vector.DependentVector (SourceReferenceAt prepared localTarget minimum))
    (depth : Nat) (tolerance areaTarget totalTarget : Fraction.Rational) (readingIndex : Nat) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length) (index : Nat), readingIndex ≤ index →
    RetainedExteriorPieceEstimate (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared depth)
      componentIndex (references.get componentIndex)
      index localTarget tolerance areaTarget totalTarget

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Every original component satisfies its retained physical-versus-source area estimate at later stages. -/
@[expose] def SourceComponentBounds
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {localTarget : Fraction.Rational} {minimum : Nat}
    (references : Vector.DependentVector (SourceReferenceAt prepared localTarget minimum))
    (depth : Nat) (tolerance : Fraction.Rational) (readingIndex : Nat) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length) {index : Nat}
    (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index), readingIndex ≤
      index →
      RetainedExteriorComponentEstimate (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared depth)
        componentIndex
        (references.get componentIndex) cache localTarget tolerance

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- The complete physical-area sum meets the count-weighted bound from the retained component-error maximum.

The same refined preparation and cache determine every physical component, while the original count-error list and local
target pay the finite-sum estimate. -/
@[expose] def SourcePhysicalBounds
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (localTarget sourceMagnitude : Fraction.Rational)
    (depth : Nat) (areaTarget totalTarget : Fraction.Rational) (readingIndex : Nat) : Prop :=
  ∀ {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index),
    readingIndex ≤ index →
    let refined := NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared depth
    let errors := List.ofFn (fun componentIndex => ComponentCountError prepared componentIndex
      sourceMagnitude areaTarget totalTarget)
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (List.ofFn (fun componentIndex => ComponentPhysicalArea refined componentIndex cache))) ≤
      (prepared.exterior.prepared.components.length : Fraction.Rational)^2 *
        (2 * (maximum id errors + localTarget))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Every original retained physical junction meets one quarter of the owner tolerance at later reading stages. -/
@[expose] def SourceJunctionBounds
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (depth : Nat) (tolerance : Fraction.Rational) (readingIndex : Nat) : Prop :=
  ∀ componentIndex : Fin prepared.exterior.prepared.components.length,
    let component := prepared.exterior.prepared.components[componentIndex.val]'componentIndex.isLt
    ∀ outer : Fin component.prepared.occurrences.length,
      let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
        outer
      let refined := NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared depth
      let position := occurrence.sideOccurrence.position
      let sheet := occurrence.sideOccurrence.sheet
      let side := occurrence.sideOccurrence.side
      let mesh := (refined.paid.cut.exterior.prepared.energy.entries.get sheet).meshes.entries.get position
      ∀ (junction : Fin (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junctionCount mesh
        side)) {index : Nat}
        (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index), readingIndex ≤
          index →
        let samples := ((refined.traces.samples cache first second).samples.get position).get sheet
        PrimitiveAreaBounds.PrimitivePoint.Bounded
          (Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece.junction samples side junction)
          (tolerance / 4)

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- A nonnegative weighted allowance is bounded by its original target. -/
private theorem allowance_le_target {target weight : Fraction.Rational} (nonnegative : 0 ≤ target) (weightNonnegative :
  0 ≤ weight) :
    Budget.Weighted.allowance target weight ≤ target := by
  apply (Fraction.Order.Field.div_le_iff_pos (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    weightNonnegative (by decide : (0 : Fraction.Rational) < 1))).mpr
  exact (le_add_of_nonneg_right (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative weightNonnegative)).trans_eq
    (by ring1)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- The retained fragment budget's tolerance is bounded by its nonnegative target. -/
theorem fragment_tolerance_le {density target : Fraction.Rational}
    (budget : Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget density target) (nonnegative : 0 ≤
      target) :
    budget.tolerance ≤ target := by
  have weight : 0 ≤ 320 * (4 * density + 3) + 80 * density := add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 320)
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) budget.density_nonnegative) (by decide)))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 80)
      budget.density_nonnegative)
  exact budget.tolerance_eq.trans_le (allowance_le_target nonnegative weight)

open Purelib.Data.Rat in
/-- One quarter of a positive rational request is strictly below that request. -/
theorem quarter_lt {requested : Fraction.Rational} (positive : 0 < requested) : requested / 4 < requested := by
  apply (Fraction.Order.Field.div_lt_iff_pos (by decide : (0 : Fraction.Rational) < 4)).mpr
  exact (show requested = 1 * requested by ring1).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct (by decide : (1 : Fraction.Rational) < 4)
      positive).trans_eq (by ring1))

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- The original per-term quarter-target allowance pays four times the squared finite count. -/
theorem count_payment {requested localTarget : Fraction.Rational} (positive : 0 < requested) (count : Nat)
    (localLe : localTarget ≤ Budget.Aggregate.perTerm (requested / 4) count) :
    4 * (count : Fraction.Rational)^2 * localTarget < requested := by
  have countNonnegative := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)
  have smaller := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct localLe countNonnegative) countNonnegative
  have paid := smaller.trans_lt (Budget.Aggregate.count_mul_perTerm_lt
    (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)) count)
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 4) paid
  have cancel : 4 * (requested / 4) = requested := by
    rw [mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  exact (show 4 * (count : Fraction.Rational)^2 * localTarget = 4 * ((count : Fraction.Rational) * ((count :
    Fraction.Rational) * localTarget)) by ring1).trans_lt
    (scaled.trans_eq cancel)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks in
open Purelib.Data.Rat in
/-- A nonnegative common bound controls the finite maximum, including the empty list. -/
theorem maximum_le {Item : Type} (value : Item → Fraction.Rational) (items : List Item)
    {bound : Fraction.Rational} (nonnegative : 0 ≤ bound) (bounded : ∀ item ∈ items, value item ≤ bound) :
    maximum value items ≤ bound := by
  induction items with
  | nil => exact nonnegative
  | cons first rest ih =>
      exact Fraction.Order.Basic.max_le (bounded first List.mem_cons_self) (ih (fun item member => bounded item
        (List.mem_cons_of_mem _ member)))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- The retained refined physical-area sum meets the original requested bound at every later reading stage. -/
@[expose] def RequestedPhysicalBound (prepared : BoundaryPreparation preparation first second target radius floor)
    (requested : Fraction.Rational) (depth readingIndex : Nat) : Prop :=
  ∀ {index : Nat} (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index),
    readingIndex ≤ index →
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (List.ofFn (fun componentIndex => ComponentPhysicalArea (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth
        prepared depth) componentIndex cache))) < requested

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- Each original component's retained total-comparison error is paid by the local target at later stages. -/
@[expose] def SourceTotalErrorsPaid
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {localTarget : Fraction.Rational} {minimum : Nat}
    (references : Vector.DependentVector (SourceReferenceAt prepared localTarget minimum))
    (depth : Nat) (tolerance : Fraction.Rational) (readingIndex : Nat) : Prop :=
  ∀ (componentIndex : Fin prepared.exterior.prepared.components.length) {index : Nat}
    (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics prepared.domains index), readingIndex ≤
      index →
      ComponentTotalError (NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared depth) componentIndex
        (references.get componentIndex)
        cache localTarget tolerance ≤ localTarget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
set_option genInjectivity false in
/-- Cached original source geometry, requests, references and depth refinement with separate paid comparison bounds.

The package retains exact cache equations and common stage bounds, preserving the same original owners across fragment,
junction, side, component, physical and total-error certificates. -/
structure ExteriorSourceRequest
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (requested : Fraction.Rational) (minimum : Nat) where
  /-- The cached per-component target for the original aggregate request. -/ localTarget : Fraction.Rational
  /-- The local target is the minimum of one and the exact quarter-target per-term allowance. -/ localTarget_eq :
    localTarget = min 1 (Budget.Aggregate.perTerm (requested / 4) prepared.exterior.prepared.components.length)
  /-- The exact cached source geometry for each original component. -/ geometry : Vector.DependentVector
    (SourceGeometryAt prepared)
  /-- The cached common source density. -/ density : Fraction.Rational
  /-- The density equals the finite maximum of the original component-geometry densities. -/ density_eq : density =
    maximum id
    (List.ofFn (fun i => (geometry.get i).density))
  /-- The cached count-error list at unit area target and total target four. -/ unitErrors : List Fraction.Rational
  /-- The unit-error cache equals the original component count-error readback. -/ unitErrors_eq : unitErrors = List.ofFn
    (fun i => ComponentCountError prepared i density 1 4)
  /-- The retained maximum unit count-error coefficient. -/ coefficient : Fraction.Rational
  /-- The coefficient equals the finite maximum of the exact unit-error cache. -/ coefficient_eq : coefficient = maximum
    id unitErrors
  /-- The retained weighted target for original physical fragments. -/ fragmentTarget : Fraction.Rational
  /-- The fragment target is the minimum of one and the exact coefficient-weighted local allowance. -/ fragmentTarget_eq
    : fragmentTarget = min 1 (Budget.Weighted.allowance localTarget coefficient)
  /-- The retained coefficient times the fragment target is paid by the original local target. -/ fragment_paid :
    coefficient * fragmentTarget ≤ localTarget
  /-- The exact density-dependent fragment-area budget. -/ fragmentBudget :
    Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget density fragmentTarget
  /-- The retained original source and face queries at the fragment tolerance. -/ queries : SourceQueryRequests prepared
    fragmentBudget.tolerance minimum
  /-- The dependent original source references at the retained query floor. -/ references : Vector.DependentVector
    (SourceReferenceAt prepared localTarget queries.sourceMinimum)
  /-- Each exact reference retains its original cached right chart and slope. -/ reference_geometry :
    SourceReferenceGeometry prepared geometry references
  /-- Each original reference's source magnitude is bounded by the retained density. -/ source_magnitude_le : ∀ i,
    (references.get i).sourceMagnitude ≤ density
  /-- The exact reference traces meet the retained fragment trace and density estimates. -/ trace_bound :
    SourceTraceBounds prepared references fragmentBudget queries.faceIndex
  /-- The retained common physical refinement depth. -/ depth : Nat
  /-- The cached original boundary preparation refined to the retained depth. -/ refined : BoundaryPreparation
    preparation first second target radius floor
  /-- The refined cache equals the exact depth refinement of the original preparation. -/ refined_eq : refined =
    NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared depth
  /-- The retained length-error budget at the refined physical dyadic count. -/ readingBudget : SourceReadingBudget
    refined localTarget
  /-- The retained owner tolerance lies below the original fragment tolerance. -/ owner_tolerance_le :
    readingBudget.tolerance ≤ fragmentBudget.tolerance
  /-- The dependent original paired-owner requests at the retained reading tolerance. -/ owners : SourceOwnerRequests
    prepared readingBudget.tolerance
  /-- The retained common stage covering the exact cached requests. -/ index : Nat
  /-- The exact refined preparation is available by the retained common reading stage. -/ refined_le : refined.index ≤
    index
  /-- The original face queries are available by the retained common reading stage. -/ queries_le : queries.faceIndex ≤
    index
  /-- The exact paired-owner requests are available by the retained common reading stage. -/ owners_le : owners.index ≤
    index
  /-- The original retained junctions satisfy their separate quarter-tolerance bounds. -/ junction_bound :
    SourceJunctionBounds prepared depth readingBudget.tolerance index
  /-- The original retained sides satisfy separate area and total estimates. -/ side_bound : SourceSideBounds prepared
    references depth readingBudget.tolerance index
  /-- The original retained pieces satisfy their paid area and total targets. -/ piece_bound : SourcePieceBounds
    prepared references depth readingBudget.tolerance fragmentTarget (4 * fragmentBudget.tolerance) index
  /-- The exact retained components satisfy physical-versus-source area estimates. -/ component_bound :
    SourceComponentBounds prepared references depth readingBudget.tolerance index
  /-- The complete original physical-area sum satisfies its count-weighted estimate. -/ physical_bound :
    SourcePhysicalBounds prepared localTarget density depth fragmentTarget (4 * fragmentBudget.tolerance) index
  /-- The retained physical-area sum meets the original requested strict bound. -/ physical_accurate :
    RequestedPhysicalBound prepared requested depth index
  /-- Every original component's retained total error is paid by the local target. -/ total_errors_paid :
    SourceTotalErrorsPaid prepared references depth readingBudget.tolerance index
  /-- The cached ordered original component source areas. -/ areas : List Basic.Canonical
  /-- The area cache equals the exact source-reference readback at the retained depth. -/ areas_eq : areas =
    SourceAreasAtDepth prepared references depth
  /-- The squared norm of the exact cached source-area sum meets the original request. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum areas) < requested

constructive_injectivity ExteriorSourceRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks in
open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- Acquire the original exterior source caches, refine their physical depth and retain all paid readback certificates.

The exact component geometry determines the density and weighted fragment allowance; retained source and owner requests
share one later reading index, and the same references supply both source and physical area bounds. -/
@[expose] def prepareExteriorSources
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (requested : Fraction.Rational) (positive : 0 < requested) (minimum : Nat) :
    ExteriorSourceRequest prepared requested minimum := by
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  let localTarget := min 1 (Budget.Aggregate.perTerm (requested / 4) prepared.exterior.prepared.components.length)
  have localPositive : 0 < localTarget := Fraction.Order.Basic.lt_min (by decide)
    (Budget.Aggregate.perTerm_positive quarterPositive prepared.exterior.prepared.components.length)
  let geometry : Vector.DependentVector (SourceGeometryAt prepared) := Vector.DependentVector.ofFn (fun i =>
    Meshes.PuncturedGrid.Exterior.BoundaryQueryBounds.SurfacePreparation.SourceGeometry.build
      (prepared.exterior.prepared.components[i.val]'i.isLt).prepared (PeriodMatrix.standardDifferential second))
  let density := maximum id (List.ofFn (fun i => (geometry.get i).density))
  have densityNonnegative : 0 ≤ density := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _
  let unitErrors := List.ofFn (fun i => ComponentCountError prepared i density 1 4)
  let coefficient := maximum id unitErrors
  have coefficientNonnegative : 0 ≤ coefficient :=
    Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _
  let fragmentTarget := min 1 (Budget.Weighted.allowance localTarget coefficient)
  have fragmentPositive : 0 < fragmentTarget := Fraction.Order.Basic.lt_min (by decide)
    (Budget.Weighted.allowance_positive localPositive coefficientNonnegative)
  have fragmentPaid : coefficient * fragmentTarget ≤ localTarget :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_right _ _)
      coefficientNonnegative).trans
      (Budget.Weighted.mul_allowance_le localPositive.le coefficientNonnegative)
  let fragmentBudget := Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget.build density
    fragmentTarget
    densityNonnegative fragmentPositive
  have toleranceSmall := fragment_tolerance_le fragmentBudget
    fragmentPositive.le
  let queries := sourceQueryRequests prepared
    fragmentBudget.tolerance minimum
  let references : Vector.DependentVector (SourceReferenceAt prepared localTarget queries.sourceMinimum) :=
    Vector.DependentVector.ofFn (fun i =>
      let component := prepared.exterior.prepared.components[i.val]'i.isLt
      component.prepared.closedBoundaryComparison (PeriodMatrix.standardDifferential second) (geometry.get i).right
        (localTarget / 4) (Fraction.Order.Field.div_pos_direct localPositive (by decide : (0 : Fraction.Rational) < 4))
          queries.sourceMinimum)
  have referenceGeometry : SourceReferenceGeometry prepared geometry references := by
    intro i
    have referenceEq : references.get i =
        (prepared.exterior.prepared.components[i.val]'i.isLt).prepared.closedBoundaryComparison
          (PeriodMatrix.standardDifferential second) (geometry.get i).right (localTarget / 4)
          (Fraction.Order.Field.div_pos_direct localPositive (by decide)) queries.sourceMinimum :=
      Vector.DependentVector.ofFn_get _ i
    constructor
    · exact (congrArg (fun comparison => comparison.original.right) referenceEq).trans
        ((prepared.exterior.prepared.components[i.val]'i.isLt).prepared.closedBoundaryComparison_right
          (PeriodMatrix.standardDifferential second) (geometry.get i).right (localTarget / 4)
          (Fraction.Order.Field.div_pos_direct localPositive (by decide)) queries.sourceMinimum)
    · exact (congrArg (fun comparison => comparison.original.slope) referenceEq).trans
        (((prepared.exterior.prepared.components[i.val]'i.isLt).prepared.closedBoundaryComparison_slope
        (PeriodMatrix.standardDifferential second) (geometry.get i).right (localTarget / 4)
        (Fraction.Order.Field.div_pos_direct localPositive (by decide)) queries.sourceMinimum).trans
        (geometry.get i).slope_eq.symm)
  have sourceMagnitudeBound (i : Fin prepared.exterior.prepared.components.length) : (references.get i).sourceMagnitude
    ≤ density := by
    have densityLe : (geometry.get i).density ≤ density :=
      Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum id (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨i, rfl⟩)
    exact ((NewtonRequestedExteriorSides.component_source_magnitude_le_slope prepared i (references.get i)).trans_eq
      (referenceGeometry i).2).trans
      ((geometry.get i).slope_le_density.trans densityLe)
  have traceBound : SourceTraceBounds prepared references fragmentBudget queries.faceIndex := by
    intro componentIndex component comparison outer occurrence i piece index later
    have trace := Meshes.PuncturedGrid.Exterior.BoundaryQueryBounds.ClosedBoundaryComparison.requested_trace_error
      comparison occurrence i piece ((queries.rows.get componentIndex).get outer) fragmentBudget.tolerance_positive
      (queries.source_le componentIndex outer) ((queries.face_le componentIndex outer).trans later)
    have densityLe : (geometry.get componentIndex).density ≤ density :=
      Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum id (Data.List.OfFn.Basic.mem_ofFn.mpr
        ⟨componentIndex, rfl⟩)
    have densityBound := ((geometry.get componentIndex).density_bound comparison (referenceGeometry componentIndex).2
      occurrence (List.getElem_mem outer.isLt) i piece index).trans densityLe
    refine ⟨trace, densityBound, ?_, ?_⟩
    · intro length tolerance
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct (le_refl tolerance) ((Fraction.Order.Basic.min_le_right _ _).trans
          trace))
        (by decide : (0 : Fraction.Rational) ≤ 2)
    · intro length tolerance lengthBound ownerNonnegative ownerBound
      exact Meshes.PuncturedGrid.Exterior.BoundaryQueryBounds.ClosedBoundaryComparison.ownedAreaError_paid comparison
        occurrence i piece index fragmentBudget densityBound trace
        ownerNonnegative ownerBound lengthBound ⟨localPositive.le, Fraction.Order.Basic.min_le_left _ _⟩
  let plans := Vector.DependentVector.ofFn (fun i =>
    componentDepthPlan prepared i (references.get i)
    localPositive)
  let depth := plans.maximum (fun _ plan => plan.val)
  let refined := NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared depth
  let reading := Approximation.Budget.RequestedLengthBudget.requested
    (RectangularDyadicPairedTrace.dyadicCount refined.paid.cut.exterior.prepared.energy.depth)
    localTarget fragmentBudget.tolerance localPositive fragmentBudget.tolerance_positive
  let readingBudget : SourceReadingBudget refined localTarget := reading.budget
  let owners := sourceOwnerRequests prepared
    readingBudget.tolerance readingBudget.tolerance_positive
  let index := max refined.index (max queries.faceIndex owners.index)
  have refinedLe : refined.index ≤ index := Data.Nat.Order.le_max_left _ _
  have queriesLe : queries.faceIndex ≤ index := (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)
  have ownersLe : owners.index ≤ index := (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)
  have pieceBound : SourcePieceBounds prepared references depth readingBudget.tolerance fragmentTarget (4 *
    fragmentBudget.tolerance) index := by
    intro componentIndex stage later
    apply NewtonRequestedExteriorSides.retained_exterior_piece_bound refined componentIndex (references.get
      componentIndex) stage localTarget readingBudget.tolerance
      fragmentTarget (4 * fragmentBudget.tolerance)
    intro outer occurrence i piece length lengthBound
    have scalar := traceBound componentIndex outer i piece stage (queriesLe.trans later)
    refine ⟨scalar.2.2.2 length readingBudget.tolerance lengthBound readingBudget.tolerance_positive.le
      reading.tolerance_le, ?_⟩
    have total := (scalar.2.2.1 length readingBudget.tolerance).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct reading.tolerance_le (le_refl fragmentBudget.tolerance)) (by
          decide))
    exact total.trans_eq (by ring1)
  have junctionBound : SourceJunctionBounds prepared depth readingBudget.tolerance index := by
    intro componentIndex component outer occurrence surface position sheet side mesh junction stage cache later samples
    exact Meshes.PuncturedGrid.Exterior.JunctionOwnerBounds.SurfaceOccurrence.retained_junction_bound occurrence
      ((surface.traces.get position).get sheet)
      (cache.normalize.get first) (cache.normalize.get second) samples side junction
      ((owners.rows.get componentIndex).get outer) (((owners.later componentIndex outer).trans ownersLe).trans later)
  have sideBound : SourceSideBounds prepared references depth readingBudget.tolerance index := by
    intro componentIndex component outer stage cache later
    let occurrence := Meshes.PuncturedGrid.Exterior.BoundaryAxisLocation.occurrenceAt component.prepared.occurrences
      outer
    have meshDepth := refined.paid.cut.exterior.prepared.energy.mesh_depth
      occurrence.sideOccurrence.sheet occurrence.sideOccurrence.position
    let budget := reindexReadingBudget readingBudget
      (congrArg RectangularDyadicPairedTrace.dyadicCount meshDepth.symm)
    exact NewtonRequestedExteriorSides.retained_exterior_side_bound refined componentIndex (references.get
      componentIndex) outer cache budget
      ((owners.rows.get componentIndex).get outer) (((owners.later componentIndex outer).trans ownersLe).trans later)
  let areas := List.ofFn (fun i => ComponentSourceArea refined i (references.get i))
  have componentBound : SourceComponentBounds prepared references depth readingBudget.tolerance index := by
    intro componentIndex stage cache later
    exact NewtonRequestedExteriorSides.retained_exterior_component_bound refined componentIndex (references.get
      componentIndex) cache
      (fun outer => sideBound componentIndex outer cache later)
  have each (i : Fin prepared.exterior.prepared.components.length) :
      Data.Gaussian.Norm.Basic.normSq (ComponentSourceArea refined i (references.get i)) ≤ localTarget := by
    have later := plans.get_le_maximum (fun _ plan => plan.val) i
    have paid := (plans.get i).property depth later
    exact paid.le
  have physicalBound : SourcePhysicalBounds prepared localTarget density depth fragmentTarget (4 *
    fragmentBudget.tolerance) index := by
    intro stage cache later surface errors
    let maximum := maximum id errors
    have physicalEach (i : Fin prepared.exterior.prepared.components.length) :
        Data.Gaussian.Norm.Basic.normSq (ComponentPhysicalArea refined i cache) ≤ 2 * (maximum + localTarget) := by
      have bound := NewtonRequestedExteriorSides.retained_exterior_component_physical_bound refined i (references.get i)
        cache
        (componentBound i cache later) (each i)
      have totalNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4)
        fragmentBudget.tolerance_positive.le
      have toleranceLe : readingBudget.tolerance ≤ 4 * fragmentBudget.tolerance :=
        reading.tolerance_le.trans ((le_add_of_nonneg_right
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 3)
            fragmentBudget.tolerance_positive.le)).trans_eq (by ring1))
      have paidError := NewtonRequestedExteriorSides.component_comparison_error_paid refined i (references.get i) cache
        fragmentPositive.le
        totalNonnegative toleranceLe (sourceMagnitudeBound i) (pieceBound i stage later)
      have countLe : ComponentCountError prepared i density fragmentTarget (4 * fragmentBudget.tolerance) ≤ maximum :=
        Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum id (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨i, rfl⟩)
      have errorLe := paidError.trans ((NewtonRequestedExteriorSides.component_count_error_atDepth prepared i density
        depth
        fragmentTarget (4 * fragmentBudget.tolerance)).trans_le countLe)
      exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct errorLe (le_refl localTarget)) (by decide))
    have aggregate := Norm.Sum.Bounds.normSq_sum_le
      (List.ofFn (fun i => ComponentPhysicalArea refined i cache)) (2 * (maximum + localTarget)) (by
        intro value member; obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member; exact physicalEach i)
    rw [Data.List.OfFn.Basic.length_ofFn] at aggregate
    change _ ≤ (prepared.exterior.prepared.components.length : Fraction.Rational) *
      ((prepared.exterior.prepared.components.length : Fraction.Rational) * (2 * (maximum + localTarget))) at aggregate
    exact aggregate.trans_eq (by ring1)
  have countErrorPaid (i : Fin prepared.exterior.prepared.components.length) :
      ComponentCountError prepared i density fragmentTarget (4 * fragmentBudget.tolerance) ≤ localTarget := by
    have scaled := NewtonRequestedExteriorSides.component_count_error_scale prepared i density fragmentTarget (4 *
      fragmentBudget.tolerance)
      densityNonnegative fragmentPositive.le (Fraction.Order.Basic.min_le_left _ _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4)
        fragmentBudget.tolerance_positive.le)
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct toleranceSmall (by
          decide : (0 : Fraction.Rational) ≤ 4))
    have unitLe : ComponentCountError prepared i density 1 4 ≤ coefficient :=
      Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum id (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨i, rfl⟩)
    exact scaled.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct unitLe fragmentPositive.le).trans
      ((mul_comm fragmentTarget coefficient).trans_le fragmentPaid))
  have totalErrorsPaid : SourceTotalErrorsPaid prepared references depth readingBudget.tolerance index := by
    intro i stage cache later
    have totalNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4)
      fragmentBudget.tolerance_positive.le
    have toleranceLe : readingBudget.tolerance ≤ 4 * fragmentBudget.tolerance :=
      reading.tolerance_le.trans ((le_add_of_nonneg_right
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 3)
          fragmentBudget.tolerance_positive.le)).trans_eq (by ring1))
    have bound := NewtonRequestedExteriorSides.component_total_error_paid refined i (references.get i) cache
      fragmentPositive.le
      totalNonnegative densityNonnegative toleranceLe
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct toleranceSmall (by
          decide : (0 : Fraction.Rational) ≤ 4))
      (sourceMagnitudeBound i) (pieceBound i stage later)
    exact bound.trans ((NewtonRequestedExteriorSides.component_count_error_atDepth prepared i density depth
      fragmentTarget
      (4 * fragmentBudget.tolerance)).trans_le (countErrorPaid i))
  have physicalAccurate : RequestedPhysicalBound prepared requested depth index := by
    intro stage cache later
    let errors := List.ofFn (fun i => ComponentCountError prepared i density fragmentTarget (4 *
      fragmentBudget.tolerance))
    have errorsPaid : maximum id errors ≤ localTarget :=
      maximum_le _ _ localPositive.le (by
        intro value member; obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member; exact countErrorPaid i)
    have bounded := (physicalBound cache later).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct errorsPaid (le_refl localTarget)) (by
              decide : (0 : Fraction.Rational) ≤ 2))
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    have paid := count_payment positive
      prepared.exterior.prepared.components.length (Fraction.Order.Basic.min_le_right _ _ : localTarget ≤ _)
    exact bounded.trans_lt ((show (prepared.exterior.prepared.components.length : Fraction.Rational)^2 * (2 *
      (localTarget + localTarget)) =
      4 * (prepared.exterior.prepared.components.length : Fraction.Rational)^2 * localTarget by ring1).trans_lt paid)
  have aggregate := Norm.Sum.Bounds.normSq_sum_le areas
    (Budget.Aggregate.perTerm (requested / 4) prepared.exterior.prepared.components.length) (by
    intro value member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    exact (each i).trans (Fraction.Order.Basic.min_le_right _ _))
  rw [Data.List.OfFn.Basic.length_ofFn] at aggregate
  exact ⟨localTarget, rfl, geometry, density, rfl, unitErrors, rfl, coefficient, rfl, fragmentTarget, rfl, fragmentPaid,
    fragmentBudget, queries, references, referenceGeometry, sourceMagnitudeBound, traceBound, depth, refined, rfl,
    readingBudget, reading.tolerance_le, owners, index, refinedLe, queriesLe, ownersLe, junctionBound, sideBound,
      pieceBound, componentBound,
    physicalBound, physicalAccurate, totalErrorsPaid, areas, rfl,
    (aggregate.trans_lt (Budget.Aggregate.count_mul_perTerm_lt quarterPositive _)).trans
      (quarter_lt positive)⟩

end Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth
