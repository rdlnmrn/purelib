module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedExteriorPathGeometry
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSourceReferences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
public import Purelib.Riemann.Integration.PreparedParentCacheRecasting
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Topology.Polygon.Stokes

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Integration

open Purelib.Riemann

public section

/-! Parity-independent source data consumed by the exterior comparisons. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} (prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program)

/-- Recover the original program's parent covers from its retained surface occurrences. -/
@[expose] def
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.sourceCovers
  : UniformReciprocalCover.ParentCovers program.cache.parents :=
  prepared.parents_eq ▸
    (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.capSpine
    prepared.occurrences).covers

/-- Recast the same original parent cache to the second differential and construct its boundary covers. -/
@[expose] def
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.otherSourceCovers
  (_prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
  regular domains program) (other : Differentials.Basic.Differential genus) :
  UniformReciprocalCover.ParentCovers
    (program.cache.parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge other)) :=
  let otherCache := Integration.PreparedParentCacheRecasting.recast program.cache other
  UniformReciprocalCover.ParentCovers.build otherCache.parents otherCache.covered
    (Paths.PreparedExteriorPathGeometry.ParentCache.onBoundary otherCache
      (by
        rw [program.walk_eq]; exact PeriodPrograms.exteriorWalk_sides base))

variable {other : Differentials.Basic.Differential genus} {requested :
  InverseRootPolynomial.Coordinate} {minimum : Nat}

set_option genInjectivity false in
/-- The two original source primitives and controlled references at one paired parent index.

Both polynomial identities, the finite reference depth and its paid dyadic error are retained together. -/
structure SourceComparison.SourceReferenceEntry
    (original : Disk.PairedParentRequest.Request regular other program.cache.parents
      (requested / 128) minimum)
    (i : Fin original.plans.length) where
  /-- The shared original source-model stage. -/ index : Nat
  /-- The retained first source primitive at that stage. -/ source :
    UniformReciprocalPrimitives.SourcePrimitive
    (Disk.PairedParentCharts.ChartParent original i).data index
  /-- The retained second source primitive at the same stage. -/ otherSource :
    UniformReciprocalPrimitives.SourcePrimitive
    (Disk.PairedParentCharts.ChartParent original i).otherData index
  /-- The first controlled request on the original parent. -/ first :
    Disk.PairedParentRequest.Request.SourceRequest
    (Disk.PairedParentCharts.ChartParent original i).parent original.allowance minimum
  /-- The second controlled request on the same parent with its differential recast. -/ second :
    Disk.PairedParentRequest.Request.SourceRequest
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other
      (Disk.PairedParentCharts.ChartParent original i).parent) original.allowance
        minimum
  /-- The first controlled request retains exactly the first source polynomial. -/ first_eq :
    first.localRequest.request.model.primitive.value = source.primitive.value
  /-- The second controlled request retains exactly the second source polynomial. -/ second_eq :
    second.localRequest.request.model.primitive.value = otherSource.primitive.value
  /-- The retained dyadic source-reference depth. -/ depth : Nat
  /-- The retained upper bound for the dyadic reference error. -/ referenceError :
    InverseRootPolynomial.Coordinate
  /-- The paired source-slope scale at the retained depth is bounded by the reference error. -/ reference_rate : 16 *
    (max (Disk.PairedParentCharts.ChartParent original i).data.sourceSlope
    (Disk.PairedParentCharts.ChartParent original i).otherData.sourceSlope)^2 *
      ((1 / 2 : InverseRootPolynomial.Coordinate)^depth)^2 ≤ referenceError

constructive_injectivity SourceComparison.SourceReferenceEntry

/-- The dependent bank of source-reference data for every original paired parent index. -/
@[expose] def SourceComparison.SourceReferenceEntries
    (original : Disk.PairedParentRequest.Request regular other program.cache.parents
      (requested / 128) minimum) :=
  Vector.DependentVector (SourceComparison.SourceReferenceEntry
    original)

/-- Read the retained dyadic source-reference paths in their original paired parent order. -/
@[expose] def SourceComparison.sourceReferencePaths
    {original : Disk.PairedParentRequest.Request regular other program.cache.parents
      (requested / 128) minimum}
    (entries : SourceComparison.SourceReferenceEntries original) :=
  List.ofFn (fun i : Fin original.plans.length => Path.Dyadic.DyadicPairedPrimitivePaths.increments
    (Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues (entries.get i).source
      (entries.get i).otherSource)
    (entries.get i).depth 0 1)

set_option genInjectivity false in
/-- A closed source comparison retains the actual primitive owners and
reference depths, independently of the chart certificate used to bound it. -/
structure
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
  (other : Differentials.Basic.Differential genus) (requested :
  InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The original paired request on the complete program parent cache. -/ original :
    Disk.PairedParentRequest.Request regular other program.cache.parents (requested /
    128) minimum
  /-- The original first covers are exactly the surface preparation's retained source covers. -/ original_left :
    original.left = prepared.sourceCovers
  /-- The dependent source-reference bank on these exact original parent plans. -/ entries :
    SourceComparison.SourceReferenceEntries original
  /-- The common allowance for all retained dyadic reference errors. -/ referenceAllowance :
    InverseRootPolynomial.Coordinate
  /-- The common reference allowance is strictly positive. -/ reference_positive : 0 < referenceAllowance
  /-- Every original parent's retained reference error meets the common allowance. -/ reference_le : ∀ i, (entries.get
    i).referenceError ≤ referenceAllowance
  /-- The complete parent-count scaling of the reference allowance is paid by the allocated target fraction. -/
    reference_paid : (original.plans.length : InverseRootPolynomial.Coordinate) * ((original.plans.length
    : InverseRootPolynomial.Coordinate) * referenceAllowance) < requested / 128
  /-- The cached total and area of the complete retained source-reference path. -/ path :
    Path.PairedIncrementArea.Summary (SourceComparison.sourceReferencePaths
    entries).flatten
  /-- The cached source-path area meets the requested tolerance. -/ source_bounded : Gaussian.Norm.Basic.normSq
    path.areaValue < requested
  /-- Both cached source-path totals meet the requested component bound. -/ source_total_bounded :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded path.totalValue requested

constructive_injectivity
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison

/-- Read the source-reference increment paths already retained by this closed comparison. -/
@[expose] def
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison.sourcePaths
  (comparison : prepared.ClosedBoundaryComparison other requested minimum) :=
  SourceComparison.sourceReferencePaths comparison.entries

/-- The actual flattened retained source-reference path meets the requested area bound. -/
theorem
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison.path_bounded
  (comparison : prepared.ClosedBoundaryComparison other requested minimum) :
    Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area comparison.sourcePaths.flatten) < requested :=
  comparison.path.area_eq ▸ comparison.source_bounded

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
