module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideCapArc
import Purelib.Riemann.Readings.RectangularObservationEndpoints
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.CenteredBilinearPath

public section

/-! Instantiate the physical cap comparison on the actual perimeter side of an occurrence. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterCapArc

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
open Purelib.Geometry.Rectangle
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest (PhysicalOwnerBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (AxisSourceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement (sourceRunDensity)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior (SourceRunRefinement)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation (physicalArcError)
open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterReadings
  (Entries original pieceCount)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
open
  PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  (sourceVertical sourceForward)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideGeometry (physicalBox fixedCoordinate
  physical_bounds fixed_coordinates)
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {differential other :
    Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine
    index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other
    target minimum}

variable {firstBank : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index
  domains} {secondBank : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index
  domains}

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
variable {cuts : Riemann.Paths.RectangularSegmentSplitting.GridCuts ((domains.get
  occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).geometry} {meshBox :
  Purelib.Geometry.Rational.Box}
  {mesh : Riemann.Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox} {depth : Nat}

namespace SharedPhysicalPerimeterReadings

/-- The retained shared perimeter readings satisfy the requested original side's oriented cap-arc bound.

The comparison uses the selected physical side and its exact box, piece count and depth, with original numerical owners
and separately paid owner, source-refinement and cap allowances. -/
theorem cap_accurate (traces : RectangularPerimeterTraces.PerimeterTraces mesh) {side : GridLiftedDualSteps.GridSide}
    (which : occurrence.sideOccurrence.side = side) (box_eq : meshBox = PhysicalSideGeometry.physicalBox occurrence)
    (readings : SharedPhysicalPerimeterReadings.Entries traces firstBank secondBank side) {requested :
      InverseRootPolynomial.Coordinate} (positive : 0 < requested)
    {pieces physicalDepth : Nat}
    (pieceCount_eq : pieces = SharedPhysicalPerimeterReadings.pieceCount mesh side) (physicalDepth_eq : physicalDepth =
      mesh.depth)
    (ownerBudget : PhysicalOwnerRequest.PhysicalOwnerBudget plan pieces (requested / 8))
    (selected : ownerBudget.Owners (RectangularDyadicPairedTrace.dyadicCount physicalDepth))
    (later : selected.index ≤ index) (prepared : ownerBudget.Prepared)
    {evaluated : PairedSourcePlan.ParentEvaluation prepared.plan sample otherSample fine}
    (sources : FragmentFamilies.AxisSourceBank evaluated mesh occurrence.sourceVertical occurrence.sourceForward)
    (capLater : prepared.plan.parents.index ≤ stage) {floor : Nat}
    (request : SourceRunRefinement prepared.plan.parents.plans.length
      (SourceRunRefinement.sourceRunDensity prepared.plan) (requested / 8) floor)
    (physicalRefined : (1 / 2 : InverseRootPolynomial.Coordinate) ^ physicalDepth ≤ request.width)
    (sourceRefined : request.depth ≤ prepared.plan.parents.depth + fine)
    (capPaid : target ≤ requested / 4) :
    Data.Gaussian.Norm.Basic.normSq (PhysicalArcAggregation.physicalArcError occurrence sample otherSample
      (occurrence.piece.mesh.depth + (prepared.plan.parents.depth + fine))
      (SharedPhysicalPerimeterReadings.original traces readings).centeredArea) < requested := by
  subst pieces physicalDepth
  cases side with
  | bottom =>
    have axis : false = occurrence.sourceVertical := by
      simp only [SurfaceOccurrence.sourceVertical, which, -eq_self, -iff_self]; rfl
    have bounds := PhysicalSideGeometry.physical_bounds occurrence
    simp only [← axis, ← box_eq, SourceIntervals.axisCoordinate, if_neg (by decide : false ≠ true), -eq_self, -iff_self]
      at bounds
    have fixed := PhysicalSideGeometry.fixed_coordinates occurrence
    simp only [SurfaceOccurrence.sourceVertical, which, PhysicalSideGeometry.fixedCoordinate, ← box_eq,
      SourceIntervals.axisCoordinate,
      Bool.not_false, -eq_self, -iff_self] at fixed
    exact SharedPhysicalHorizontalReadings.Data.cap_accurate readings positive ownerBudget selected later prepared
      (AxisSourceBank.castAxis axis.symm sources)
      (fixed.1.trans mesh.y_first.symm) (fixed.2.trans mesh.y_first.symm)
      axis rfl bounds.1 bounds.2 capLater request physicalRefined sourceRefined capPaid
  | top =>
    have axis : false = occurrence.sourceVertical := by
      simp only [SurfaceOccurrence.sourceVertical, which, -eq_self, -iff_self]; rfl
    have bounds := PhysicalSideGeometry.physical_bounds occurrence
    simp only [← axis, ← box_eq, SourceIntervals.axisCoordinate, if_neg (by decide : false ≠ true), -eq_self, -iff_self]
      at bounds
    have fixed := PhysicalSideGeometry.fixed_coordinates occurrence
    simp only [SurfaceOccurrence.sourceVertical, which, PhysicalSideGeometry.fixedCoordinate, ← box_eq,
      SourceIntervals.axisCoordinate,
      Bool.not_false, -eq_self, -iff_self] at fixed
    exact SharedPhysicalHorizontalReadings.Data.cap_accurate readings positive ownerBudget selected later prepared
      (AxisSourceBank.castAxis axis.symm sources)
      (fixed.1.trans mesh.y_last.symm) (fixed.2.trans mesh.y_last.symm)
      axis rfl bounds.1 bounds.2 capLater request physicalRefined sourceRefined capPaid
  | left =>
    have axis : true = occurrence.sourceVertical := by
      simp only [SurfaceOccurrence.sourceVertical, which, -eq_self, -iff_self]; rfl
    have bounds := PhysicalSideGeometry.physical_bounds occurrence
    simp only [← axis, ← box_eq, SourceIntervals.axisCoordinate, -eq_self, -iff_self] at bounds
    have fixed := PhysicalSideGeometry.fixed_coordinates occurrence
    simp only [SurfaceOccurrence.sourceVertical, which, PhysicalSideGeometry.fixedCoordinate, ← box_eq,
      SourceIntervals.axisCoordinate,
      Bool.not_true, if_neg (by decide : false ≠ true), -eq_self, -iff_self] at fixed
    exact SharedPhysicalVerticalReadings.Data.cap_accurate readings positive ownerBudget selected later prepared
      (AxisSourceBank.castAxis axis.symm sources)
      (fixed.1.trans mesh.x_first.symm) (fixed.2.trans mesh.x_first.symm)
      axis rfl bounds.1 bounds.2 capLater request physicalRefined sourceRefined capPaid
  | right =>
    have axis : true = occurrence.sourceVertical := by
      simp only [SurfaceOccurrence.sourceVertical, which, -eq_self, -iff_self]; rfl
    have bounds := PhysicalSideGeometry.physical_bounds occurrence
    simp only [← axis, ← box_eq, SourceIntervals.axisCoordinate, -eq_self, -iff_self] at bounds
    have fixed := PhysicalSideGeometry.fixed_coordinates occurrence
    simp only [SurfaceOccurrence.sourceVertical, which, PhysicalSideGeometry.fixedCoordinate, ← box_eq,
      SourceIntervals.axisCoordinate,
      Bool.not_true, if_neg (by decide : false ≠ true), -eq_self, -iff_self] at fixed
    exact SharedPhysicalVerticalReadings.Data.cap_accurate readings positive ownerBudget selected later prepared
      (AxisSourceBank.castAxis axis.symm sources)
      (fixed.1.trans mesh.x_last.symm) (fixed.2.trans mesh.x_last.symm)
      axis rfl bounds.1 bounds.2 capLater request physicalRefined sourceRefined capPaid

end SharedPhysicalPerimeterReadings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalPerimeterCapArc
