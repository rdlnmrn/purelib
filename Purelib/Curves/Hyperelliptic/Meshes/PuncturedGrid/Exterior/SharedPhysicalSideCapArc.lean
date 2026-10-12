module
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideOwnerRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideCapArc
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSideCapArc
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalReadingSample
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
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
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Topology.Polygon.Stokes

public section

/-! Compare the cached physical readings to cap arcs with automatically paid owner errors. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideOwnerRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseSideCapArc
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest (OwnerRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (AxisSourceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies.JoinedFragmentFamily (buildHorizontal
  buildVertical)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalOwnerRequest (PhysicalOwnerBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceRunRefinement (sourceRunDensity)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior (SourceRunRefinement)
open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples.SharedPhysicalHorizontalReadings
  (Data firstValue secondValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation (physicalArcError)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other : Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Coordinate} {minimum stage fine index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other
    target minimum}

variable {data : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index}
  {otherData : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other
  index}

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
variable {cuts : GridCuts ((domains.get occurrence.sideOccurrence.position).domain
  occurrence.sideOccurrence.sheet).geometry} {meshBox : Purelib.Geometry.Rational.Box}
  {mesh : ObservationMesh cuts meshBox} {depth : Nat}

namespace SharedPhysicalHorizontalReadings.Data
variable {firstRow secondRow : Fin mesh.partition.y.intervals.length}
  {height : Coordinate} {side : MatchedHorizontalSide mesh mesh firstRow secondRow height}
  {trace : side.Trace depth}
  {firstBank : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index
    domains} {secondBank : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index
    domains}

/-- The retained shared horizontal readings meet the requested oriented cap-arc comparison.

The selected original owner budget pays the physical error, while the supplied source refinement and cap allowance
retain their separate stage and width obligations. -/
theorem
  cap_accurate
    (readings : SharedPhysicalHorizontalReadings.Data trace firstBank secondBank) {requested : Coordinate} (positive : 0
      < requested)
    (ownerBudget : PhysicalOwnerRequest.PhysicalOwnerBudget plan mesh.boundaryColumns (requested / 8))
    (selected : ownerBudget.Owners (dyadicCount depth))
    (later : selected.index ≤ index) (prepared : ownerBudget.Prepared)
    {evaluated : PairedSourcePlan.ParentEvaluation prepared.plan sample otherSample fine} {forward : Bool}
    (sources : FragmentFamilies.AxisSourceBank evaluated mesh false forward)
    (sourceFirst : occurrence.start.im = height) (sourceLast : occurrence.finish.im = height)
    (axis : false = occurrence.sourceVertical) (direction : occurrence.sourceForward = forward)
    (start : meshBox.xLower = if forward then occurrence.start.re else occurrence.finish.re)
    (finish : meshBox.xUpper = if forward then occurrence.finish.re else occurrence.start.re)
    (capLater : prepared.plan.parents.index ≤ stage) {floor : Nat}
    (request : SourceRunRefinement prepared.plan.parents.plans.length
      (SourceRunRefinement.sourceRunDensity prepared.plan) (requested / 8) floor)
    (physicalRefined : (1 / 2 : Coordinate) ^ depth ≤ request.width)
    (sourceRefined : request.depth ≤ prepared.plan.parents.depth + fine)
    (capPaid : target ≤ requested / 4) :
    Data.Gaussian.Norm.Basic.normSq (PhysicalArcAggregation.physicalArcError occurrence sample otherSample
      (occurrence.piece.mesh.depth + (prepared.plan.parents.depth + fine)) readings.original.centeredArea) < requested
        := by
  have paid := JoinedFragmentFamily.buildHorizontal_error_requested
    (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Coordinate) < 8))
    ownerBudget selected later prepared trace sources sourceFirst sourceLast readings.first readings.second
    (SharedPhysicalHorizontalReadings.firstValue trace firstBank) (SharedPhysicalHorizontalReadings.secondValue trace
      secondBank) readings.first_eq readings.second_eq
  cases forward with
  | false =>
    simp only [PhysicalArcAggregation.physicalArcError, direction, if_neg (by decide : false ≠ true), -eq_self,
      -iff_self]
    exact JoinedFragmentFamily.buildHorizontal_reverse_conjugate_cap_arc
      trace sources sourceFirst sourceLast selected.piece.budget selected.junction.budget
      selected.owners (selected.owners_le.trans later) selected.junctionOwners (selected.junctionOwners_le.trans later)
      readings.first readings.second (SharedPhysicalHorizontalReadings.firstValue trace firstBank)
        (SharedPhysicalHorizontalReadings.secondValue trace secondBank)
      readings.first_eq readings.second_eq axis direction start finish readings.original
      capLater request physicalRefined sourceRefined paid.le capPaid
  | true =>
    simp only [PhysicalArcAggregation.physicalArcError, direction, -eq_self, -iff_self]
    exact JoinedFragmentFamily.buildHorizontal_conjugate_cap_arc
      trace sources sourceFirst sourceLast selected.piece.budget selected.junction.budget
      selected.owners (selected.owners_le.trans later) selected.junctionOwners (selected.junctionOwners_le.trans later)
      readings.first readings.second (SharedPhysicalHorizontalReadings.firstValue trace firstBank)
        (SharedPhysicalHorizontalReadings.secondValue trace secondBank)
      readings.first_eq readings.second_eq axis direction start finish readings.original
      capLater request physicalRefined sourceRefined paid.le capPaid

end SharedPhysicalHorizontalReadings.Data

namespace SharedPhysicalVerticalReadings.Data
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples.SharedPhysicalVerticalReadings
  (Data firstValue secondValue)
variable {firstColumn secondColumn : Fin mesh.partition.x.intervals.length}
  {horizontal : Coordinate} {side : MatchedVerticalSide mesh mesh firstColumn secondColumn horizontal}
  {trace : side.Trace depth}
  {firstBank : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index
    domains} {secondBank : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index
    domains}

/-- The retained shared vertical readings meet the requested oriented cap-arc comparison.

The selected original owner budget pays the physical error, while the supplied source refinement and cap allowance
retain their separate stage and width obligations. -/
theorem
  cap_accurate
    (readings : Data trace firstBank secondBank) {requested : Coordinate} (positive : 0 < requested)
    (ownerBudget : PhysicalOwnerRequest.PhysicalOwnerBudget plan mesh.boundaryRows (requested / 8))
    (selected : ownerBudget.Owners (dyadicCount depth))
    (later : selected.index ≤ index) (prepared : ownerBudget.Prepared)
    {evaluated : PairedSourcePlan.ParentEvaluation prepared.plan sample otherSample fine} {forward : Bool}
    (sources : FragmentFamilies.AxisSourceBank evaluated mesh true forward)
    (sourceFirst : occurrence.start.re = horizontal) (sourceLast : occurrence.finish.re = horizontal)
    (axis : true = occurrence.sourceVertical) (direction : occurrence.sourceForward = forward)
    (start : meshBox.yLower = if forward then occurrence.start.im else occurrence.finish.im)
    (finish : meshBox.yUpper = if forward then occurrence.finish.im else occurrence.start.im)
    (capLater : prepared.plan.parents.index ≤ stage) {floor : Nat}
    (request : SourceRunRefinement prepared.plan.parents.plans.length
      (SourceRunRefinement.sourceRunDensity prepared.plan) (requested / 8) floor)
    (physicalRefined : (1 / 2 : Coordinate) ^ depth ≤ request.width)
    (sourceRefined : request.depth ≤ prepared.plan.parents.depth + fine)
    (capPaid : target ≤ requested / 4) :
    Data.Gaussian.Norm.Basic.normSq (PhysicalArcAggregation.physicalArcError occurrence sample otherSample
      (occurrence.piece.mesh.depth + (prepared.plan.parents.depth + fine)) readings.original.centeredArea) < requested
        := by
  have paid := JoinedFragmentFamily.buildVertical_error_requested
    (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Coordinate) < 8))
    ownerBudget selected later prepared trace sources sourceFirst sourceLast readings.first readings.second
    (firstValue trace firstBank) (secondValue trace secondBank) readings.first_eq readings.second_eq
  cases forward with
  | false =>
    simp only [PhysicalArcAggregation.physicalArcError, direction, if_neg (by decide : false ≠ true), -eq_self,
      -iff_self]
    exact JoinedFragmentFamily.buildVertical_reverse_conjugate_cap_arc
      trace sources sourceFirst sourceLast selected.piece.budget selected.junction.budget
      selected.owners (selected.owners_le.trans later) selected.junctionOwners (selected.junctionOwners_le.trans later)
      readings.first readings.second (firstValue trace firstBank) (secondValue trace secondBank)
      readings.first_eq readings.second_eq axis direction start finish readings.original
      capLater request physicalRefined sourceRefined paid.le capPaid
  | true =>
    simp only [PhysicalArcAggregation.physicalArcError, direction, -eq_self, -iff_self]
    exact JoinedFragmentFamily.buildVertical_conjugate_cap_arc
      trace sources sourceFirst sourceLast selected.piece.budget selected.junction.budget
      selected.owners (selected.owners_le.trans later) selected.junctionOwners (selected.junctionOwners_le.trans later)
      readings.first readings.second (firstValue trace firstBank) (secondValue trace secondBank)
      readings.first_eq readings.second_eq axis direction start finish readings.original
      capLater request physicalRefined sourceRefined paid.le capPaid

end SharedPhysicalVerticalReadings.Data

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples
