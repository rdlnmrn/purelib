module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.Newton.ExteriorCapJoiningComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapTotalBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugatePhysicalExteriorProduct
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.ExteriorBoundary

public section

/-! The retained cap evaluations pay every period premise of the regular comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.RetainedCapJoiningComparison

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {firstIndex secondIndex : Fin genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- The lap and cap requests, at their common supplied readings, suffice.
Canonical component periods and the physical terminal product are bounded
internally from the retained cap integral allowance. -/
theorem retained_exterior_cap_joining_accurate
    {first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex)}
    {second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex)}
    {lapError : Fraction.Rational} (lap : Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest.ExteriorLapRequest
      first second lapError)
    {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential firstIndex) stage domains}
    {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential secondIndex) stage domains}
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (right
      : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (later : lap.index ≤ stage) (firstLater : first.index ≤ stage) (secondLater : second.index ≤ stage) (newSheet : Fin
      2)
    {capTarget : Fraction.Rational} {floor depth otherDepth readingIndex : Nat} {box : Rational.Box}
    {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap (Periods.PeriodMatrix.standardDifferential
      firstIndex) stage box}
    {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap (Periods.PeriodMatrix.standardDifferential
      secondIndex) stage box}
    {allocated : PuncturedGrid.Exterior.PairedCapRequest

        (PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
        regular domains (Periods.PeriodMatrix.standardDifferential firstIndex))

        (PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
        regular domains (Periods.PeriodMatrix.standardDifferential secondIndex)) capTarget floor}
    (evaluated : PuncturedGrid.Exterior.PairedCapRequest.Evaluation allocated
      sample otherSample leftBank rightBank depth otherDepth readingIndex)
    (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
      (PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
      regular domains (Periods.PeriodMatrix.standardDifferential firstIndex)))
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    Data.Gaussian.Norm.Basic.normSq (2 *
      ConjugatePhysicalRequest.exterior (paired := paired) newSheet
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) -
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea attached
        sample otherSample) <
        4 * (lapError + 16 * max
          (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired
            := paired) grid.shrunk.included first)
          (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired
            := paired) grid.shrunk.included second) * allocated.allowance +
          capTarget + 4 * allocated.allowance^2) := by
  have small :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapTotalBounds.PairedCapRequest.Evaluation.built_one_lap_small
    evaluated degree left right newSheet
  have comparison := grid.shrunk.included.exterior_comparison base.bank.frame grid.punctured.bank.frame
    current.edges current.vertices (fun point member =>
      (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt grid.punctured.bank.toBranchCellBank
        point member).toLoop)
  have firstRead := comparison.values (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh
    left.values)
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse current.mesh left.values) newSheet
  have secondRead := comparison.values (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
    current.mesh right.values)
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse current.mesh right.values) newSheet
  have terminal := Hyperelliptic.Meshes.PuncturedGrid.ConjugatePhysicalExteriorProduct.conjugate_product_bound
    (paired := paired) grid.shrunk.included
    first second newSheet left right firstLater secondLater
    ((congrArg Data.Gaussian.Norm.Basic.normSq firstRead).trans_le small.1.le) ((congrArg
      Data.Gaussian.Norm.Basic.normSq secondRead).trans_le small.2.le)
  have result := Hyperelliptic.Meshes.Newton.ExteriorCapJoiningComparison.exterior_cap_joining_accurate
    lap left right later newSheet terminal evaluated attached degree

      (PuncturedGrid.Exterior.BuiltCapTotalBounds.PairedCapRequest.Evaluation.built_component_totals_bounded
      evaluated degree left right)
  exact result.trans_eq (by ring1)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.RetainedCapJoiningComparison
