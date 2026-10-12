module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.LapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateExteriorLapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BuiltCapJoining
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! Compare the actual Newton exterior offset with the regular cap attachment. -/
section

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization

open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Rat.Fraction.Compatibility

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

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.ExteriorCapJoiningComparison

/-- Both comparisons read the same triangles and primitive samples. The lap,
terminal product, cap request and cross-component total errors all remain paid. -/
theorem exterior_cap_joining_accurate
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
    (later : lap.index ≤ stage) (newSheet : Fin 2) {terminalError : Fraction.Rational}
    (terminal : Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
      grid.shrunk.included current.edges current.vertices newSheet
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
        Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh
        left.values edge))
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)))
          ≤ terminalError)
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
    (degree : curve.polynomial.natDegree = 2 * genus + 2) {totalBound : Fraction.Rational}
    (bounded : ∀ word ∈ current.exteriorBoundaries,
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total (word.map (fun edge =>
        (⟨conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values edge),
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ :
            Topology.Polygon.Stokes.PrimitivePoint)))) totalBound) :
    Data.Gaussian.Norm.Basic.normSq (2 *
      ConjugatePhysicalRequest.exterior (paired := paired) newSheet
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) -
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea attached
        sample otherSample) <
        4 * (lapError + 4 * terminalError + capTarget + 4 * totalBound^2) := by
  let middle := Data.Gaussian.Norm.Sum.Basic.gaussianSum (current.exteriorBoundaries.map (fun word =>
    Path.PairedIncrementArea.area (word.map (fun edge =>
      (⟨conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values edge),
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ :
          Topology.Polygon.Stokes.PrimitivePoint)))))
  let source := 2 * ConjugatePhysicalRequest.exterior (paired :=
    paired) newSheet
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values)
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values)
  let finish := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea
    attached sample otherSample
  have firstBound : Data.Gaussian.Norm.Basic.normSq (source - middle) ≤ 2 * (lapError + 4 * terminalError) :=
    Hyperelliptic.Meshes.Newton.ConjugateExteriorLapRequest.ConjugatePhysicalRequest.exterior_component_bound lap left
      right later newSheet terminal
  have lastBound : Data.Gaussian.Norm.Basic.normSq (middle - finish) < 2 * (capTarget + 4 * totalBound^2) :=

      PuncturedGrid.Exterior.BuiltCapJoining.PairedCapRequest.Evaluation.conjugate_built_joining_accurate
      evaluated attached degree left right bounded
  have sumBound := (Fraction.Order.Arithmetic.add_le_add_direct firstBound (le_refl (Data.Gaussian.Norm.Basic.normSq
    (middle - finish)))).trans_lt
    (Fraction.Order.Arithmetic.add_lt_add_left_direct lastBound (2 * (lapError + 4 * terminalError)))
  have result := (Gaussian.Norm.Bounds.normSq_add_le_two (source - middle) (middle - finish)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2) sumBound)
  have cancel : source - finish = (source - middle) + (middle - finish) := by ring1
  exact ((congrArg Data.Gaussian.Norm.Basic.normSq cancel).trans_lt result).trans_eq (by ring1)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.ExteriorCapJoiningComparison

end
