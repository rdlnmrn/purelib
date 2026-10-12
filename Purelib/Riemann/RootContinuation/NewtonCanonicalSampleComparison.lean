module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Riemann.Periods.NewtonRequestedPairedPeriods
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Riemann.Periods.NewtonCanonicalPeriodData
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Periods.NewtonPairedPeriodFragments
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Vector.Basic
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.NewtonPeriodGeometry
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Integration.Program.Gaussian.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Compare canonical resplit words with the displayed original matrix samples,
retaining both the word-to-model and witness-to-model errors. -/
namespace Purelib.Riemann.RootContinuation.NewtonCanonicalSampleComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered
  anchor)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Periods.NewtonPeriodGeometry (PeriodGeometry)
open Purelib.Riemann.Periods.NewtonCanonicalPeriodData (ACanonicalPreparation BCanonicalPreparation)
open Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback (canonicalPeriodSheet)
open Purelib.Riemann.Periods.PeriodMatrix (sampledMatrix sampledMatrix_aProgram_close sampledMatrix_bProgram_close)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}
  {geometry : PeriodGeometry base.bank.toBranchCellBank}
  {differential cycle : Fin genus} {target : Rational} {minimum : Nat}

open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Riemann.Periods
open Purelib.Topology.Surface
/-- Compare the canonical A-cycle edge word with its sampled period.

After the retained numerical and fragment thresholds, combines the canonical word estimate with the period-program
sample estimate, preserving the original lifted anchor and the factor-two squared-norm bound. -/
theorem ACanonicalPreparation.sample_accurate
    (data : ACanonicalPreparation prepared geometry differential cycle target minimum)
    (positive : 0 < target) (numericalIndex : Nat)
    (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics geometry.domains numericalIndex)
    (triangles : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get differential)
      geometry.lifted.mesh)
    (later : data.numericalIndex ≤ numericalIndex) (stage : Nat)
    (after : data.request.fragments.stage ≤ stage) :
    let word := Sewing.SewingRetraction.wordValue
      (Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation geometry.lifted.mesh triangles.values)
      (geometry.lifted.edges.indexedEdges geometry.lifted.vertices
        (geometry.grid.shrunk.included.resplit (prepared.aWalk cycle).closed.walk
          (lifted.vertices.coordinate_onGrid
            (Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)))
        (canonicalPeriodSheet (lifted := lifted) (sheet := sheet) geometry))
    Data.Gaussian.Norm.Basic.normSq (word - sampledMatrix prepared.periodData.aMatrix stage differential cycle) ≤
      2 * (target + Geometric.Basic.quarterRadius
        (max (prepared.periodData.aProgram differential cycle).integral.errorScale 1) stage) := by
  intro word
  let model := ((prepared.periodData.aProgram differential cycle).integral.model stage).integralSample
  let sample := sampledMatrix prepared.periodData.aMatrix stage differential cycle
  have canonical := NewtonCanonicalPeriodReadback.ACanonicalPreparation.word_accurate data positive numericalIndex cache
    triangles later stage after
  have witness := sampledMatrix_aProgram_close prepared.periodData differential cycle stage
  calc
    Data.Gaussian.Norm.Basic.normSq (word - sample) = Data.Gaussian.Norm.Basic.normSq ((word - model) - (sample -
      model)) :=
      congrArg Data.Gaussian.Norm.Basic.normSq (by ring1)
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (word - model) + Data.Gaussian.Norm.Basic.normSq (sample - model)) :=
      Norm.Bounds.normSq_sub_le_two _ _
    _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct canonical.le witness) (by decide)

/-- Compare the canonical B-cycle edge word with its sampled period.

After the retained numerical and fragment thresholds, combines the canonical word estimate with the period-program
sample estimate, preserving the original lifted anchor and the factor-two squared-norm bound. -/
theorem BCanonicalPreparation.sample_accurate
    (data : BCanonicalPreparation prepared geometry differential cycle target minimum)
    (positive : 0 < target) (numericalIndex : Nat)
    (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics geometry.domains numericalIndex)
    (triangles : Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get differential)
      geometry.lifted.mesh)
    (later : data.numericalIndex ≤ numericalIndex) (stage : Nat)
    (after : data.request.fragments.stage ≤ stage) :
    let word := Sewing.SewingRetraction.wordValue
      (Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation geometry.lifted.mesh triangles.values)
      (geometry.lifted.edges.indexedEdges geometry.lifted.vertices
        (geometry.grid.shrunk.included.resplit (prepared.bWalk cycle).closed.walk
          (lifted.vertices.coordinate_onGrid
            (Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)))
        (canonicalPeriodSheet (lifted := lifted) (sheet := sheet) geometry))
    Data.Gaussian.Norm.Basic.normSq (word - sampledMatrix prepared.periodData.bMatrix stage differential cycle) ≤
      2 * (target + Geometric.Basic.quarterRadius
        (max (prepared.periodData.bProgram differential cycle).integral.errorScale 1) stage) := by
  intro word
  let model := ((prepared.periodData.bProgram differential cycle).integral.model stage).integralSample
  let sample := sampledMatrix prepared.periodData.bMatrix stage differential cycle
  have canonical := NewtonCanonicalPeriodReadback.BCanonicalPreparation.word_accurate data positive numericalIndex cache
    triangles later stage after
  have witness := sampledMatrix_bProgram_close prepared.periodData differential cycle stage
  calc
    Data.Gaussian.Norm.Basic.normSq (word - sample) = Data.Gaussian.Norm.Basic.normSq ((word - model) - (sample -
      model)) :=
      congrArg Data.Gaussian.Norm.Basic.normSq (by ring1)
    _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (word - model) + Data.Gaussian.Norm.Basic.normSq (sample - model)) :=
      Norm.Bounds.normSq_sub_le_two _ _
    _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct canonical.le witness) (by decide)

end Purelib.Riemann.RootContinuation.NewtonCanonicalSampleComparison
