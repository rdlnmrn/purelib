module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.LinearAlgebra.Gaussian.Energy

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Riemann.RootContinuation.NewtonCanonicalMatrixRequest
public import Purelib.Riemann.Periods.PeriodSampleBounds
public import Purelib.Riemann.Readings.RawEnergyPerturbation
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Field
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.NewtonCombinedPeriodArea
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.NewtonPeriodGeometry
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic

public section

/-! A computed common tail transports raw energy from one retained Newton
geometry to the original corrected A/B sampler, paying a homogeneous loss. -/
namespace Purelib.Riemann.RootContinuation.NewtonOriginalEnergyComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.Periods.NewtonPeriodGeometry (PeriodGeometry)
open Purelib.Riemann.Periods.NewtonCanonicalPeriodReadback (canonicalPeriodSheet)
open Purelib.Riemann.Periods.NewtonCombinedPeriodArea (resplitPeriodMatrix)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Periods.PeriodMatrix (sampledMatrix)
open _root_.Purelib.Riemann.Periods (PeriodSampleBounds)
open Purelib.Riemann.Readings.RawEnergyPerturbation (rawEnergyMatrixTarget rawEnergyMatrixTarget_positive
  raw_energy_sub_selected_allowance_le)
open Purelib.LinearAlgebra.Gaussian.Energy (unnormalizedEnergyForm)
open Purelib.Riemann.RootContinuation.NewtonCanonicalMatrixRequest (CanonicalMatrixRequest)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Paid comparison between refined canonical and original sampled period energy.

Retains the positive allowance, original period magnitude bounds, exact matrix target and the actual canonical matrix
request at that target. -/
structure OriginalEnergyComparison (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (geometry : PeriodGeometry base.bank.toBranchCellBank) (allowance : Fraction.Rational) (minimum : Nat) where
  /-- Strict positivity of the energy allowance. -/ positive : 0 < allowance
  /-- Retained magnitude bounds for the original sampled periods. -/ bounds : PeriodSampleBounds prepared.periodData
  /-- Cached entrywise matrix perturbation target. -/ target : Fraction.Rational
  /-- The target is exactly the one allocated from genus, magnitude and allowance. -/ target_eq : target =
    rawEnergyMatrixTarget genus bounds.magnitude allowance
  /-- Actual canonical matrix request at the retained target. -/ request : CanonicalMatrixRequest prepared geometry
    target minimum

constructive_injectivity OriginalEnergyComparison

namespace OriginalEnergyComparison

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Construct the original energy comparison from a positive allowance.

Computes period magnitude bounds, allocates the corresponding matrix perturbation target and retains the canonical
request using that exact value. -/
@[expose] def build (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (geometry : PeriodGeometry base.bank.toBranchCellBank)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (minimum : Nat) :
    OriginalEnergyComparison prepared geometry allowance minimum :=
  let bounds := PeriodSampleBounds.build prepared.periodData
  let target := rawEnergyMatrixTarget genus bounds.magnitude allowance
  let request := CanonicalMatrixRequest.build prepared geometry target
    (rawEnergyMatrixTarget_positive genus bounds.magnitude_nonnegative positive) minimum
  ⟨positive, bounds, target, rfl, request⟩

variable {prepared : Prepared paired}
  {geometry : PeriodGeometry base.bank.toBranchCellBank} {allowance : Rational} {minimum :
    Nat}

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Gaussian in
/-- Transfer refined canonical energy to the original sampled period matrices.

After the retained request index, applies the entrywise A/B comparison and original magnitude bounds, subtracting the
allowance times the coefficient squared-norm sum. -/
theorem energy_lower (comparison : OriginalEnergyComparison prepared geometry allowance minimum)
    (stage : Nat) (cache : Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics geometry.domains stage)
    (triangles : Vector.DependentVector (fun basis : Fin genus =>
      Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get basis) geometry.lifted.mesh))
    (later : comparison.request.index ≤ stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    let values := fun basis => Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation geometry.lifted.mesh
      (triangles.get basis).values
    let incoming := canonicalPeriodSheet (lifted := lifted) (sheet := sheet) geometry
    let aMatrix := resplitPeriodMatrix prepared geometry.grid.shrunk.included geometry.lifted.edges
      geometry.lifted.vertices incoming values false
    let bMatrix := resplitPeriodMatrix prepared geometry.grid.shrunk.included geometry.lifted.edges
      geometry.lifted.vertices incoming values true
    Energy.unnormalizedEnergyForm coefficients aMatrix bMatrix - allowance * FiniteSum.Fin.sumFin (fun basis =>
      Data.Gaussian.Norm.Basic.normSq (coefficients basis)) ≤
      Energy.unnormalizedEnergyForm coefficients
        (sampledMatrix prepared.periodData.aMatrix stage) (sampledMatrix prepared.periodData.bMatrix stage) := by
  intro values incoming aMatrix bMatrix
  apply raw_energy_sub_selected_allowance_le coefficients
    (sampledMatrix prepared.periodData.aMatrix stage) (sampledMatrix prepared.periodData.bMatrix stage)
    aMatrix bMatrix comparison.bounds.magnitude_nonnegative comparison.positive
    (comparison.bounds.a_bounded stage) (comparison.bounds.b_bounded stage)
  · intro row cycle
    exact (comparison.request.a_accurate stage cache triangles later row cycle).trans_eq comparison.target_eq
  · intro row cycle
    exact (comparison.request.b_accurate stage cache triangles later row cycle).trans_eq comparison.target_eq

end OriginalEnergyComparison
end Purelib.Riemann.RootContinuation.NewtonOriginalEnergyComparison
