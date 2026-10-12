module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.ParentBoundary
public import Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveSide
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveAreaReadback
import Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps

public section

/-! A requested paired primitive comparison on the original annular parent
cache. The result retains both full-path summaries, including endpoint
errors; transport to the shared grid primitive values remains explicit. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedPrimitiveRequest

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Periods
open Purelib.Riemann.RootContinuation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation (Comparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
    {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index} {lifted :
    Purelib.Riemann.Meshes.LiftedPuncturedGrid grid.punctured}

namespace Lifted.OuterPreparation.Comparison

variable {region : Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted} {prepared :
  Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region}
  {differential : Fin genus} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {tolerance : Purelib.Data.Rat.Fraction.Rational}

/-- Acquire both differential models on the exact parents already used by annular excision. Coverage, properness and
boundary geometry are automatic. -/
@[expose] def pairedPrimitiveRequest (comparison : OuterPreparation.Comparison prepared differential domains tolerance)
    (other : Fin genus) (areaTarget : Fraction.Rational) (positive : 0 < areaTarget) :
    RequestedNewtonPrimitiveSide.FullAreaRequest
      (OuterPreparation.band prepared differential) (PeriodMatrix.standardDifferential other) genus
      comparison.parents.parents areaTarget :=
  RequestedNewtonPrimitiveSide.fullAcquire
    (OuterPreparation.band prepared differential) (PeriodMatrix.standardDifferential other)
    ((preparation.profiles.get index).differentials.profiles.get other)
    comparison.parents.covered (fun _ member => comparison.parents_onBoundary member)
    comparison.parents.proper (grid.bands.box index).diagonalSq
    (grid.bands.box index).diagonalSq_nonneg
    (fun _ member => (comparison.parents_onBoundary member).movement_le)
    areaTarget positive

/-- The density charge uses only the original retained parent count and the selected band. Refining the children does
not change this bound. -/
@[expose] def pairedDensityCharge (comparison : OuterPreparation.Comparison prepared differential domains tolerance)
    (other : Fin genus) : Fraction.Rational :=
  let band := OuterPreparation.band prepared differential
  let otherProfile := ((preparation.profiles.get index).differentials.profiles.get other)
  let magnitude := (PreparedNewtonBandSamples.Sample.preparedDensity band.sample ((preparation.profiles.get
    index).differentials.profiles.get differential) band.error +
    PreparedNewtonBandSamples.Sample.preparedDensity band.sample otherProfile band.error) * (grid.bands.box
      index).diagonalSq
  let n : Fraction.Rational := comparison.parents.parents.length
  2 * (n^2 * (4 * magnitude^2) + 4 * (n^2 * magnitude)^2)

/-- Control the full numerical path, including the polygon joining parent endpoints. The bank may retain a different
child depth for every parent. -/
theorem paired_numerical_area_bound
    (comparison : OuterPreparation.Comparison prepared differential domains tolerance) (other : Fin genus)
    {areaTarget : Fraction.Rational}
    (sample : RequestedNewtonPrimitiveSide.FullAreaRequest
      (OuterPreparation.band prepared differential) (PeriodMatrix.standardDifferential other) genus
      comparison.parents.parents areaTarget) :
    Data.Gaussian.Norm.Basic.normSq sample.2.2.1.areaValue ≤

        pairedDensityCharge
        comparison other := by
  let band := OuterPreparation.band prepared differential
  let otherProfile := ((preparation.profiles.get index).differentials.profiles.get other)
  have movements := fun parent member =>
    (comparison.parents_onBoundary (parent := parent) member).movement_le
  have bounds := sample.2.1.bank.block_bounds otherProfile movements
  have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (add_nonneg (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative band.sample ((preparation.profiles.get
      index).differentials.profiles.get differential) band.errorPositive.le)
      (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative band.sample otherProfile band.errorPositive.le))
    (grid.bands.box index).diagonalSq_nonneg
  have estimate := PairedAreaBlocks.blocks_area_bound sample.2.1.bank.incrementBlocks
    nonnegative (fun block member => (bounds block member).1)
    (fun block member => (bounds block member).2)
  rw [sample.2.1.bank.incrementBlocks_length] at estimate
  rw [sample.2.2.1.area_eq]
  exact estimate

/-- Transfer the numerical density estimate to the actual requested primitive path on these same parents, paying the
complete area discrepancy. -/
theorem paired_primitive_area_bound
    (comparison : OuterPreparation.Comparison prepared differential domains tolerance) (other : Fin genus)
    {areaTarget : Fraction.Rational}
    (sample : RequestedNewtonPrimitiveSide.FullAreaRequest
      (OuterPreparation.band prepared differential) (PeriodMatrix.standardDifferential other) genus
      comparison.parents.parents areaTarget) :
    Data.Gaussian.Norm.Basic.normSq sample.2.2.2.val.areaValue ≤
      2 * (areaTarget +
        pairedDensityCharge
        comparison other) := by
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two
    (sample.2.2.2.val.areaValue - sample.2.2.1.areaValue) sample.2.2.1.areaValue).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct sample.2.2.2.property.1

          (paired_numerical_area_bound
          comparison other sample)) (by decide))
  rw [sub_add_cancel] at estimate
  exact estimate

end Lifted.OuterPreparation.Comparison
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedPrimitiveRequest
