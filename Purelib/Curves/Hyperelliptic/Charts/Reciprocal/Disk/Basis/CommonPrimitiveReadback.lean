module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveRequest
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Periods.PeriodMatrix

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! The retained source path is exactly the original parent primitive path
at the summed dyadic depth, including every intermediate excursion. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition (CommonPrimitivePlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans (Blocks)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin_zero sumFin_mul_right)

open Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples (DyadicSample)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements_sub_constant pathArea_dyadicIncrements)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {target :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements dyadicEdges_flatten_increments)

namespace BasisSourceLocations.PrimitiveBank

/-- The coefficient-weighted value of the retained original primitive bank at the supplied parent-edge parameter. -/
@[expose] def value (bank : BasisSourceLocations.PrimitiveBank covers index) (coefficients :
    LinearAlgebra.Gaussian.Energy.GaussianVector
  genus)
    (parameter : InverseRootPolynomial.Coordinate) : Gaussian :=
  FiniteSum.Fin.sumFin fun row => coefficients row * (bank.get row).primitive.value.eval (parent.edge.point parameter)

end BasisSourceLocations.PrimitiveBank

/-- Pointwise equal Gaussian paths have equal finite dyadic increment lists at every depth. -/
private theorem increments_congr {firstValue lastValue : InverseRootPolynomial.Coordinate →
  InverseRootPolynomial.Gaussian}
    (equal : ∀ parameter, firstValue parameter = lastValue parameter) (depth : Nat) (first last :
      InverseRootPolynomial.Coordinate) :
    DyadicPrimitivePaths.dyadicIncrements firstValue depth first last = DyadicPrimitivePaths.dyadicIncrements lastValue
      depth first last := by
  induction depth generalizing first last with
  | zero => change [firstValue last - firstValue first] = [lastValue last - lastValue first]; rw [equal, equal]
  | succ depth ih => rw [DyadicPrimitivePaths.dyadicIncrements, DyadicPrimitivePaths.dyadicIncrements, ih, ih]

namespace CommonPrimitivePlans.Blocks

variable {polynomials :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
      index box}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index} {cells :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers
    index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {depth : Nat}

/-- The actual concatenated source blocks equal the dyadic increments of the original primitive bank on each retained
common interval. -/
theorem source_paths : {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    {plans : CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor intervals} →
    (blocks : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients depth plans) →
    (blocks.paths.map Prod.fst).flatten =
      (intervals.map (fun interval => DyadicPrimitivePaths.dyadicIncrements
        ((BasisSourceLocations.PrimitiveBank.value
        originals coefficients)) depth
        interval.edge.left.parameter interval.edge.right.parameter)).flatten
  | _, _, .nil => rfl
  | _, _, .cons (interval := interval) head _ remaining => by
      change head.source.increments ++ (remaining.paths.map Prod.fst).flatten =
        DyadicPrimitivePaths.dyadicIncrements
          ((BasisSourceLocations.PrimitiveBank.value
          originals coefficients)) depth interval.edge.left.parameter interval.edge.right.parameter ++ _
      rw [head.source.increments_eq,
        source_paths
        remaining]
      apply congrArg (fun path => path ++ _)
      apply Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.increments_congr
      intro parameter
      exact PrimitiveSample.sourceValue_readback interval regular polynomials originals cells coefficients parameter

/-- Common-cover completeness identifies the full original parent path. -/
theorem source_parent_path {minimum : Nat} {common : CommonCover.BasisCommonCover cover covers minimum}
    {plans : CommonPrimitiveAcquisition.CommonPrimitivePlans regular target floor common.intervals}
    (blocks : CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients depth plans) :
    (blocks.paths.map Prod.fst).flatten = DyadicPrimitivePaths.dyadicIncrements
      ((BasisSourceLocations.PrimitiveBank.value
      originals coefficients)) (common.depth + depth) 0 1 := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.CommonPrimitivePlans.Blocks.source_paths
    blocks]
  have mapEq : common.intervals.map (fun interval => DyadicPrimitivePaths.dyadicIncrements
    ((Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
    originals coefficients)) depth
      interval.edge.left.parameter interval.edge.right.parameter) =
      (common.intervals.map BasisCommonInterval.edge).map (fun edge => DyadicPrimitivePaths.dyadicIncrements
        ((BasisSourceLocations.PrimitiveBank.value
        originals coefficients)) depth
        edge.left.parameter edge.right.parameter) := by
    rw [Purelib.Data.List.Map.map_map]
    rfl
  rw [mapEq, common.edges_eq, DyadicPrimitivePaths.dyadicEdges_flatten_increments]
  rfl

end CommonPrimitivePlans.Blocks

namespace CommonPrimitiveRequest.Acquisition

variable {minimum : Nat} {common :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}
  {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {request : CommonPrimitiveRequest
    regular common allowance floor} {polynomials :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
        index box}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index} {cells :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers
    index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {depth : Nat}

/-- The cached source area is the complete original parent path area. -/
theorem source_area (acquired : CommonPrimitiveRequest.Acquisition request polynomials originals cells coefficients
  depth) :
    acquired.source.area = IncrementArea.pathArea
      (DyadicPrimitivePaths.dyadicIncrements
        ((BasisSourceLocations.PrimitiveBank.value
        originals coefficients)) (common.depth + depth) 0 1) := by
  rw [acquired.source.area_eq,
    CommonPrimitivePlans.Blocks.source_parent_path
    acquired.blocks]

/-- The requested comparison now names the original parent primitive path, while retaining the actual pullback path and
its independently cached area. -/
theorem original_bound (acquired : CommonPrimitiveRequest.Acquisition request polynomials originals cells coefficients
  depth) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea (DyadicPrimitivePaths.dyadicIncrements
      ((BasisSourceLocations.PrimitiveBank.value
      originals coefficients)) (common.depth + depth) 0 1) -
      acquired.pullback.area) ≤ allowance^2 * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  rw [←
    source_area
    acquired, ← acquired.difference_eq]
  exact acquired.bounded

end CommonPrimitiveRequest.Acquisition
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
