module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAdjacency
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedArea
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib

open Purelib.Riemann

public section

/-! Prepay physical connector insertion before polynomial and root sampling.
One local tolerance pays the complete parent area and endpoint errors. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target allowance : Normalization.InverseRootPolynomial.Coordinate}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)}

set_option genInjectivity false in
/-- A paid whole-parent request for inserting the original physical connectors.

It retains the primitive slope bound, actual interval count, one positive local tolerance and separate complete area and
endpoint payment inequalities. -/
structure BasisCommonConnectorBudget (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds
  bounds)
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals)
    (parentAllowance : Normalization.InverseRootPolynomial.Coordinate) (joinFloor : Nat) where
  /-- The retained common ceiling for the actual chart block totals. -/ bound :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The ceiling uses the original primitive slope and chart allowance. -/ bound_eq : bound = 2 * (2 *
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers + 1) +
    allowance^2)
  /-- The cached whole-parent connector error weight. -/ weight : Normalization.InverseRootPolynomial.Coordinate
  /-- The weight pays the actual interval count and every connector interaction with retained block totals. -/ weight_eq
    : weight = (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 + 8 * (intervals.length :
    Normalization.InverseRootPolynomial.Coordinate)^2 * bound +
    64 * (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^4 * (1 + bound)
  /-- The common local connector tolerance. -/ tolerance : Normalization.InverseRootPolynomial.Coordinate
  /-- The tolerance is the minimum of one and the weighted allowance for the squared parent target. -/ tolerance_eq :
    tolerance = min 1 (Rational.Budget.Weighted.allowance (parentAllowance^2) weight)
  /-- The retained connector tolerance is positive. -/ positive : 0 < tolerance
  /-- The original physical junction requests at that same local tolerance and supplied floor. -/ junctions :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions basis tolerance joinFloor requests
  /-- The complete connector insertion area error is paid by the squared parent allowance. -/ area_paid : 8 *
    (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * tolerance * bound +
    64 * (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^4 * tolerance * (tolerance + bound) ≤
      parentAllowance^2
  /-- The complete connector total-increment error is paid by the squared parent allowance. -/ total_paid :
    (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * tolerance ≤ parentAllowance^2

constructive_injectivity BasisCommonConnectorBudget

namespace BasisCommonConnectorBudget

/-- Prepare all original physical junction requests and prepay their complete parent area and endpoint errors. -/
@[expose] def build (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals)
    (links : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAdjacency.BasisCommonInterval.Links intervals)
      (parentAllowance : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < parentAllowance)
    (joinFloor : Nat) : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget.BasisCommonConnectorBudget
      basis requests parentAllowance joinFloor := open Purelib.Data.Rat in by
  let bound := 2 * (2 *
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers + 1) +
    allowance^2)
  have boundNonnegative : 0 ≤ bound := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
      covers) (by decide)))
    (Fraction.Order.Arithmetic.sq_nonneg_direct allowance))
  let count := (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2
  let first := 8 * (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * bound
  let last := 64 * (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^4
  have countNonnegative : 0 ≤ count := Fraction.Order.Arithmetic.sq_nonneg_direct _
  have firstNonnegative : 0 ≤ first := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      boundNonnegative
  have lastNonnegative : 0 ≤ last := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4)
  have enlargedNonnegative : 0 ≤ last * (1 + bound) := Fraction.Order.Arithmetic.mul_nonneg_direct lastNonnegative
    (add_nonneg (by decide) boundNonnegative)
  let weight := count + first + last * (1 + bound)
  have weightNonnegative : 0 ≤ weight := add_nonneg (add_nonneg countNonnegative firstNonnegative) enlargedNonnegative
  let tolerance := min 1 (Rational.Budget.Weighted.allowance (parentAllowance^2) weight)
  have tolerancePositive : 0 < tolerance := Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide)
    (Rational.Budget.Weighted.allowance_positive (Fraction.Order.Arithmetic.pow_pos_direct positive 2)
      weightNonnegative)
  have small : tolerance ≤ 1 := Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (show tolerance ≤ Rational.Budget.Weighted.allowance (parentAllowance^2) weight from
      Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _) weightNonnegative).trans
    (Rational.Budget.Weighted.mul_allowance_le (Fraction.Order.Arithmetic.sq_nonneg_direct parentAllowance)
      weightNonnegative)
  have totalCoefficient : count ≤ weight :=
    (le_add_of_nonneg_right firstNonnegative).trans (le_add_of_nonneg_right enlargedNonnegative)
  have areaCoefficient : first + last * (1 + bound) ≤ weight := by
    exact (le_add_of_nonneg_left countNonnegative).trans_eq (by dsimp only [weight]; ring1)
  have areaTerm := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct small (le_rfl : bound ≤ bound))
    (Fraction.Order.Arithmetic.mul_nonneg_direct lastNonnegative tolerancePositive.le)
  have area := Fraction.Order.Arithmetic.add_le_add_direct (le_rfl : first * tolerance ≤ first * tolerance) areaTerm
  let junctions := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions.build basis tolerance
    tolerancePositive joinFloor requests links
  refine ⟨bound, rfl, weight, rfl, tolerance, rfl, tolerancePositive, junctions, ?_, ?_⟩
  · exact (show 8 * (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * tolerance * bound +
        64 * (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^4 * tolerance * (tolerance + bound) =
        first * tolerance + last * tolerance * (tolerance + bound) by ring1).trans_le
      (area.trans ((show first * tolerance + last * tolerance * (1 + bound) =
        (first + last * (1 + bound)) * tolerance by ring1).trans_le
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct areaCoefficient tolerancePositive.le).trans
          paid)))
  · exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct totalCoefficient tolerancePositive.le).trans paid

variable {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
    target allowance floor sourceFloor intervals}
  {parentAllowance : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {polynomials :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {radialDepth : Nat}
  {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
    polynomials minimum requests}
  {readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings
    anchorBank bank stage requests plans}

/-- The actual joined parent area and original chart area meet the retained homogeneous connector-area bound. -/
theorem area_bounded (budget :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget.BasisCommonConnectorBudget basis requests
  parentAllowance joinFloor)
    (paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings)
    (connectors : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients radialDepth
      budget.tolerance requests plans readings)
    {primitiveTarget : Normalization.InverseRootPolynomial.Coordinate} {primitiveFloor : Nat}
    {primitivePlans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans regular
      primitiveTarget primitiveFloor intervals}
    (blocks : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks regular
      polynomials originals bank coefficients depth primitivePlans)
    (small : primitiveTarget ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq
      ((CommonConnectedPaths.BasisCommonChartRequests.Plans.Paths.joinedSummary
      0 paths connectors).area - paths.chartSummary.area) ≤
      parentAllowance^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := open
        Purelib.Data.Rat in by
  have estimate :=
    CommonConnectedArea.BasisCommonChartRequests.Plans.Paths.joined_parent_area_bound
    paths connectors blocks small budget.positive.le
  dsimp only at estimate
  rw [← budget.bound_eq] at estimate
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct budget.area_paid
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- The actual joined parent total and original chart total meet the retained homogeneous connector endpoint bound. -/
theorem total_bounded (budget :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget.BasisCommonConnectorBudget basis requests
  parentAllowance joinFloor)
    (paths : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings)
    (connectors : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Connectors coefficients radialDepth
      budget.tolerance requests plans readings) :
    Data.Gaussian.Norm.Basic.normSq
      ((CommonConnectedPaths.BasisCommonChartRequests.Plans.Paths.joinedSummary
      0 paths connectors).total - paths.chartSummary.total) ≤
      parentAllowance^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open Purelib.Algebra
        in open Purelib.Data.Rat in by
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  exact
    (CommonConnectedArea.BasisCommonChartRequests.Plans.Paths.joined_total_bound
    paths connectors budget.positive.le).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct budget.total_paid nonnegative)

end BasisCommonConnectorBudget
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget
