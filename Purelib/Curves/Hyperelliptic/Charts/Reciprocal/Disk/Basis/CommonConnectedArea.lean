module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Decide
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementAreaJoins
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths.BasisCommonChartRequests.Plans

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib

open Purelib.Riemann

public section

/-! Complete connector insertion errors depend on the retained interval count,
not on the number of internal chart segments. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedArea

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {regular : RegularBounds.Data cap} {model :
    UniformReciprocalRootChannels.RootModel cell}
  {parameter target sourceTarget : Normalization.InverseRootPolynomial.Coordinate} {floor sourceFloor : Nat}
  {covers : SourceLocations.BasisSourceCovers parent}

variable {cover : UniformReciprocalCover.Cover data}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {depth : Nat} {allowance : Normalization.InverseRootPolynomial.Coordinate}

variable {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace BasisCommonChartRequests.Plans

variable {anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index
  cover.mesh.edges}
  {bank : SourceLocations.BasisSourceLocations.SampleBank covers index}
  {originals : CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Paths

variable {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {radialDepth : Nat}

/-- Every actual inserted connector satisfies the retained homogeneous joining bound, including the supplied incoming
connector. -/
private theorem joinedBlocks_small (incoming : Normalization.InverseRootPolynomial.Gaussian) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals} →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans} →
    (paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings) →
    (connectors : CommonConnectorBank.Connectors coefficients radialDepth
      joinTarget requests plans readings) →
    Gaussian.Norm.Basic.normSq incoming ≤ joinTarget * Readings.PreparedObservationCoercivity.coefficientNormSq
      coefficients →
    ∀ block ∈
      Paths.joinedBlocks
      incoming paths connectors, Gaussian.Norm.Basic.normSq block.1 ≤ joinTarget *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
  | _, .nil, _, _, _, _, _, _, member => False.elim (List.not_mem_nil member)
  | _, .cons _ .nil, _, _, _, _, small, block, member => by
      cases Purelib.Data.List.Membership.mem_singleton.mp member
      exact small
  | _, .cons _ (.cons _ _), _, _, paths, connectors, small, block, member => by
      rcases Purelib.Data.List.Membership.mem_cons.mp member with same | member
      · subst block; exact small
      · exact
          joinedBlocks_small
          connectors.1.increment paths.2 connectors.2 connectors.1.increment_bound block member

/-- The original chart block-total bounds also bound the corresponding blocks after connector insertion. -/
private theorem joinedBlocks_bounded (incoming : Normalization.InverseRootPolynomial.Gaussian)
    {intervals : List (CommonCover.BasisCommonInterval cover covers)}
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals}
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans}
    (paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings)
    (connectors : CommonConnectorBank.Connectors coefficients radialDepth
      joinTarget requests plans readings)
    {bound : Normalization.InverseRootPolynomial.Coordinate} (bounded : ∀ pair ∈ paths.pairs,
      Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum pair.2) ≤ bound) :
    ∀ block ∈
      Paths.joinedBlocks
      incoming paths connectors, Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum block.2)
      ≤ bound := by
  intro block member
  have inOriginal : block.2 ∈
    (Paths.joinedBlocks
    incoming paths connectors).map Prod.snd :=
    Data.List.Map.mem_map.mpr ⟨block, member, rfl⟩
  rw
    [Paths.joinedBlocks_original
    incoming paths connectors] at inOriginal
  obtain ⟨pair, inPairs, equal⟩ := Data.List.Map.mem_map.mp inOriginal
  rw [← equal]
  exact bounded pair inPairs

/-- The squared norm of the retained coefficient vector is nonnegative. -/
private theorem norm_nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open
  Purelib.Algebra in FiniteSum.Fin.sumFin_zero.symm.trans_le
  (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
    Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => normSq_nonneg (coefficients
    row)))

/-- Every inserted connector is paid, including its interaction with all
other block totals. The leading zero fixes the original initial point. -/
theorem joined_area_bound
    {intervals : List (CommonCover.BasisCommonInterval cover covers)}
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals}
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans}
    (paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings)
    (connectors : CommonConnectorBank.Connectors coefficients radialDepth
      joinTarget requests plans readings)
    (positive : 0 ≤ joinTarget) {bound : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ bound)
    (bounded : ∀ pair ∈ paths.pairs, Gaussian.Norm.Basic.normSq (Gaussian.Norm.Sum.Basic.gaussianSum
      pair.2) ≤ bound * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Gaussian.Norm.Basic.normSq
      ((Paths.joinedSummary
      0 paths connectors).area - paths.chartSummary.area) ≤
      (8 * (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * joinTarget * bound +
        64 * (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^4 * joinTarget * (joinTarget + bound))
          * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := open Purelib.Data.Rat in open
          Purelib.Integration in by
  have errorNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct positive
    (norm_nonnegative
    (coefficients := coefficients))
  have zeroSmall : Gaussian.Norm.Basic.normSq (0 : Normalization.InverseRootPolynomial.Gaussian) ≤ joinTarget *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [Gaussian.Norm.Basic.normSq_zero]; exact errorNonnegative
  have estimate := Path.IncrementAreaJoins.joined_blocks_area_bound
    (Paths.joinedBlocks 0
    paths connectors)
    errorNonnegative (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative
      norm_nonnegative)

      (joinedBlocks_small
      0 paths connectors zeroSmall)
      (joinedBlocks_bounded
      0 paths connectors bounded)
  rw
    [Paths.joinedBlocks_count,
    Paths.joinedBlocks_original,
    ←
    (Paths.joinedSummary
    0 paths connectors).area_eq,
    ← paths.chartSummary.area_eq] at estimate
  exact estimate.trans_eq (by ring1)

/-- The total error from inserting all original connectors is bounded by the squared retained interval count times the
homogeneous joining target. -/
theorem joined_total_bound
    {intervals : List (CommonCover.BasisCommonInterval cover covers)}
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals}
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans}
    (paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings)
    (connectors : CommonConnectorBank.Connectors coefficients radialDepth
      joinTarget requests plans readings)
    (positive : 0 ≤ joinTarget) :
    Gaussian.Norm.Basic.normSq
      ((Paths.joinedSummary
      0 paths connectors).total - paths.chartSummary.total) ≤
      (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * joinTarget *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open Purelib.Data.Rat in open
        Purelib.Integration in by
  have zeroSmall : Gaussian.Norm.Basic.normSq (0 : Normalization.InverseRootPolynomial.Gaussian) ≤ joinTarget *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [Gaussian.Norm.Basic.normSq_zero]; exact Fraction.Order.Arithmetic.mul_nonneg_direct positive
      norm_nonnegative
  have estimate := Path.IncrementAreaJoins.joined_blocks_total_bound
    (Paths.joinedBlocks 0
    paths connectors)

      (joinedBlocks_small
      0 paths connectors zeroSmall)
  rw
    [Paths.joinedBlocks_count,
    Paths.joinedBlocks_original,
    ←
    (Paths.joinedSummary
    0 paths connectors).total_eq,
    ← paths.chartSummary.total_eq] at estimate
  exact estimate.trans_eq (by ring1)

open Purelib.Data.Rat in
/-- The retained primitive blocks supply the chart-total ceiling, without
an additional numerical hypothesis or a new sampling bank. -/
theorem joined_parent_area_bound
    {intervals : List (CommonCover.BasisCommonInterval cover covers)}
    {requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals}
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} {readings :
      CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans}
    (paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings)
    (connectors : CommonConnectorBank.Connectors coefficients radialDepth
      joinTarget requests plans readings)
    {primitiveTarget : Normalization.InverseRootPolynomial.Coordinate} {primitiveFloor : Nat}
    {primitivePlans : CommonPrimitiveAcquisition.CommonPrimitivePlans regular
      primitiveTarget primitiveFloor intervals}
    (blocks : CommonPrimitiveAcquisition.CommonPrimitivePlans.Blocks regular
      polynomials originals bank coefficients depth primitivePlans)
    (small : primitiveTarget ≤ 1) (positive : 0 ≤ joinTarget) :
    let bound := 2 * (2 *
      (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers + 1) +
      allowance^2)
    Gaussian.Norm.Basic.normSq
      ((Paths.joinedSummary
      0 paths connectors).area - paths.chartSummary.area) ≤
      (8 * (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * joinTarget * bound +
        64 * (intervals.length : Normalization.InverseRootPolynomial.Coordinate)^4 * joinTarget * (joinTarget + bound))
          * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  dsimp only
  apply
    joined_area_bound
    paths connectors positive
    (Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
      (Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
        (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
        covers) (by decide)))
      (Arithmetic.sq_nonneg_direct allowance)))
  intro pair member
  exact (CommonChartArea.BasisCommonChartRequests.Plans.Paths.block_bounds
    small paths blocks pair member).2.2.2

end Paths
end BasisCommonChartRequests.Plans
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedArea
