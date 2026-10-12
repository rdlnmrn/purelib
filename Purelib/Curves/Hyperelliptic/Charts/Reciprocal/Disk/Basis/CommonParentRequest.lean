module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAdjacency
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget
public import Purelib.Integration.Budget.Trace.Restoration
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Riemann

public section

/-! Select one common-parent geometry and numerical schedule before acquiring
polynomials. All subordinate requests retain their original common cover. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest

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

variable {minimum : Nat} {common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers
  minimum}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}

/-- The retained chart local allowance is bounded by the square of its parent allowance.

The cached weight is nonnegative, so division by its positive successor
retains the squared parent ceiling. The original minimum selects the allowance. -/
theorem chart_local_le_square {depth floor sourceFloor : Nat} {target allowance :
  Normalization.InverseRootPolynomial.Coordinate}
    (budget : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget.BasisCommonChartBudget common regular depth
      target allowance floor sourceFloor) :
    budget.localAllowance ≤ allowance^2 := by
  have weightNonnegative : 0 ≤ budget.weight := by
    rw [budget.weight_eq]
    exact add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
        (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (add_nonneg
            (CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative
            covers) (by decide))) (by decide)))
  rw [budget.local_eq]
  apply (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans
  apply (Fraction.Order.Field.div_le_iff_pos (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    weightNonnegative (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 1))).mpr
  exact (show allowance^2 = allowance^2 * 1 by ring1).trans_le
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ((AddZeroClass.zero_add _).symm.trans_le
      (Fraction.Order.Arithmetic.add_le_add_direct weightNonnegative (le_refl _)))
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))

set_option genInjectivity false in
/-- A complete common-parent geometric and numerical request on the original shared cover.

It retains coordinate and arc refinements, restoration and chart allowances, physical connector requests and the
prepared integral request before any polynomial acquisition. -/
structure BasisCommonParentRequest (common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover
  cover covers minimum)
    (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (allowance coefficientTarget : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original parent allowance is positive. -/ positive : 0 < allowance
  /-- The retained restoration allocation for the same parent allowance. -/ restoration :
    Budget.Trace.Restoration.BasisCommonRestorationAllowance allowance
  /-- The common-cover refinement at the supplied floor. -/ refinement :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest.BasisCommonDepthRequest common allowance floor
  /-- The retained coordinate requests on the original common intervals. -/ coordinates :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateRequest regular
    common.intervals refinement.depth
  /-- The arc requests using those same coordinates and basis bounds. -/ arcs :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest.BasisCommonArcRequest common basis coordinates allowance
  /-- The cached allowance used by every chart request. -/ chartAllowance :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The chart allowance is the minimum of one, the parent allowance and the incoming restoration allowance. -/
    chartAllowance_eq : chartAllowance = min 1 (min allowance restoration.incomingAllowance)
  /-- The cached chart allowance is positive. -/ chart_positive : 0 < chartAllowance
  /-- The chart allowance is paid by the parent allowance. -/ chart_le : chartAllowance ≤ allowance
  /-- The original chart requests using the retained arc depth and tolerance. -/ charts :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget.BasisCommonChartBudget common regular arcs.depth
    arcs.tolerance chartAllowance floor floor
  /-- The local chart error is paid by the incoming restoration allowance. -/ source_le : charts.localAllowance ≤
    restoration.incomingAllowance
  /-- The physical connector requests on those original chart requests. -/ connectors :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget.BasisCommonConnectorBudget basis charts.requests
    allowance floor
  /-- The prepared integral and coefficient request on the same common cover. -/ prepared :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest.BasisPreparedAreaRequest regular common allowance
    coefficientTarget floor
  /-- The cached joint chart and prepared-integral threshold. -/ index : Nat
  /-- The joint threshold is the maximum of the original prepared and chart thresholds. -/ index_eq : index = max
    prepared.request.index charts.requests.index
  /-- The cached stage floor for acquiring the actual chart readings. -/ readingFloor : Nat
  /-- The reading floor includes the supplied floor and every retained connector junction stage. -/ readingFloor_eq :
    readingFloor = max floor (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions.stage charts.requests
    connectors.junctions)

constructive_injectivity BasisCommonParentRequest

namespace BasisCommonParentRequest

/-- Prepare the complete common-parent schedule and its paid subordinate allowances.

The construction preserves the original common cover, basis bounds and coefficient target, with separate joint request
and reading thresholds. -/
@[expose] def build (common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers
  minimum)
    (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (allowance coefficientTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < allowance)
      (coefficientPositive : 0 < coefficientTarget)
    (floor : Nat) : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest.BasisCommonParentRequest common basis
      allowance coefficientTarget floor := by
  let restoration := Budget.Trace.Restoration.BasisCommonRestorationAllowance.build allowance positive
  let refinement := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest.BasisCommonDepthRequest.build common
    allowance positive floor
  let coordinates :=
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateRequest.build regular
    common.intervals refinement.depth
  let arcs := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest.BasisCommonArcRequest.build common basis
    coordinates allowance positive
  let chartAllowance := min 1 (min allowance restoration.incomingAllowance)
  have chartPositive : 0 < chartAllowance := Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide)
    (Purelib.Data.Rat.Fraction.Order.Basic.lt_min positive restoration.incoming_positive)
  have small : chartAllowance ≤ 1 := Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _
  have squareLe : chartAllowance^2 ≤ chartAllowance :=
    (show chartAllowance^2 = chartAllowance * chartAllowance by ring1).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small chartPositive.le).trans_eq
        (Fraction.Field.mul_one_direct _))
  let charts := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartBudget.BasisCommonChartBudget.build common regular
    arcs.depth arcs.tolerance chartAllowance
    arcs.tolerance_positive chartPositive floor floor
  have sourceLe : charts.localAllowance ≤ restoration.incomingAllowance :=
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest.chart_local_le_square charts).trans (squareLe.trans
      ((Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans
      (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _)))
  let connectors := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBudget.BasisCommonConnectorBudget.build
    basis charts.requests (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonAdjacency.BasisCommonCover.links common)
    allowance positive floor
  let prepared := Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest.BasisPreparedAreaRequest.build regular
    common allowance coefficientTarget positive coefficientPositive floor
  exact ⟨positive, restoration, refinement, coordinates, arcs, chartAllowance, rfl, chartPositive,
    (Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _).trans (Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _
      _), charts, sourceLe, connectors, prepared,
    max prepared.request.index charts.requests.index, rfl,
    max floor (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions.stage charts.requests
      connectors.junctions), rfl⟩

variable {allowance coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The retained arc depth is at least the original common refinement depth. -/
theorem refinement_le (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest.BasisCommonParentRequest
  common basis allowance coefficientTarget floor) :
    request.refinement.depth ≤ request.arcs.depth := request.coordinates.minimum_le.trans request.arcs.coordinate_le

/-- The joint threshold covers the original prepared integral request. -/
theorem prepared_le (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest.BasisCommonParentRequest
  common basis allowance coefficientTarget floor) :
    request.prepared.request.index ≤ request.index := (Purelib.Data.Nat.Order.le_max_left ..).trans_eq
      request.index_eq.symm

/-- The joint threshold covers every original chart request. -/
theorem charts_le (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest.BasisCommonParentRequest
  common basis allowance coefficientTarget floor) :
    request.charts.requests.index ≤ request.index := (Purelib.Data.Nat.Order.le_max_right ..).trans_eq
      request.index_eq.symm

/-- The reading floor covers every retained physical connector junction. -/
theorem connectors_le (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest.BasisCommonParentRequest
  common basis allowance coefficientTarget floor) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonJunctions.Junctions.stage request.charts.requests
      request.connectors.junctions ≤ request.readingFloor :=
  (Purelib.Data.Nat.Order.le_max_right ..).trans_eq request.readingFloor_eq.symm

end BasisCommonParentRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
