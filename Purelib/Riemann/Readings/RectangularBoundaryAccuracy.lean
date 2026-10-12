module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Branches.RectangularSheetGauge

import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Topology.Grid.Signs
public import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.Tactic.Ring

open Purelib.Riemann.Normalization.InverseRootPolynomial

@[expose] public section

/-!
# A computed accuracy request for the complete regular-grid boundary

Pay coarse seams and coarse corner polygons before any spatial refinement.
The returned grid model request works for every subsequent dyadic mesh depth.
No caller-supplied seam, corner, or total-error smallness check is needed.
-/

namespace Purelib.Riemann.Readings.RectangularBoundaryAccuracy

open Purelib.Data.Rat

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Readings.RectangularBoundaryAssembly (BoundaryAssembly)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Data in
/-- The exact rational coordinate type. -/
private abbrev Coordinate := Rat.Fraction.Rational

set_option genInjectivity false in
/-- Retain a computed accuracy request for the complete regular-grid boundary.

The coarse seam and corner counts determine a paid tolerance before spatial refinement. One original grid-model request
then controls every later dyadic boundary assembly. -/
structure GridBoundaryAccuracy {polynomial numerator : Polynomial} {ambient : Box}
    {clearance : RegionClearance polynomial ambient} (bounds : PrimitiveOverlapBounds clearance numerator)
    (columns rows : Nat) (target : Coordinate) where
  /-- The cached original primitive boundary slope bound. -/ slope : Coordinate
  /-- The retained slope is the boundary slope from the original overlap bounds. -/ slope_eq : slope = boundarySlope
    bounds
  /-- The cached sum of squared horizontal and vertical coarse seam counts. -/ seamFactor : Coordinate
  /-- The seam factor equals the two explicit coarse-grid count squares. -/ seamFactor_eq : seamFactor = ((columns :
    Coordinate) * ((rows : Coordinate) + 1)) ^ 2 + (((columns : Coordinate) + 1) * (rows : Coordinate)) ^ 2
  /-- The cached squared number of coarse corner junctions. -/ cornerFactor : Coordinate
  /-- The corner factor is the coarse row-column product squared. -/ cornerFactor_eq : cornerFactor = ((columns :
    Coordinate) * (rows : Coordinate)) ^ 2
  /-- The retained coefficient paying seam and corner losses. -/ denominator : Coordinate
  /-- The payment coefficient is one plus the slope-weighted seam factor and corner factor. -/ denominator_eq :
    denominator = 1 + 32 * seamFactor * (4 * slope + 1) + 128 * cornerFactor
  /-- The payment coefficient is strictly positive. -/ denominator_positive : 0 < denominator
  /-- The computed model tolerance for the complete boundary. -/ tolerance : Coordinate
  /-- The selected model tolerance is strictly positive. -/ positive : 0 < tolerance
  /-- The selected model tolerance is at most one. -/ le_one : tolerance ≤ 1
  /-- The payment coefficient times the model tolerance fits the requested target. -/ paid : denominator * tolerance ≤
    target
  /-- The original grid primitive request at the selected tolerance. -/ gridRequest : GridPrimitiveAccuracy bounds
    columns tolerance

constructive_injectivity GridBoundaryAccuracy

namespace GridBoundaryAccuracy

variable {polynomial numerator : Polynomial} {ambient : Box} {clearance : RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator} {columns rows : Nat} {target : Coordinate}

open Purelib.Approximation in
open Purelib.Data in
/-- Compute and pay a common boundary tolerance from the original overlap bounds.

A positive target gives tolerance equal to target divided by payment coefficient plus target, retaining the exact coarse
seam and corner factors. -/
def build (bounds : PrimitiveOverlapBounds clearance numerator) (columns rows : Nat)
    (target : Coordinate) (targetPositive : 0 < target) : GridBoundaryAccuracy bounds columns rows target :=
  let columnCount := Rational.Budget.Aggregate.countCoordinate columns
  let rowCount := Rational.Budget.Aggregate.countCoordinate rows
  let slope := boundarySlope bounds
  let seamFactor := (columnCount * (rowCount + 1)) ^ 2 + ((columnCount + 1) * rowCount) ^ 2
  let cornerFactor := (columnCount * rowCount) ^ 2
  let denominator := 1 + 32 * seamFactor * (4 * slope + 1) + 128 * cornerFactor
  have slopeNonnegative : 0 ≤ slope := Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct bounds.numeratorUpper_nonnegative
        bounds.inverseUpper_positive.le)) ambient.diagonalSq_nonneg
  have seamNonnegative : 0 ≤ seamFactor := add_nonneg (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have cornerNonnegative : 0 ≤ cornerFactor := Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _
  have denominatorPositive : 0 < denominator := (show (0 : Coordinate) < 1 by decide).trans_le
    ((le_add_of_nonneg_right (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) seamNonnegative)
      (add_nonneg (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) slopeNonnegative) (by decide)))).trans
      (le_add_of_nonneg_right (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) cornerNonnegative)))
  have totalPositive : 0 < denominator + target := Rat.Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
    denominatorPositive targetPositive.le
  let tolerance := target / (denominator + target)
  have positive : 0 < tolerance := Rat.Fraction.Order.Field.div_pos_direct targetPositive totalPositive
  have cancel : (denominator + target) * tolerance = target := by
    rw [Rat.Fraction.Field.mul_comm]
    exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _ totalPositive.ne'
  { slope := slope
    slope_eq := rfl
    seamFactor := seamFactor
    seamFactor_eq := by dsimp only [seamFactor, columnCount, rowCount]; rw
      [Rational.Budget.Aggregate.countCoordinate_eq, Rational.Budget.Aggregate.countCoordinate_eq]
    cornerFactor := cornerFactor
    cornerFactor_eq := by dsimp only [cornerFactor, columnCount, rowCount]; rw
      [Rational.Budget.Aggregate.countCoordinate_eq, Rational.Budget.Aggregate.countCoordinate_eq]
    denominator := denominator
    denominator_eq := rfl
    denominator_positive := denominatorPositive
    tolerance := tolerance
    positive := positive
    le_one := (Rat.Fraction.Order.Field.div_le_iff_pos totalPositive).2 (by
      rw [Rat.Fraction.Field.one_mul]
      exact le_add_of_nonneg_left denominatorPositive.le)
    paid := (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (le_add_of_nonneg_right targetPositive.le) positive.le).trans_eq cancel
    gridRequest := GridPrimitiveAccuracy.build bounds columns tolerance positive }

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Every actual later boundary assembly satisfies the strict requested discrepancy bound.

The original aligned primitive banks, offsets and ambient refinements feed the retained grid request; both coarse seam
and corner errors are paid independently of fine depth. -/
theorem accurate (request : GridBoundaryAccuracy bounds columns rows target)
    {geometry : Geometry columns rows} {bank : Bank polynomial geometry}
    {transitions : Transitions (bank.refine request.gridRequest.index)} {gauge : Grid.Signs.Gauge transitions.flatGrid}
    {primitives : Primitives (Branches.RectangularSheetGauge.Transitions.oriented transitions gauge) numerator} {anchors
      : PrimitiveAnchors primitives}
    {offsets : LinearAlgebra.Grid.Offsets anchors.edges} {depth : Nat} (assembly : BoundaryAssembly anchors offsets
      depth)
    (refines : ∀ column row, (geometry.box column row).Refines ambient) :
    normSq (assembly.localTotal - assembly.exterior) < target := by
  have globalNonnegative := request.gridRequest.edgeBound_nonnegative.trans request.gridRequest.edgeBound_le_globalBound
  have globalLe := request.gridRequest.accurate.le.trans request.le_one
  have edgeLe := request.gridRequest.edgeBound_le_globalBound.trans globalLe
  have seamNonnegative : 0 ≤ request.seamFactor := by
    rw [request.seamFactor_eq]
    exact add_nonneg (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _) (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct
      _)
  have cornerNonnegative : 0 ≤ request.cornerFactor := by
    rw [request.cornerFactor_eq]; exact Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _
  have squareLe : request.gridRequest.globalBound ^ 2 ≤ request.gridRequest.globalBound := by
    have product := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct globalLe globalNonnegative
    exact (show request.gridRequest.globalBound ^ 2 = request.gridRequest.globalBound * request.gridRequest.globalBound
      by ring1).trans_le
      (product.trans_eq (by ring1))
  have raw := Readings.RectangularSeamBounds.GridPrimitiveAccuracy.boundaryDiscrepancy_bound request.gridRequest
    assembly refines
  rw [← request.seamFactor_eq, ← request.cornerFactor_eq, ← request.slope_eq] at raw
  calc
    _ ≤ _ := raw
    _ ≤ 32 * request.seamFactor * request.gridRequest.globalBound * (4 * request.slope + 1) +
        128 * request.cornerFactor * request.gridRequest.globalBound := add_le_add
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add le_rfl edgeLe)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
          (by decide +kernel) seamNonnegative) globalNonnegative))
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe
        (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) cornerNonnegative))
    _ ≤ request.denominator * request.gridRequest.globalBound := by
      rw [request.denominator_eq]
      exact (le_add_of_nonneg_right globalNonnegative).trans_eq (by ring1)
    _ < request.denominator * request.tolerance := Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
      request.denominator_positive request.gridRequest.accurate
    _ ≤ target := request.paid

end GridBoundaryAccuracy

end Purelib.Riemann.Readings.RectangularBoundaryAccuracy
