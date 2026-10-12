module
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapTotals
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceAlignment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

public section

/-! A positive request pays the complete two-differential cap-total polygon
comparison before either cap or shared grid bank is sampled. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation
  (Request Samples sourceMaximum sourceMaximum_nonnegative)
open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility

namespace PairedCapRequest

/-- The per-occurrence allocation of a positive target does not exceed that target. -/
private theorem perTerm_le {target : Fraction.Rational} (positive : 0 < target) (count : Nat) :
    Purelib.Approximation.Rational.Budget.Aggregate.perTerm target count ≤ target := open Purelib.Approximation in by
  have countNonnegative : (0 : Fraction.Rational) ≤ count := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)
  have squareNonnegative := Fraction.Order.Arithmetic.sq_nonneg_direct (count : Fraction.Rational)
  have extra : 0 ≤ 2 * (count : Fraction.Rational)^2 + 4 * count + 1 :=
    add_nonneg (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) squareNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) countNonnegative)) (by decide)
  have denominatorLe : (1 : Fraction.Rational) ≤ 2 * ((count : Fraction.Rational) + 1)^2 :=
    (le_add_of_nonneg_right extra).trans_eq (by ring1)
  have denominatorPositive : 0 < (2 : Fraction.Rational) * ((count : Fraction.Rational) + 1)^2 :=
    lt_of_lt_of_le (by decide) denominatorLe
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct denominatorLe positive.le
  rw [mul_one] at scaled
  rw [Rational.Budget.Aggregate.perTerm, Rational.Budget.Aggregate.countCoordinate_eq]
  exact (Fraction.Order.Field.div_le_iff_pos denominatorPositive).mpr scaled

/-- Each original cap request's local allowance is bounded by its positive complete target. -/
private theorem local_le_target {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
    {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
    {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
      Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
    {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {prepared :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains differential} {target areaTarget : Fraction.Rational} {floor : Nat}
    (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request prepared target
      areaTarget floor) (positive : 0 < target) : request.localTarget ≤ target := by
  rw [request.localTarget_eq]
  exact ((Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.min_le_left _ _)).trans
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest.perTerm_le positive request.count)

end PairedCapRequest

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

set_option genInjectivity false in
/-- A paid comparison request for the complete original two-differential cap-total polygons.

The retained occurrence count and two source slopes determine one positive allowance. Both original cap requests retain
their own geometry and share that allowance and stage floor. -/
structure PairedCapRequest (first :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (last :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains other) (target : Fraction.Rational) (floor : Nat) where
  /-- The cached occurrence count of the first original cap preparation. -/ count : Nat
  /-- The count equals the complete original first occurrence-list length. -/ count_eq : count =
    first.occurrences.length
  /-- The cached common source-slope bound for the two original preparations. -/ slope : Fraction.Rational
  /-- The common slope is the maximum of their exact original source maxima. -/ slope_eq : slope = max
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.sourceMaximum first.occurrences)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.sourceMaximum last.occurrences)
  /-- The cached count-and-slope coefficient in the paired polygon error estimate. -/ coefficient : Fraction.Rational
  /-- The coefficient is sixteen times the fourth power of the count times twice the sum of the common slope and one. -/
    coefficient_eq : coefficient = 16 * (count : Fraction.Rational)^4 * (2 * (slope + 1))
  /-- The cached polygon-error coefficient is nonnegative. -/ coefficient_nonnegative : 0 ≤ coefficient
  /-- The shared positive local accuracy allocated to both cap requests. -/ allowance : Fraction.Rational
  /-- The accuracy divides the target by one plus the retained error coefficient. -/ allowance_eq : allowance = target /
    (coefficient + 1)
  /-- The allocated common cap accuracy is strictly positive. -/ positive : 0 < allowance
  /-- The retained error coefficient times the allocated accuracy is strictly below the target. -/ paid : coefficient *
    allowance < target
  /-- The original first cap request paid at the common allowance. -/ left :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request first allowance target
    floor
  /-- The original second cap request paid at the same allowance. -/ right :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request last allowance target
    floor

constructive_injectivity PairedCapRequest

namespace PairedCapRequest
variable {first :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential}
  {last :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains other} {target : Fraction.Rational} {floor : Nat}

/-- Construct both original cap requests with one allowance paying their complete paired-total error.

The positive target fixes the count-and-slope coefficient and its exact retained allocation before either supplied bank
is sampled. -/
@[expose] def build (first :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (last :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains other) (target : Fraction.Rational) (positive : 0 < target) (floor : Nat) :
    PairedCapRequest first last target floor := by
  let count := first.occurrences.length
  let slope := max (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.sourceMaximum
    first.occurrences) (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.sourceMaximum
    last.occurrences)
  have slopeNonnegative : 0 ≤ slope :=
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.sourceMaximum_nonnegative
    first.occurrences).trans (Fraction.Order.Basic.le_max_left _ _)
  let coefficient := 16 * (count : Fraction.Rational)^4 * (2 * (slope + 1))
  have nonnegative : 0 ≤ coefficient := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg slopeNonnegative (by decide)))
  have denominatorPositive : 0 < coefficient + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    nonnegative (by decide)
  let allowance := target / (coefficient + 1)
  have allowancePositive : 0 < allowance := Fraction.Order.Field.div_pos_direct positive denominatorPositive
  have paid : coefficient * allowance < target := by
    have coefficientIncrease : coefficient < coefficient + 1 := by
      have translated := Fraction.Order.Arithmetic.add_lt_add_left_direct
        (by decide : (0 : Fraction.Rational) < 1) coefficient
      rewrite [AddZeroClass.add_zero] at translated
      exact translated
    have increase := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      coefficientIncrease allowancePositive
    exact increase.trans_eq ((Fraction.Field.mul_comm _ _).trans
      (Fraction.Field.div_mul_cancel_of_ne target (coefficient + 1) denominatorPositive.ne'))
  exact ⟨count, rfl, slope, rfl, coefficient, rfl, nonnegative, allowance, rfl, allowancePositive, paid,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.build first allowance
      target allowancePositive positive floor,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.build last allowance
      target allowancePositive positive floor⟩

/-- The common stage threshold for the two retained cap requests. -/
@[expose] def index (allocated : PairedCapRequest first
  last target floor) : Nat := max allocated.left.index allocated.right.index

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest in
/-- The common reading threshold of both original cap requests. -/
@[expose] def readingIndex (allocated : PairedCapRequest
  first last target floor) : Nat :=
  max allocated.left.readingIndex allocated.right.readingIndex

variable {stage depth otherDepth readingIndex otherReadingIndex : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage box}
  {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    {otherShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other stage domains}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest in
/-- The requested bound holds on any common later bank. The supplied samples
retain both original cap paths, including unequal internal subdivisions. -/
theorem accurate (allocated : PairedCapRequest first last
  target floor)
    (left : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples
      allocated.left.entries sample shared depth readingIndex)
    (right : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Samples
      allocated.right.entries otherSample otherShared otherDepth otherReadingIndex)
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
      (lastReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared
      lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (first.sources.map (fun source =>
        (⟨source.increment firstReadings.values, source.increment lastReadings.values⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))) -
      Path.PairedIncrementArea.area ((left.pairedValues right).map Prod.snd)) < target := by
  have estimate := left.triangle_cap_area_error right firstReadings lastReadings
  have count : allocated.left.count = allocated.count := allocated.left.count_eq.trans allocated.count_eq.symm
  have slope : max allocated.left.slope allocated.right.slope = allocated.slope :=
    (congrArg₂ max allocated.left.slope_eq allocated.right.slope_eq).trans allocated.slope_eq.symm
  have errors : max allocated.left.localTarget allocated.right.localTarget ≤ allocated.allowance :=
    Fraction.Order.Basic.max_le (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest.local_le_target
      allocated.left allocated.positive) (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest.local_le_target
      allocated.right allocated.positive)
  have coefficient : 16 * (allocated.left.count : Fraction.Rational)^4 *
      (2 * (max allocated.left.slope allocated.right.slope + 1)) = allocated.coefficient := by
    rw [count, slope]
    exact allocated.coefficient_eq.symm
  have payment := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errors allocated.coefficient_nonnegative
  have rearrange : 16 * (allocated.left.count : Fraction.Rational)^4 *
      max allocated.left.localTarget allocated.right.localTarget *
        (2 * (max allocated.left.slope allocated.right.slope + 1)) =
      allocated.coefficient * max allocated.left.localTarget allocated.right.localTarget := by
    rw [← coefficient]
    ring1
  exact estimate.trans_lt ((rearrange.trans_le payment).trans_lt allocated.paid)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest in
set_option genInjectivity false in
/-- Both requests evaluate against supplied banks at one stage. -/
structure Evaluation (allocated : PairedCapRequest first
  last target floor)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage box)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains)
      (otherShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other stage domains)
    (depth otherDepth readingIndex : Nat) where
  /-- The complete retained evaluation of the first cap request on its supplied banks. -/ left :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation allocated.left
    sample shared depth readingIndex
  /-- The complete retained evaluation of the second cap request on its supplied banks. -/ right :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request.Evaluation allocated.right
    otherSample otherShared otherDepth readingIndex

constructive_injectivity Evaluation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest in
/-- Evaluate both retained cap requests against supplied banks at one sufficiently late stage and reading index.

The two independent cap subdivision depths and both original shared grid banks remain indexed in the result. -/
@[expose] def evaluate (allocated : PairedCapRequest first
  last target floor)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage box)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains)
      (otherShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other stage domains)
    (depth otherDepth readingIndex : Nat) (later : allocated.index ≤ stage)
    (readingLater : allocated.readingIndex ≤ readingIndex) :
    Evaluation allocated sample
      otherSample shared otherShared depth otherDepth readingIndex :=
  ⟨allocated.left.evaluate sample shared depth readingIndex
      ((Data.Nat.Order.le_max_left _ _).trans later) ((Data.Nat.Order.le_max_left _ _).trans readingLater),
   allocated.right.evaluate otherSample otherShared otherDepth readingIndex
      ((Data.Nat.Order.le_max_right _ _).trans later) ((Data.Nat.Order.le_max_right _ _).trans readingLater)⟩

namespace Evaluation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest in
/-- The retained paired evaluation satisfies the requested shared-triangle versus cap-total area bound. -/
theorem accurate {allocated : PairedCapRequest
  first last target floor}
    (evaluated : Evaluation allocated
      sample otherSample shared otherShared depth otherDepth readingIndex)
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
      (lastReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared
      lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (first.sources.map (fun source =>
        (⟨source.increment firstReadings.values, source.increment lastReadings.values⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))) -
      Path.PairedIncrementArea.area ((evaluated.left.samples.pairedValues evaluated.right.samples).map Prod.snd)) <
        target :=
  allocated.accurate evaluated.left.samples evaluated.right.samples firstReadings lastReadings

end Evaluation

end PairedCapRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
