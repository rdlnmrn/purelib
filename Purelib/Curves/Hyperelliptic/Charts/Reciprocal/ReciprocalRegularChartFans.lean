module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedPairedRadialRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialPairedArcs
import Purelib.Riemann.RootContinuation.RootRadialPairedBoundary
import Purelib.Riemann.RootContinuation.RootRadialRefinement
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Physical-coordinate fans reuse the existing shared radial request.
The retained vertices are inverse source points, never even-sheet signs. -/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Integration.Path
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Normalization
open Purelib.Riemann.RootContinuation.RootRadialGeometry
open Purelib.Riemann.RootContinuation.RootRadialPairedArcs
open Purelib.Riemann.RootContinuation.RootRadialPairedBoundary
open Purelib.Riemann.RootContinuation.RootRadialRefinement

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover CommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank (ChartRequest junctionLeft junctionRight
  ChartPlan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation (ChartPreparation IntervalAt)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank (fanEdgeWeight)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources.SourceChartRequest (Parameter)
open Purelib.Riemann.RootContinuation

variable {genus count otherCount depth floor index : Nat} {curve : HyperellipticCurve
  genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent}
  {otherPatch : PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Data patch count} {otherData :
    Data otherPatch otherCount}
  {cover : Cover data} {otherCover :
    Cover otherData}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    CommonCover cover otherCover}
  {target : Coordinate} {request :
    ChartRequest regular common depth target floor}
  (evaluated : Evaluation request
    index)

/-- The physical inverse source point at the actual retained chart vertex.

The coordinate uses the original parent parameter and is independent of the selected root sheet. -/
@[expose] def regularCoordinate (i : Fin common.intervals.length)
    (vertex : Fin ((request.plans.get i).geometry.tail.length + 1)) : Gaussian :=
  (parent.edge.point (SourceChartRequest.Parameter
    (geometry := (request.plans.get i).geometry) vertex))⁻¹

/-- Every retained physical inverse vertex lies in the polynomial's regular reciprocal disk. -/
theorem regularCoordinate_inside (i : Fin common.intervals.length)
    (vertex : Fin ((request.plans.get i).geometry.tail.length + 1)) :
    Reciprocal.Bounds.InDisk curve.polynomial
      (regularCoordinate (request := request) i
      vertex) :=
  ReciprocalExteriorCollar.inverse_inDisk curve (data.boundary.point
    ⟨(CommonChartPreparation.IntervalAt common i).first.owner.left.inside.1.trans
      ((request.plans.get i).geometry.vertices.get vertex).first.root.between.1,
      ((request.plans.get i).geometry.vertices.get vertex).first.root.between.2.trans
        (CommonChartPreparation.IntervalAt common i).first.owner.right.inside.2⟩)

/-- The paired radial area potential at one actual retained physical inverse vertex and radial depth. -/
@[expose] def regularPotential (radialDepth : Nat) (i : Fin common.intervals.length)
    (vertex : Fin ((request.plans.get i).geometry.tail.length + 1)) : Gaussian :=
  Bilinear.radialArea (CommonChartRadialJunctions.radialValues evaluated) radialDepth
    (regularCoordinate (request := request) i vertex)

/-- The original interval's physical inverse-coordinate arc area using the two exact shared cap samples. -/
@[expose] def regularArcArea (radialDepth : Nat) (i : Fin common.intervals.length) : Gaussian :=
  SourceChartRequest.regularArcArea (request.plans.get i).geometry
    evaluated.samples.firstCap evaluated.samples.otherCap radialDepth

/-- The complete physical interval boundary area, including its first and last radial potentials. -/
@[expose] def regularIntervalBoundary (radialDepth : Nat) (i : Fin common.intervals.length) : Gaussian :=
  regularPotential evaluated radialDepth i 0 +
    regularArcArea evaluated radialDepth i -
    regularPotential evaluated radialDepth i (Fin.last
      (request.plans.get i).geometry.tail.length)

/-- The radial potentials at each actual retained neighboring owner junction are equal. -/
theorem regularPotential_join (radialDepth : Nat) (i : Fin (common.intervals.length - 1)) :
    regularPotential evaluated radialDepth
      (CommonChartBank.junctionLeft common i)
      (Fin.last (request.plans.get (CommonChartBank.junctionLeft common i)).geometry.tail.length) =
    regularPotential evaluated radialDepth
      (CommonChartBank.junctionRight common i) 0 :=
  congrArg (fun point : InverseRootPolynomial.Gaussian => Bilinear.radialArea (CommonChartRadialJunctions.radialValues
    evaluated) radialDepth point⁻¹)
    (request.junctions.get i).owners.first.point_eq

/-- A finite chain of matching consecutive endpoints telescopes to its first endpoint minus its last. -/
private theorem linked_sum {n : Nat} (first last : Fin (n + 1) → InverseRootPolynomial.Gaussian)
    (links : ∀ i : Fin n, first i.succ = last i.castSucc) :
    FiniteSum.Fin.sumFin (fun i => first i - last i) = first 0 - last (Fin.last n) := by
  induction n with
  | zero =>
      rw [FiniteSum.Fin.sumFin_succ]
      change first 0 - last 0 + 0 = first 0 - last 0
      ring1
  | succ n ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      have tail := ih (fun i => first i.succ) (fun i => last i.succ) (fun i => links i.succ)
      rw [tail]
      have join := links 0
      change first (Fin.succ 0) = last 0 at join
      rw [join]
      change first 0 - last 0 + (last 0 - last (Fin.last (n + 1))) = _
      ring1

/-- A nonempty retained endpoint chain telescopes after cancellation at every indexed internal join. -/
private theorem linked_sum_nonempty {n : Nat} (first last : Fin n → InverseRootPolynomial.Gaussian) (positive : 0 < n)
    (links : ∀ i : Fin (n - 1), first ⟨i.val + 1, by omega0⟩ = last ⟨i.val, by omega0⟩) :
    FiniteSum.Fin.sumFin (fun i => first i - last i) = first ⟨0, positive⟩ - last ⟨n - 1, by omega0⟩ := by
  cases n with
  | zero => exact (Nat.not_lt_zero _ positive).elim
  | succ n => exact linked_sum first last links

/-- Radial ends at every internal owner join are identical physical points. Only the two actual parent endpoints remain.
-/
theorem regular_boundary_eq (radialDepth : Nat) :
    FiniteSum.Fin.sumFin (regularIntervalBoundary
      evaluated radialDepth) =
      FiniteSum.Fin.sumFin (regularArcArea evaluated
        radialDepth) +
        Bilinear.radialArea (CommonChartRadialJunctions.radialValues evaluated) radialDepth (parent.edge.point 0)⁻¹ -
        Bilinear.radialArea (CommonChartRadialJunctions.radialValues evaluated) radialDepth (parent.edge.point 1)⁻¹ :=
          by
  let first := fun i => regularPotential evaluated
    radialDepth i 0
  let last := fun i => regularPotential evaluated
    radialDepth i (Fin.last (request.plans.get i).geometry.tail.length)
  have ends := linked_sum_nonempty first last
    common.nonempty (fun i => (regularPotential_join
    evaluated radialDepth i).symm)
  have firstEq : first common.firstIndex =
      Bilinear.radialArea (CommonChartRadialJunctions.radialValues evaluated) radialDepth (parent.edge.point 0)⁻¹ :=
    congrArg (fun parameter => Bilinear.radialArea (CommonChartRadialJunctions.radialValues evaluated) radialDepth
      (parent.edge.point parameter)⁻¹) common.first_parameter
  have lastEq : last common.lastIndex =
      Bilinear.radialArea (CommonChartRadialJunctions.radialValues evaluated) radialDepth (parent.edge.point 1)⁻¹ :=
    congrArg (fun parameter => Bilinear.radialArea (CommonChartRadialJunctions.radialValues evaluated) radialDepth
      (parent.edge.point parameter)⁻¹)
      ((request.plans.get common.lastIndex).geometry.last_parameter.trans common.last_parameter)
  change FiniteSum.Fin.sumFin (fun i => first i - last i) = first common.firstIndex - last common.lastIndex at ends
  rw [FiniteSum.Fin.sumFin_sub, firstEq, lastEq] at ends
  change FiniteSum.Fin.sumFin (fun i => first i +
    regularArcArea evaluated radialDepth i - last i) =
    _
  rw [FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_add]
  calc
    _ = FiniteSum.Fin.sumFin (regularArcArea evaluated
      radialDepth) + (FiniteSum.Fin.sumFin first - FiniteSum.Fin.sumFin last) := by
      ring1
    _ = _ := by rw [ends]; ring1

namespace FanRequest
variable {evaluated} {fanTarget : Coordinate} {minimum : Nat}

set_option genInjectivity false in
/-- One bounded physical-coordinate radial fan using the exact original chart edge and request parameters.

The retained paired polynomial sample supplies the actual area and its strict requested bound. -/
structure RegularFan (planned : CommonChartFans.FanRequest evaluated fanTarget minimum)
    (i : Fin common.intervals.length) (edge : Fin (request.plans.get i).geometry.tail.length) where
  /-- The actual bounded radial refinement between the two retained physical inverse vertices. -/ geometry :
    RootRadialRefinement.BoundedRefinement
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularCoordinate (request := request) i
      edge.castSucc)
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularCoordinate (request := request) i
      edge.succ) planned.parameters
  /-- The paired polynomial sample on that exact retained radial refinement. -/ sampled :
    RootRadialPairedBoundary.PairedPolynomialSample geometry planned.firstBounds planned.otherBounds
  /-- The actual retained fan area has squared norm below the requested fan tolerance. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq sampled.area < fanTarget

constructive_injectivity RegularFan

/-- Build the physical fan using the original request's radial parameters and both retained polynomial bounds. -/
@[expose] def acquireRegular (planned : CommonChartFans.FanRequest evaluated fanTarget minimum)
    (i : Fin common.intervals.length) (edge : Fin (request.plans.get i).geometry.tail.length) :
      RegularFan planned i edge := by
  have bounded (vertex) : Data.Gaussian.Norm.Basic.normSq
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularCoordinate (request := request) i vertex)
    ≤ 2 :=
    (Reciprocal.Bounds.disk_unit_bound
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularCoordinate_inside (request := request) i
      vertex)).trans (by decide)
  let geometry := BoundedRefinement.build (bounded edge.castSucc) (bounded edge.succ) planned.parameters
  let sampled := PairedPolynomialSample.build geometry planned.firstBounds planned.otherBounds
  have error : sampled.error = planned.error := by rw [sampled.error_eq, planned.error_eq, planned.scale_eq]
  exact ⟨geometry, sampled, sampled.bounded.trans_lt (error.trans_lt planned.accurate)⟩

/-- The retained sampled fan area equals its physical arc plus first radial potential minus last radial potential. -/
theorem RegularFan.boundary_eq {planned : CommonChartFans.FanRequest evaluated fanTarget minimum}
    {i : Fin common.intervals.length} {edge : Fin (request.plans.get i).geometry.tail.length}
    (fan : RegularFan planned i edge) :
    fan.sampled.area = Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularPotential evaluated
      planned.depth i edge.castSucc +
      Bilinear.arcArea (CommonChartRadialJunctions.radialValues evaluated) planned.depth
        (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularCoordinate (request := request) i
          edge.castSucc) (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularCoordinate (request
          := request) i edge.succ) -
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularPotential evaluated planned.depth i
        edge.succ := PairedPolynomialSample.boundary_eq_arcs fan.sampled

end FanRequest

namespace FanBankRequest
variable {evaluated} {requested : Coordinate} {minimum : Nat}

/-- The dependent vector of physical radial fans on every edge of one exact retained chart interval. -/
@[expose] def RegularIntervalFans (planned : CommonChartFanBank.FanBankRequest evaluated requested minimum) (i : Fin
  common.intervals.length) :=
  Data.Vector.DependentVector (fun edge : Fin (request.plans.get i).geometry.tail.length =>
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.FanRequest.RegularFan planned.fan i edge)

set_option genInjectivity false in
/-- The cached total physical fan area on one original retained chart interval.

Its exact sum and complete radial-boundary identity share the original dependent fan vector. -/
structure RegularInterval (planned : CommonChartFanBank.FanBankRequest evaluated requested minimum) (i : Fin
  common.intervals.length) where
  /-- The actual dependent fan vector on this original retained interval. -/ fans :
    RegularIntervalFans planned i
  /-- The cached total area of the retained interval fans. -/ area : InverseRootPolynomial.Gaussian
  /-- The cached interval area is exactly the sum of its original sampled fan areas. -/ area_eq : area =
    FiniteSum.Fin.sumFin (fun edge => (fans.get edge).sampled.area)
  /-- The cached interval area satisfies its retained strict allowance. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq area < planned.intervalAllowance
  /-- The cached interval area equals its complete original physical boundary. -/ boundary_eq : area =
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularIntervalBoundary evaluated
    planned.fan.depth i

constructive_injectivity RegularInterval

/-- The squared norm of the actual interval fan sum is below its retained interval allowance. -/
theorem regular_interval_bounded (planned : CommonChartFanBank.FanBankRequest evaluated requested minimum)
    (i : Fin common.intervals.length) (fans :
      RegularIntervalFans planned i) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun edge => (fans.get edge).sampled.area)) <
      planned.intervalAllowance := by
  have bound := Indexed.normSq_sumFin_le (fun edge => (fans.get edge).sampled.area)
    planned.fanAllowance (fun edge => (fans.get edge).accurate.le)
  have count : (request.plans.get i).geometry.tail.length ≤ planned.maximumEdges :=
    (DependentVector.get_le_maximum (CommonChartFanBank.fanEdgeWeight (request := request)) request.plans i).trans_eq
      planned.maximumEdges_eq.symm
  have squares := Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    (request.plans.get i).geometry.tail.length))
    (Fraction.Cast.Order.natCast_le_direct count) 2
  have counted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct squares planned.fanPositive.le
  have paid : (planned.maximumEdges : InverseRootPolynomial.Coordinate)^2 * planned.fanAllowance <
    planned.intervalAllowance :=
    (by ring1 : (planned.maximumEdges : InverseRootPolynomial.Coordinate)^2 * planned.fanAllowance =
      (planned.maximumEdges : InverseRootPolynomial.Coordinate) * ((planned.maximumEdges :
        InverseRootPolynomial.Coordinate) * planned.fanAllowance)).trans_lt planned.fanPaid
  exact bound.trans_lt (counted.trans_lt paid)

/-- The actual edge fan sum equals the retained physical interval's complete boundary area. -/
theorem regular_interval_boundary (planned : CommonChartFanBank.FanBankRequest evaluated requested minimum)
    (i : Fin common.intervals.length) (fans :
      RegularIntervalFans planned i) :
    FiniteSum.Fin.sumFin (fun edge => (fans.get edge).sampled.area) =
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularIntervalBoundary evaluated
      planned.fan.depth i := by
  have edges := FiniteSum.Fin.sumFin_congr (fun edge => (fans.get edge).boundary_eq)
  have telescoping := BoundaryRibbon.sum_increasing
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularPotential evaluated planned.fan.depth i)
  rw [FiniteSum.Fin.sumFin_sub] at telescoping
  calc
    _ = Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularArcArea evaluated planned.fan.depth i -
        (FiniteSum.Fin.sumFin (fun edge : Fin (request.plans.get i).geometry.tail.length =>
          Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularPotential evaluated planned.fan.depth
          i edge.succ) -
          FiniteSum.Fin.sumFin (fun edge : Fin (request.plans.get i).geometry.tail.length =>
            Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularPotential evaluated
            planned.fan.depth i edge.castSucc)) := by
      rw [edges, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_add]
      have scalar (a b c : InverseRootPolynomial.Gaussian) : a + b - c = b - (c - a) := by ring1
      exact scalar _ _ _
    _ = _ := by
      rw [telescoping];
      unfold Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularIntervalBoundary;
      ring1

/-- Acquire every physical fan on the original chart interval and cache their paid total and boundary identity. -/
@[expose] def acquireRegularInterval (planned : CommonChartFanBank.FanBankRequest evaluated requested minimum) (i : Fin
  common.intervals.length) :
    RegularInterval planned i :=
  let fans := DependentVector.ofFn (fun edge =>
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.FanRequest.acquireRegular planned.fan i edge)
  ⟨fans, FiniteSum.Fin.sumFin (fun edge => (fans.get edge).sampled.area), rfl,
    regular_interval_bounded planned i
      fans, regular_interval_boundary
      planned i fans⟩

set_option genInjectivity false in
/-- The complete physical fan bank on the original common interval cover.

The cached area retains its actual interval sum, whole requested bound and exact full boundary readback. -/
structure RegularBank (planned : CommonChartFanBank.FanBankRequest evaluated requested minimum) where
  /-- The actual dependent physical fan evaluations on every original common interval. -/ intervals :
    Data.Vector.DependentVector
    (RegularInterval planned)
  /-- The cached total area of all original retained interval evaluations. -/ area : InverseRootPolynomial.Gaussian
  /-- The complete area cache is exactly the sum of its actual retained interval areas. -/ area_eq : area =
    FiniteSum.Fin.sumFin (fun i => (intervals.get i).area)
  /-- The complete original physical fan bank satisfies the requested strict bound. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq area < requested
  /-- The complete area cache is the full sum of the original interval boundaries. -/ boundary_eq : area =
    FiniteSum.Fin.sumFin (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularIntervalBoundary
    evaluated planned.fan.depth)

constructive_injectivity RegularBank

/-- Acquire all original interval fans and cache their complete paid area with exact boundary readback. -/
@[expose] def acquireRegular (planned : CommonChartFanBank.FanBankRequest evaluated requested minimum) :
  RegularBank planned := by
  let intervals := DependentVector.ofFn (fun i =>
    acquireRegularInterval planned i)
  let area := FiniteSum.Fin.sumFin (fun i => (intervals.get i).area)
  have estimate := Indexed.normSq_sumFin_le (fun i => (intervals.get i).area)
    planned.intervalAllowance (fun i => (intervals.get i).bounded.le)
  have paid : (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * planned.intervalAllowance < requested :=
    (by ring1 : (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * planned.intervalAllowance =
      (common.intervals.length : InverseRootPolynomial.Coordinate) * ((common.intervals.length :
        InverseRootPolynomial.Coordinate) * planned.intervalAllowance)).trans_lt planned.intervalPaid
  exact ⟨intervals, area, rfl, estimate.trans_lt paid, FiniteSum.Fin.sumFin_congr (fun i => (intervals.get
    i).boundary_eq)⟩

/-- The full physical fan bank equals the original arc sum plus its first radial end minus its last radial end. -/
theorem RegularBank.open_boundary {planned : CommonChartFanBank.FanBankRequest evaluated requested minimum} (bank :
  RegularBank planned) :
    bank.area = FiniteSum.Fin.sumFin (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regularArcArea
      evaluated planned.fan.depth) +
      Bilinear.radialArea (CommonChartRadialJunctions.radialValues evaluated) planned.fan.depth (parent.edge.point 0)⁻¹
        -
      Bilinear.radialArea (CommonChartRadialJunctions.radialValues evaluated) planned.fan.depth (parent.edge.point 1)⁻¹
        :=
  bank.boundary_eq.trans (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.regular_boundary_eq
    evaluated planned.fan.depth)

end FanBankRequest

/-- The concrete chart-versus-arc budget of one retained interval plan: the actual retained geometry, the requested area
error, and the mesh arc error. -/
@[expose] def chartArcBudget {depth : Nat} {allowance : InverseRootPolynomial.Coordinate} {floor : Nat} {i : Fin
  common.intervals.length}
    (plan : CommonChartBank.ChartPlan regular common depth allowance floor i) : Coordinate :=
  2 * ((plan.geometry.tail.length : InverseRootPolynomial.Coordinate)^2 *
    (264 * regular.factorUpper^2 * (plan.budget.tolerance / 4 / 4)) +
    SourceChartRequest.regularArcError regular
      plan.geometry)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans
