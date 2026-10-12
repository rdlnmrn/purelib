module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! The common-cover fan bank with all internal radial junctions paid.
Only the two outer radial ends survive; no root closure is asserted. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib
open Purelib.Riemann
open Purelib.Data.Rat

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Rat.Fraction.Compatibility

/-- The first left endpoint minus the last right endpoint, with zero for an empty bank. -/
@[expose] def endDifference {n : Nat} (first last : Fin n → Gaussian.Basic.Canonical) : Gaussian :=
  match n, first, last with
  | 0, _, _ => 0
  | n + 1, first, last => first 0 - last (Fin.last n)

/-- The sum of all interval differences minus the adjacent junction differences equals the two outer endpoint readings.
-/
private theorem telescope {n : Nat} (first last : Fin (n + 1) → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun i => first i - last i) -
      FiniteSum.Fin.sumFin (fun i : Fin n => first i.succ - last i.castSucc) = first 0 - last (Fin.last n) := by
  induction n with
  | zero =>
      rw [FiniteSum.Fin.sumFin_succ]
      change (first 0 - last 0 + 0) - 0 = first 0 - last 0
      ring1
  | succ n ih =>
      rw [FiniteSum.Fin.sumFin_succ (fun i => first i - last i),
        FiniteSum.Fin.sumFin_succ (fun i : Fin (n + 1) => first i.succ - last i.castSucc)]
      have tail := ih (fun i => first i.succ) (fun i => last i.succ)
      change FiniteSum.Fin.sumFin (fun i : Fin (n + 1) => first i.succ - last i.succ) -
        FiniteSum.Fin.sumFin (fun i : Fin n => first i.succ.succ - last i.castSucc.succ) =
        first (Fin.succ 0) - last (Fin.last (n + 1)) at tail
      have terms := FiniteSum.Fin.sumFin_congr (fun i : Fin n =>
        show first i.succ.succ - last i.succ.castSucc = first i.succ.succ - last i.castSucc.succ from rfl)
      rw [terms, show last (Fin.castSucc 0) = last 0 from rfl]
      calc
        _ = first 0 - first (Fin.succ 0) +
            (FiniteSum.Fin.sumFin (fun i : Fin (n + 1) => first i.succ - last i.succ) -
              FiniteSum.Fin.sumFin (fun i : Fin n => first i.succ.succ - last i.castSucc.succ)) := by ring1
        _ = _ := by rw [tail]; ring1

/-- Finite interval and internal-junction sums telescope to the retained outer difference, including the empty case. -/
private theorem telescope_all {n : Nat} (first last : Fin n → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun i => first i - last i) -
      FiniteSum.Fin.sumFin (fun i : Fin (n - 1) => first ⟨i.val + 1, by omega0⟩ - last ⟨i.val, by omega0⟩) =
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.endDifference first last := by
  cases n with
  | zero => change (0 : Gaussian.Basic.Canonical) - 0 = 0; ring1
  | succ n => exact Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.telescope first last

/-- For a nonempty bank, the retained outer difference is its actual first left and last right reading. -/
private theorem endDifference_nonempty {n : Nat} (first last : Fin n → Gaussian.Basic.Canonical) (positive : 0 < n) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.endDifference first last = first ⟨0, positive⟩ -
      last ⟨n - 1, by omega0⟩ := by
  cases n with
  | zero => exact (Nat.not_lt_zero 0 positive).elim
  | succ n => rfl

variable {genus count otherCount depth floor index : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {otherCover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonCover cover otherCover}
  {target : Normalization.InverseRootPolynomial.Coordinate} {request :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest regular common depth target floor}
  {evaluated : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest.Evaluation request index}

namespace FanBankRequest

/-- The two uncancelled outer radial potentials of the original common-cover interval bank. -/
@[expose] def OuterRadialBoundary (radialDepth : Nat) : Gaussian :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.endDifference (fun i =>
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.radialPotential evaluated radialDepth i 0)
    (fun i => Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.radialPotential evaluated radialDepth i
      (Fin.last (request.plans.get i).geometry.tail.length))

/-- For a nonempty common cover, the outer radial boundary is the original first and last radial potential difference.
-/
theorem outerRadialBoundary_eq (radialDepth : Nat) (nonempty : 0 < common.intervals.length) :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.OuterRadialBoundary (evaluated :=
      evaluated) radialDepth =
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.radialPotential evaluated radialDepth ⟨0,
        nonempty⟩ 0 -
        Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.radialPotential evaluated radialDepth
          ⟨common.intervals.length - 1, by omega0⟩
          (Fin.last (request.plans.get ⟨common.intervals.length - 1, by omega0⟩).geometry.tail.length) :=
  Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.endDifference_nonempty _ _ nonempty

/-- The actual polygon wedge connecting the last point of one chart to the first point of the next chart. -/
@[expose] def ConnectorArea (i : Fin (common.intervals.length - 1)) : Gaussian :=
  Topology.Polygon.Stokes.edgeArea
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.lastChartPoint evaluated
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.junctionLeft common i))
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections.Evaluation.firstChartPoint evaluated
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.junctionRight common i))

/-- The actual curved chart arcs and actual between-chart wedges, with
the uncancelled outer radial boundary retained explicitly. -/
@[expose] def JoinedBoundary (radialDepth : Nat) : Gaussian :=
  FiniteSum.Fin.sumFin (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest.ArcArea (evaluated :=
    evaluated) radialDepth) + FiniteSum.Fin.sumFin
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.ConnectorArea (evaluated := evaluated)) +
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.OuterRadialBoundary (evaluated :=
      evaluated) radialDepth

/-- Removing the original internal radial errors from the interval boundaries leaves the joined boundary with its outer
radial ends. -/
theorem joined_boundary (radialDepth : Nat) :
    FiniteSum.Fin.sumFin (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest.IntervalBoundary
      (evaluated := evaluated) radialDepth) -
      FiniteSum.Fin.sumFin (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.junctionRadialError
        evaluated radialDepth) =
        Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.JoinedBoundary (evaluated :=
        evaluated) radialDepth := by
  have telescoping := Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.telescope_all
    (fun i => Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.radialPotential evaluated radialDepth i 0)
    (fun i => Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.radialPotential evaluated radialDepth i
      (Fin.last (request.plans.get i).geometry.tail.length))
  change FiniteSum.Fin.sumFin (fun i => Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.radialPotential
    evaluated radialDepth i 0 -
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.radialPotential evaluated radialDepth i (Fin.last
        (request.plans.get i).geometry.tail.length)) -
    FiniteSum.Fin.sumFin (fun i => Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.radialPotential
      evaluated radialDepth (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.junctionRight common i) 0 -
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.radialPotential evaluated radialDepth
        (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.junctionLeft common i)
        (Fin.last (request.plans.get (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.junctionLeft common
          i)).geometry.tail.length)) =
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.OuterRadialBoundary (evaluated :=
      evaluated) radialDepth at telescoping
  rw [FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_sub] at telescoping
  unfold Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest.IntervalBoundary
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.junctionRadialError
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.JoinedBoundary
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.ConnectorArea
  rw [FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_sub]
  rw [← telescoping]
  ring1

variable {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- The retained radial junction data at every original common-cover interval transition. -/
@[expose] def Junctions (planned : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest evaluated
  requested minimum) :=
  Data.Vector.DependentVector (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.RadialJunction evaluated
    planned.fan.depth)

/-- The squared norm of the sum of the actual retained junction corrections fits the original chart target. -/
theorem junctions_bounded (planned : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest evaluated
  requested minimum)
    (junctions : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.Junctions planned) :
      Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun i => (junctions.get i).difference)) < target :=
      open Purelib.Data.Rat in by
  have allowance : request.allowance / 16 ≤ request.allowance :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (show (16 :
      Normalization.InverseRootPolynomial.Coordinate)⁻¹ ≤ 1 by decide +kernel)
      request.positive.le).trans_eq (mul_one _)
  have bound := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le (fun i => (junctions.get i).difference)
    request.allowance (fun i => ((junctions.get i).bounded.trans_le allowance).le)
  have squares := Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    (common.intervals.length - 1)))
    (Fraction.Cast.Order.natCast_le_direct (Nat.sub_le common.intervals.length 1)) 2
  have counted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct squares request.positive.le
  have paid : (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * request.allowance < target
    :=
    (by ring1 : (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * request.allowance =
      (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) * ((common.intervals.length :
        Normalization.InverseRootPolynomial.Coordinate) * request.allowance)).trans_lt request.paid
  exact bound.trans_lt (counted.trans_lt paid)

set_option genInjectivity false in
/-- The sampled fan bank after subtracting its actual retained radial-junction corrections.

The cached joined area retains its exact boundary identity, both outer radial ends and the original quantitative bound.
-/
structure Joined (planned : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest evaluated requested
  minimum) (bank : planned.Bank) where
  /-- The actual retained radial junctions between the original fan intervals. -/ junctions :
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.Junctions planned
  /-- The cached sum of the actual junction differences. -/ correction : Gaussian.Basic.Canonical
  /-- The cached correction is exactly the sum of the retained junction differences. -/ correction_eq : correction =
    FiniteSum.Fin.sumFin (fun i => (junctions.get i).difference)
  /-- The squared norm of the cached correction fits the original chart target. -/ correction_bounded :
    Data.Gaussian.Norm.Basic.normSq correction < target
  /-- The cached corrected area of the original sampled fan bank. -/ area : Gaussian.Basic.Canonical
  /-- The corrected area is the original bank area minus the cached correction. -/ area_eq : area = bank.area -
    correction
  /-- The squared norm of the joined area fits twice the sum of the original area and chart targets. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq area < 2 * (requested + target)
  /-- The cached area equals the joined boundary with its uncancelled outer radial ends. -/ boundary_eq : area =
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.JoinedBoundary (evaluated := evaluated)
    planned.fan.depth

constructive_injectivity Joined

/-- Consume the already sampled fan bank. The retained junction calculations
are summed once and reused both in the area and in its explanatory certificate. -/
@[expose] def Bank.join {planned : Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank.FanBankRequest evaluated
  requested minimum} (bank : planned.Bank)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
      Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.Joined planned bank := open
      Purelib.Data.Rat in by
  let junctions := Data.Vector.DependentVector.ofFn (fun i =>
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.radialJunction evaluated branch planned.fan.depth i)
  let correction := FiniteSum.Fin.sumFin (fun i => (junctions.get i).difference)
  have correctionBound :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.junctions_bounded planned junctions
  have correctionEq : correction = FiniteSum.Fin.sumFin
    (Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions.junctionRadialError evaluated planned.fan.depth) :=
    FiniteSum.Fin.sumFin_congr (fun i => by
      let joined := junctions.get i
      exact joined.difference_eq.trans
        (congrArg₂ (fun a b => a - b) (congrArg₂ (fun a b => a - b) joined.last_eq joined.first_eq)
          joined.connector_eq))
  have bound := (Gaussian.Norm.Bounds.normSq_sub_le_two bank.area correction).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide) (Fraction.Order.Arithmetic.add_lt_add_direct
      bank.bounded correctionBound))
  have boundary : bank.area - correction =
    Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.JoinedBoundary (evaluated := evaluated)
    planned.fan.depth := by
    rw [bank.boundary_eq, correctionEq]
    exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest.joined_boundary
      planned.fan.depth
  exact ⟨junctions, correction, rfl, correctionBound, bank.area - correction, rfl, bound, boundary⟩

end FanBankRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans
