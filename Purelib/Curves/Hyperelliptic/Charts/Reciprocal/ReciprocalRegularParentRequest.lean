module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Membership
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
public import Purelib.Integration.Path.Dyadic.DyadicSteps
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTotal
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentArea
import Init.Data.List.OfFn
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Tactic.Ring
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentReadings

public section

/-! Requested regular exterior chart bounds on the existing common-depth
parent bank, with one retained pair of cap samples. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Budget
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentArea
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTotal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Geometry.Path.Gaussian
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Riemann.Topology
open Purelib.Topology.Polygon

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)
open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap (EnergyBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts (ChartBankRequest ChartParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans (RegularFanRequest)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {target : Coordinate} {minimum : Nat}
  {original : Request regular other parents
    target minimum}
/-- A positive aggregate target bounds its finite-count per-term allowance. -/
theorem perTerm_le {target : InverseRootPolynomial.Coordinate} (positive : 0 < target) (count : Nat) :
    Aggregate.perTerm target count ≤ target := by
  have n : (0 : InverseRootPolynomial.Coordinate) ≤ count := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)
  have extra : (0 : InverseRootPolynomial.Coordinate) ≤ 2 * (count : InverseRootPolynomial.Coordinate)^2 + 4 * count + 1
    :=
    add_nonneg (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) n)) (by decide +kernel)
  have lower : (1 : InverseRootPolynomial.Coordinate) ≤ 2 * ((count : InverseRootPolynomial.Coordinate) + 1)^2 :=
    (le_add_of_nonneg_right extra).trans_eq (by ring1)
  rw [Aggregate.perTerm, Aggregate.countCoordinate_eq]
  apply (Fraction.Order.Field.div_le_iff_pos ((by decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 1).trans_le
    lower)).mpr
  exact (show target = target * 1 by ring1).le.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lower positive.le)

/-- One quarter of a positive rational is at most that rational. -/
theorem quarter_le {value : InverseRootPolynomial.Coordinate} (positive : 0 < value) : value / 4 ≤ value := by
  apply (Fraction.Order.Field.div_le_iff_pos (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 4)).mpr
  exact (show value = value * 1 by ring1).le.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide +kernel) positive.le)

/-- The minimum of a finite rational list and one. -/
@[expose] def positiveMinimum : List InverseRootPolynomial.Coordinate → InverseRootPolynomial.Coordinate
  | [] => 1
  | first :: rest => min first
    (positiveMinimum rest)

/-- The unit-capped minimum of a finite positive list is strictly positive. -/
theorem positiveMinimum_positive (values : List InverseRootPolynomial.Coordinate)
    (positive : ∀ value ∈ values, 0 < value) : 0 <
      positiveMinimum values := by
  induction values with
  | nil => exact (by decide : (0 : InverseRootPolynomial.Coordinate) < 1)
  | cons first rest ih =>
      exact Fraction.Order.Basic.lt_min (positive first List.mem_cons_self)
        (ih (fun value member => positive value (List.mem_cons_of_mem _ member)))

/-- The unit-capped finite minimum is at most each retained list member. -/
theorem positiveMinimum_le (values : List InverseRootPolynomial.Coordinate) (value : InverseRootPolynomial.Coordinate)
    (member : value ∈ values) : positiveMinimum
      values ≤ value := by
  induction values with
  | nil => exact (List.not_mem_nil member).elim
  | cons first rest ih =>
      rcases Data.List.Membership.mem_cons.mp member with equal | member
      · exact equal ▸ Fraction.Order.Basic.min_le_left first
          (positiveMinimum rest)
      · exact (Fraction.Order.Basic.min_le_right _ _).trans (ih member)

set_option genInjectivity false in
/-- The existing parent bank with all regular interval budgets paid. The shared depth and sample index remain those of
`ChartBankRequest`. -/
structure RegularParentRequest (original : PairedParentRequest.Request regular other parents target minimum) (error :
  InverseRootPolynomial.Coordinate) where
  /-- The selected common geometric refinement depth. -/ depth : Nat
  /-- The retained numerical chart target. -/ requested : InverseRootPolynomial.Coordinate
  /-- The numerical chart target is strictly positive. -/ positive : 0 < requested
  /-- The chart target fits the aggregate requested error. -/ requested_le : requested ≤ error
  /-- The actual chart bank at the retained common depth and numerical target. -/ request :
    PairedParentCharts.ChartBankRequest original depth requested
  /-- The complete source-to-chart area scale fits the aggregate error at the actual chart allowance. -/
    source_area_paid : ReciprocalRegularParentArea.sourceParentAreaScale original * request.allowance ≤ error
  /-- The independently retained source resampling allowance. -/ referenceError : InverseRootPolynomial.Coordinate
  /-- The source resampling allowance is strictly positive. -/ reference_positive : 0 < referenceError
  /-- The squared parent-count aggregate of the resampling allowance is below the requested error. -/ reference_paid :
    (original.plans.length : InverseRootPolynomial.Coordinate)^2 * referenceError < error
  /-- The actual common source depth pays the retained resampling rate. -/ reference_depth_paid :
    Geometric.Basic.quarterRadius (16 * original.slope^2) (original.depth + depth) < referenceError
  /-- Every retained parent interval's chart-versus-arc budget fits its nested aggregate share. -/ interval_paid : ∀ (p
    : Fin original.plans.length)
      (i : Fin (PairedParentCharts.ChartParent original p).common.intervals.length),
    ReciprocalRegularChartFans.chartArcBudget
      ((request.plans.get p).plans.get i) <
      Aggregate.perTerm (Aggregate.perTerm error original.plans.length)
        (PairedParentCharts.ChartParent original p).common.intervals.length

constructive_injectivity RegularParentRequest

namespace RegularParentRequest

/-- The nested parent-and-interval share of the aggregate error. -/
@[expose] def intervalShare (original : PairedParentRequest.Request regular other parents target minimum) (error :
  InverseRootPolynomial.Coordinate)
    (p : Fin original.plans.length) : Coordinate :=
  Aggregate.perTerm (Aggregate.perTerm error original.plans.length)
    (PairedParentCharts.ChartParent original p).common.intervals.length

/-- The retained parent's arc scale from its displacement and regular inverse bound. -/
@[expose] def arcScale (original : PairedParentRequest.Request regular other parents target minimum) (p : Fin
  original.plans.length) : Coordinate :=
  16 * regular.inverseUpper^2 * (Data.Gaussian.Norm.Basic.normSq (PairedParentCharts.ChartParent original
    p).parent.model.displacement)^2

/-- The retained parent arc scale is nonnegative. -/
theorem arcScale_nonnegative (original : PairedParentRequest.Request regular other parents target minimum)
    (p : Fin original.plans.length) : 0 ≤
      arcScale original p :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- Select a common geometric refinement before choosing the numerical request. Both finite parent and interval counts
are paid explicitly. -/
@[expose] def build (original : PairedParentRequest.Request regular other parents target minimum)
    (error : InverseRootPolynomial.Coordinate) (positive : 0 < error) :
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.RegularParentRequest original error := by
  have sharePositive (p : Fin original.plans.length) : 0 <
    intervalShare original
    error p :=
    Aggregate.perTerm_positive (Aggregate.perTerm_positive positive _) _
  let depths : Data.Vector.DependentVector (fun _ : Fin original.plans.length => Nat) := DependentVector.ofFn
    (fun p => Search.firstQuarterBelow
      (arcScale original p)
      minimum
      (intervalShare original
        error p / 4))
  let referenceError := Aggregate.perTerm error original.plans.length
  have referencePositive : 0 < referenceError := Aggregate.perTerm_positive positive _
  let referenceDepth := Search.firstQuarterBelow (16 * original.slope^2) minimum referenceError
  let depth := max (depths.maximum (fun _ value => value)) referenceDepth
  have referencePaid : (original.plans.length : InverseRootPolynomial.Coordinate)^2 * referenceError < error :=
    (by ring1 : (original.plans.length : InverseRootPolynomial.Coordinate)^2 * referenceError =
      (original.plans.length : InverseRootPolynomial.Coordinate) * ((original.plans.length :
        InverseRootPolynomial.Coordinate) * referenceError)).trans_lt
        (Aggregate.count_mul_perTerm_lt positive _)
  have referenceScaleNonnegative : 0 ≤ 16 * original.slope^2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have referenceDepthPaid : Geometric.Basic.quarterRadius (16 * original.slope^2) (original.depth + depth) <
    referenceError :=
    (quarterRadius_antitone referenceScaleNonnegative
      ((Data.Nat.Order.le_max_right _ _).trans (Nat.le_add_left _ _))).trans_lt
        (Search.firstQuarterBelow_accurate _ referenceScaleNonnegative minimum _ referencePositive)
  let rate := fun p : Fin original.plans.length =>
    ((((2^(original.localDepth (PairedParentCharts.ChartParent original p) depth) : Nat) :
      InverseRootPolynomial.Coordinate)^2)) *
      (264 * regular.factorUpper^2)
  have rateNonnegative (p) : 0 ≤ rate p := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  let tolerances := fun p => Weighted.allowance
    (intervalShare original
    error p / 4) (rate p)
  have tolerancePositive (p) : 0 < tolerances p := Weighted.allowance_positive
    (Fraction.Order.Field.div_pos_direct (sharePositive p) (by decide)) (rateNonnegative p)
  let areaTolerance := Weighted.allowance error (ReciprocalRegularParentArea.sourceParentAreaScale original)
  have areaPositive : 0 < areaTolerance := Weighted.allowance_positive positive
    (ReciprocalRegularParentArea.sourceParentAreaScale_nonnegative original)
  let requested := min error (min (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.positiveMinimum
    (List.ofFn tolerances)) areaTolerance)
  have requestedPositive : 0 < requested := Fraction.Order.Basic.lt_min positive (Fraction.Order.Basic.lt_min
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.positiveMinimum_positive _ (by
    intro value member
    obtain ⟨p, equal⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    exact equal ▸ tolerancePositive p)) areaPositive)
  have requestedLe (p) : requested ≤ tolerances p := (Fraction.Order.Basic.min_le_right _ _).trans
    ((Fraction.Order.Basic.min_le_left _ _).trans
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.positiveMinimum_le _ _
      (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨p, rfl⟩)))
  let request := ChartBankRequest.build original depth requested requestedPositive
  have bankAllowance : request.allowance ≤ requested := by
    rw [request.allowance_eq, request.joinBudget.allowance_eq]
    exact (Fraction.Order.Basic.min_le_left _ _).trans
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.perTerm_le requestedPositive _)
  have areaPaid : ReciprocalRegularParentArea.sourceParentAreaScale original * request.allowance ≤ error :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (bankAllowance.trans ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)))
      (ReciprocalRegularParentArea.sourceParentAreaScale_nonnegative original)).trans
        (Weighted.mul_allowance_le positive.le
          (ReciprocalRegularParentArea.sourceParentAreaScale_nonnegative original))
  refine ⟨depth, requested, requestedPositive, Fraction.Order.Basic.min_le_left _ _, request, areaPaid,
    referenceError, referencePositive, referencePaid, referenceDepthPaid, ?_⟩
  intro p i
  let parentRequest := request.plans.get p
  let plan := parentRequest.plans.get i
  have parentAllowance : parentRequest.allowance ≤ request.allowance := by
    rw [parentRequest.allowance_eq, parentRequest.joinBudget.allowance_eq]
    exact (Fraction.Order.Basic.min_le_left _ _).trans
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.perTerm_le request.positive _)
  have toleranceLe : plan.budget.tolerance / 4 / 4 ≤ tolerances p :=
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.quarter_le
      (Fraction.Order.Field.div_pos_direct plan.budget.positive (by decide))).trans
      ((Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.quarter_le plan.budget.positive).trans
        (plan.budget.bounded.trans (parentAllowance.trans (bankAllowance.trans (requestedLe p)))))
  have edges : plan.geometry.tail.length = 2^(original.localDepth (PairedParentCharts.ChartParent original p) depth) :=
    by
    rw [plan.geometry.tail_eq, DyadicSteps.tail_length]
  have sheet : (plan.geometry.tail.length : InverseRootPolynomial.Coordinate)^2 *
      (264 * regular.factorUpper^2 * (plan.budget.tolerance / 4 / 4)) ≤
        intervalShare
        original error p / 4 := by
    have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct toleranceLe (rateNonnegative p)).trans
      (Weighted.mul_allowance_le (Fraction.Order.Field.div_pos_direct (sharePositive p) (by decide)).le (rateNonnegative
        p))
    exact (show (plan.geometry.tail.length : InverseRootPolynomial.Coordinate)^2 *
      (264 * regular.factorUpper^2 * (plan.budget.tolerance / 4 / 4)) =
      rate p * (plan.budget.tolerance / 4 / 4) by rw [edges]; dsimp only [rate, -eq_self, -iff_self]; ring1).trans_le
        paid
  have depthLe : Search.firstQuarterBelow
    (arcScale original p)
    minimum
      (intervalShare original
        error p / 4) ≤ original.localDepth (PairedParentCharts.ChartParent original p) depth := by
    have selected := DependentVector.get_le_maximum (fun _ value => value) depths p
    dsimp only [depths, -eq_self, -iff_self] at selected
    rw [DependentVector.ofFn_get] at selected
    exact selected.trans ((Data.Nat.Order.le_max_left _ _).trans (Nat.le_add_left _ _))
  have arcs : SourceChartRequest.regularArcError regular plan.geometry <
      intervalShare original
        error p / 4 :=
    (SourceChartRequest.regularArcError_geometric regular plan.geometry).trans_lt
      ((quarterRadius_antitone
        (arcScale_nonnegative
        original p) depthLe).trans_lt
        (Search.firstQuarterBelow_accurate _
          (arcScale_nonnegative
          original p) minimum _
          (Fraction.Order.Field.div_pos_direct (sharePositive p) (by decide))))
  have total := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2)
    ((Fraction.Order.Arithmetic.add_lt_add_left_direct arcs _).trans_le
      (Fraction.Order.Arithmetic.add_le_add_direct sheet (le_refl
        (intervalShare
        original error p / 4))))
  exact total.trans_eq (by
    calc
      2 * (intervalShare
        original error p / 4 +
        intervalShare
        original error p / 4) =
        intervalShare
          original error p / 4 * 4 := by ring1
      _ = intervalShare
        original error p := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

/-- The actual common source depth pays each parent's resampling rate. The cached reference allowance can be aggregated
independently of the smaller numerical chart tolerance. -/
theorem source_reference_rate {error : InverseRootPolynomial.Coordinate} (selected :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.RegularParentRequest original error)
    (i : Fin original.plans.length) :
    16 * (max (PairedParentCharts.ChartParent original i).data.sourceSlope (PairedParentCharts.ChartParent original
      i).otherData.sourceSlope)^2 *
      ((1 / 2 : InverseRootPolynomial.Coordinate)^(original.depth + selected.depth))^2 < selected.referenceError := by
  let density := max (PairedParentCharts.ChartParent original i).data.sourceSlope (PairedParentCharts.ChartParent
    original i).otherData.sourceSlope
  have nonnegative : 0 ≤ density :=
    (PairedParentCharts.ChartParent original i).data.sourceSlope_nonnegative.trans (Fraction.Order.Basic.le_max_left _
      _)
  have bounds := PairedParentRequest.Request.plan_bounds original (PairedParentCharts.ChartParent original i)
    (List.getElem_mem i.isLt)
  have smaller := Fraction.Order.Arithmetic.pow_le_pow_direct nonnegative (Fraction.Order.Basic.max_le bounds.1
    bounds.2) 2
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct smaller (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16)
  have rate : 16 * density^2 * ((1 / 2 : InverseRootPolynomial.Coordinate)^(original.depth + selected.depth))^2 =
      16 * density^2 * (1 / 4 : InverseRootPolynomial.Coordinate)^(original.depth + selected.depth) := by
    rw [← pow_mul, Nat.mul_comm (original.depth + selected.depth) 2, pow_mul,
      show (1 / 2 : InverseRootPolynomial.Coordinate)^2 = 1 / 4 by decide]
  have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scaled
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1 / 4)
      (original.depth + selected.depth))
  exact rate.trans_le upper |>.trans_lt
    ((Geometric.Basic.quarterRadius_eq_mul_pow _ _).symm.trans_lt selected.reference_depth_paid)

/-- The chart-versus-arc budget is automatic on the shared parent bank. -/
theorem chart_arc_accurate {error : InverseRootPolynomial.Coordinate} (selected :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.RegularParentRequest original error)
    (positive : 0 < error) (evaluated : selected.request.Evaluation)
    {fanError : InverseRootPolynomial.Coordinate} {fanFloor : Nat} (fan : ReciprocalRegularParentFans.RegularFanRequest
      evaluated fanError fanFloor)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.chartArea - RegularFanRequest.arcArea fan) < error :=
  ReciprocalRegularParentFans.chartArea_arcArea_total_of_intervals evaluated fan error positive unramified
    (fun p i => (selected.interval_paid p i).le)

/-- Close the actual regular parent chain. The source correction remains explicit and the source and chart estimates use
the same cap samples. -/
theorem source_closed_bound {error : InverseRootPolynomial.Coordinate} (selected :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.RegularParentRequest original error)
    (positive : 0 < error) (evaluated : selected.request.Evaluation)
    {fanFloor : Nat} {fan : ReciprocalRegularParentFans.RegularFanRequest evaluated error fanFloor} (certified :
      RegularFanRequest.Certificate fan)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    (closed : start.coordinate = finish.coordinate) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.sourceArea - evaluated.correction) ≤ 10 * error := by
  have bounded := certified.sourceClosedBoundary_bound
    (selected.chart_arc_accurate positive evaluated fan unramified).le chain closed
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct selected.requested_le (le_refl (2 * (error + error))))
    (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
  exact bounded.trans (paid.trans_eq (by ring1))

/-- The full closed chart trace, including its actual closing edge, is small on the same shared bank. Owner joins supply
the connector identities. -/
theorem closed_chart_bound {error : InverseRootPolynomial.Coordinate} (selected :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.RegularParentRequest original error)
    (positive : 0 < error) (evaluated : selected.request.Evaluation)
    {fanFloor : Nat} {fan : ReciprocalRegularParentFans.RegularFanRequest evaluated error fanFloor} (certified :
      RegularFanRequest.Certificate fan)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (present : 0 < original.plans.length)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain parents first last)
    (closed : start.coordinate = finish.coordinate)
    (returned : Gaussian.Equivalence.NamedEquivalent last first) :
    Data.Gaussian.Norm.Basic.normSq ((Evaluation.regularTrace evaluated).area id +
      Stokes.edgeArea (Evaluation.regularTrace evaluated).last (Evaluation.regularTrace evaluated).first) < 4 * error :=
        by
  rw [Evaluation.regularTrace_closed_area evaluated unramified present chain roots closed returned]
  have chart := selected.chart_arc_accurate positive evaluated fan unramified
  have arcs := certified.closed_bounded chain closed
  have bounded := (Data.Gaussian.Norm.Bounds.normSq_add_le_two
      (evaluated.chartArea - RegularFanRequest.arcArea fan) (RegularFanRequest.arcArea fan)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct chart arcs))
  rw [sub_add_cancel] at bounded
  exact bounded.trans_eq (by ring1)

/-- Bound the full raw source area, including the polygon of parent totals. The connector readings and regular fans use
the original numerical bank. -/
theorem source_area_bound {error : InverseRootPolynomial.Coordinate} (selected :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.RegularParentRequest original error)
    (positive : 0 < error) (small : error ≤ 1) (evaluated : selected.request.Evaluation)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain parents first last)
    (closed : start.coordinate = finish.coordinate)
    (returned : Gaussian.Equivalence.NamedEquivalent last first) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area evaluated.sourcePaths.flatten) ≤ 16 * error := by
  rcases Nat.eq_zero_or_pos original.plans.length with empty | present
  · have pathsEmpty : evaluated.sourcePaths = [] := List.eq_nil_of_length_eq_zero (by
      rw [Evaluation.sourcePaths, Data.List.OfFn.Basic.length_ofFn, empty])
    rw [pathsEmpty]
    change Data.Gaussian.Norm.Basic.normSq 0 ≤ 16 * error
    exact Data.Gaussian.Norm.Basic.normSq_zero.trans_le
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) positive.le)
  · have allowance : selected.request.allowance ≤ 1 := by
      rw [selected.request.allowance_eq, selected.request.joinBudget.allowance_eq]
      exact (Fraction.Order.Basic.min_le_left _ _).trans
        ((Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.perTerm_le selected.positive _).trans
        (selected.requested_le.trans small))
    obtain ⟨retained, _, compared⟩ := Evaluation.regular_source_area_comparison evaluated allowance present
      chain roots closed returned unramified error positive
    let fan := RegularFanRequest.build retained error positive minimum
    have chart := selected.closed_chart_bound positive retained fan.acquire unramified present chain roots closed
      returned
    rw [Evaluation.regularTrace_closed_area retained unramified present chain roots closed returned] at chart
    have difference : Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area evaluated.sourcePaths.flatten -
      retained.chartArea) ≤ 4 * error :=
      compared.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct selected.source_area_paid le_rfl) (by
            decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq (by ring1))
    have bounded := Data.Gaussian.Norm.Bounds.normSq_add_le_two
      (PairedIncrementArea.area evaluated.sourcePaths.flatten - retained.chartArea) retained.chartArea
    rw [sub_add_cancel] at bounded
    exact bounded.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct difference chart.le)
      (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq (by ring1))

/-- From a positive request, acquire the shared regular parent bank and its fans and bound its corrected closed source
area below that request. -/
theorem source_closed_requested (original : PairedParentRequest.Request regular other parents target minimum)
    (error : InverseRootPolynomial.Coordinate) (positive : 0 < error)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    (closed : start.coordinate = finish.coordinate) :
    let share := min (error / 64) 1
    let sharePositive := Fraction.Order.Basic.lt_min (Fraction.Order.Field.div_pos_direct positive (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 64)) (by decide +kernel)
    let selected := build
      original share sharePositive
    let evaluated := selected.request.acquire
    Data.Gaussian.Norm.Basic.normSq (evaluated.sourceArea - evaluated.correction) < error := by
  intro share sharePositive selected evaluated
  let fan := RegularFanRequest.build evaluated share sharePositive minimum
  have bounded := selected.source_closed_bound sharePositive evaluated fan.acquire unramified chain closed
  have paid := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct (by
      decide +kernel : (10 : InverseRootPolynomial.Coordinate) < 64)
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 64))
  exact bounded.trans_lt (((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_left
    _ _) (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 10)).trans_lt paid).trans_eq (by
    change 64 * (error / 64) = error
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)))

/-- The same selected bank also pays the raw source-total request. Its root chain supplies all joins; no chart-reading
floor is left to the caller. -/
theorem source_total_requested (original : PairedParentRequest.Request regular other parents target minimum)
    (error : InverseRootPolynomial.Coordinate) (positive : 0 < error)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain parents first last)
    (closed : start.coordinate = finish.coordinate)
    (returned : Gaussian.Equivalence.NamedEquivalent last first) :
    let share := min (error / 64) 1
    let sharePositive := Fraction.Order.Basic.lt_min (Fraction.Order.Field.div_pos_direct positive (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 64)) (by decide +kernel)
    let selected := build
      original share sharePositive
    let evaluated := selected.request.acquire
    PrimitivePoint.Bounded (PairedIncrementArea.total evaluated.sourcePaths.flatten) error := by
  intro share sharePositive selected evaluated
  have bounded := Evaluation.regular_source_total_bound evaluated
    (selected.requested_le.trans (Fraction.Order.Basic.min_le_right _ _)) chain roots closed returned unramified
  have requestedLe := selected.requested_le.trans (Fraction.Order.Basic.min_le_left _ _)
  have paid : 33 * selected.requested ≤ error := by
    calc
      _ ≤ 33 * (error / 64) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct requestedLe
        (by decide +kernel)
      _ ≤ 64 * (error / 64) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
        (Fraction.Order.Field.div_pos_direct positive (by
            decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 64)).le
      _ = error := by rw [Fraction.Field.mul_comm]; exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)
  exact ⟨bounded.1.trans paid, bounded.2.trans paid⟩

/-- The shared regular bank pays the full raw source-area request, alongside the corrected area and total bounds above.
-/
theorem source_area_requested (original : PairedParentRequest.Request regular other parents target minimum)
    (error : InverseRootPolynomial.Coordinate) (positive : 0 < error)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain parents first last)
    (closed : start.coordinate = finish.coordinate)
    (returned : Gaussian.Equivalence.NamedEquivalent last first) :
    let share := min (error / 64) 1
    let sharePositive := Fraction.Order.Basic.lt_min (Fraction.Order.Field.div_pos_direct positive (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 64)) (by decide)
    let selected := build
      original share sharePositive
    let evaluated := selected.request.acquire
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area evaluated.sourcePaths.flatten) < error := by
  intro share sharePositive selected evaluated
  have bounded := selected.source_area_bound sharePositive (Fraction.Order.Basic.min_le_right _ _) evaluated unramified
    chain roots closed returned
  have paid := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct (by
      decide +kernel : (16 : InverseRootPolynomial.Coordinate) < 64)
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 64))
  exact bounded.trans_lt (((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_left
    _ _)
    (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16)).trans_lt paid).trans_eq (by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)))

end RegularParentRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest
