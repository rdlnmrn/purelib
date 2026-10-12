module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Tactic.Ring

public section

/-! Requested open-boundary areas over the actual retained parent family.
All parents share the cap sample pair and one radial mesh. Their independently
selected source depths and uncancelled outer radial terms remain explicit. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries

open Purelib
open Purelib.Algebra
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts (ChartParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary (BoundaryRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation (ChartPreparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank (SampleBank ChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest (ConnectorArea
  OuterRadialBoundary)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily (CommonRibbonRequest)
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {target : Coordinate} {minimum : Nat}
  (original : Request regular other parents
    target minimum)

/-- The actual original parent's common-cover open-boundary request at the retained allowance. -/
@[expose] def BoundaryPlanAt (allowance : InverseRootPolynomial.Coordinate) (i : Fin original.plans.length) :=
  CommonRequestedBoundary.BoundaryRequest regular (PairedParentCharts.ChartParent original i).common allowance minimum

/-- The model stage required by this original parent's retained boundary plan. -/
@[expose] def boundaryIndexWeight {allowance : InverseRootPolynomial.Coordinate} (i : Fin original.plans.length)
    (plan : BoundaryPlanAt original allowance i) :
      Nat := plan.request.index

set_option genInjectivity false in
/-- One positive open-boundary request for the exact original parent family.

The cached block scale and parent-count allowances pay all retained parent boundaries before common cap samples or
radial fans are acquired. -/
structure BoundaryBankRequest (requested : InverseRootPolynomial.Coordinate) where
  /-- The cached complete block-comparison scale from the original parent count and source slope. -/ blockScale :
    InverseRootPolynomial.Coordinate
  /-- The block scale is the exact retained quadratic and quartic parent-count expression. -/ blockScale_eq : blockScale
    = 2 * ((original.plans.length : InverseRootPolynomial.Coordinate)^2 +
    16 * (original.plans.length : InverseRootPolynomial.Coordinate)^4 * (4 * (original.slope + 1)))
  /-- The cached common positive boundary allowance for every original parent. -/ allowance :
    InverseRootPolynomial.Coordinate
  /-- The common allowance is the minimum of the unit ceiling, parent-count budget and weighted block budget. -/
    allowance_eq : allowance = min 1 (min (Aggregate.perTerm requested original.plans.length)
    (Weighted.allowance (requested / 2) blockScale))
  /-- The actual retained common parent allowance is strictly positive. -/ positive : 0 < allowance
  /-- The retained common allowance is at most one. -/ small : allowance ≤ 1
  /-- The original cached block scale times the retained allowance is below the requested whole target. -/ block_paid :
    blockScale * allowance < requested
  /-- The original parent count squared times the retained allowance is below the requested whole target. -/ paid :
    (original.plans.length : InverseRootPolynomial.Coordinate) * ((original.plans.length :
    InverseRootPolynomial.Coordinate) * allowance) < requested
  /-- The dependent vector of actual boundary plans on the original parent family. -/ plans :
    Data.Vector.DependentVector (BoundaryPlanAt
    original allowance)
  /-- The cached common model stage paying the original family and every boundary plan. -/ index : Nat
  /-- The model stage is the exact maximum of the original request stage and retained plan stages. -/ index_eq : index =
    max original.index (plans.maximum
    (boundaryIndexWeight original))

constructive_injectivity BoundaryBankRequest

namespace BoundaryBankRequest
open Purelib.Data.Rat.Fraction.Compatibility

/-- Compute the original block and count budgets, prepare every retained parent boundary, and cache their common stage.
-/
@[expose] def build (requested : InverseRootPolynomial.Coordinate) (positive : 0 < requested) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries.BoundaryBankRequest original requested :=
  let blockScale : Coordinate := 2 * ((original.plans.length : InverseRootPolynomial.Coordinate)^2 +
    16 * (original.plans.length : InverseRootPolynomial.Coordinate)^4 * (4 * (original.slope + 1)))
  have nonnegative : 0 ≤ blockScale := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
      original.plans.length)) 4))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg original.slope_nonnegative (by decide)))))
  let allowance := min 1 (min (Aggregate.perTerm requested original.plans.length)
    (Weighted.allowance (requested / 2) blockScale))
  have halfPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2)
  have allowancePositive : 0 < allowance := Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Basic.lt_min (Aggregate.perTerm_positive positive original.plans.length)
      (Weighted.allowance_positive halfPositive nonnegative))
  have halfEq : requested / 2 + requested / 2 = requested :=
    (by ring1 : requested / 2 + requested / 2 = (requested / 2) * 2).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by
      decide))
  have blockPaid : blockScale * allowance < requested :=
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ((Fraction.Order.Basic.min_le_right _ _).trans
      (Fraction.Order.Basic.min_le_right _ _)) nonnegative).trans
      (Weighted.mul_allowance_le halfPositive.le nonnegative)).trans_lt
      ((Fraction.Field.zero_add _ ▸ Fraction.Order.Arithmetic.add_lt_add_right_direct halfPositive _).trans_eq halfEq)
  have paid : (original.plans.length : InverseRootPolynomial.Coordinate) * ((original.plans.length :
    InverseRootPolynomial.Coordinate) * allowance) < requested :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ((Fraction.Order.Basic.min_le_right _ _).trans
        (Fraction.Order.Basic.min_le_left _ _)) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))).trans_lt (Aggregate.count_mul_perTerm_lt positive
        original.plans.length)
  let plans := DependentVector.ofFn (fun i => BoundaryRequest.build regular (PairedParentCharts.ChartParent original
    i).common
    (ChartPreparation.build regular (PairedParentCharts.ChartParent original i).common)
    allowance allowancePositive minimum)
  ⟨blockScale, rfl, allowance, rfl, allowancePositive, Fraction.Order.Basic.min_le_left _ _, blockPaid, paid,
    plans, max original.index (plans.maximum
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries.boundaryIndexWeight original)), rfl⟩

variable {original} {requested : Coordinate} (request :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries.BoundaryBankRequest original requested)

/-- The common retained boundary stage also pays the original parent request. -/
theorem original_le : original.index ≤ request.index := (Data.Nat.Order.le_max_left _ _).trans_eq request.index_eq.symm

/-- The dependent bank of actual parent boundary evaluations at the retained common model stage. -/
@[expose] def Entries := Data.Vector.DependentVector (fun i => (request.plans.get i).request.Evaluation request.index)

/-- Evaluate every original common-cover parent using the same supplied cap pair and external reading floor. -/
@[expose] def evaluateEntries (externalFloor : Nat) (firstCap : Primitives.Sample cap differential request.index
  collar.box)
    (otherCap : Primitives.Sample cap other request.index collar.box) : request.Entries :=
  DependentVector.ofFn (fun i =>
    let parent := PairedParentCharts.ChartParent original i
    let samples := SampleBank.ofCapSamples
      (cover := parent.left) (otherCover := parent.right) firstCap otherCap
    (request.plans.get i).request.evaluate samples
      ((DependentVector.get_le_maximum
        (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries.boundaryIndexWeight original) request.plans
        i).trans
        ((Data.Nat.Order.le_max_right _ _).trans_eq request.index_eq.symm)) externalFloor)

/-- Every actual parent evaluation reuses the exact same two retained cap samples. -/
@[expose] def SharedCaps (entries : request.Entries)
    (firstCap : Primitives.Sample cap differential request.index collar.box)
    (otherCap : Primitives.Sample cap other request.index collar.box) : Prop :=
  ∀ i, (entries.get i).samples.firstCap = firstCap ∧ (entries.get i).samples.otherCap = otherCap

/-- Every acquired original parent evaluation retains the supplied cap pair exactly. -/
theorem shared (externalFloor : Nat) (firstCap : Primitives.Sample cap differential request.index collar.box)
    (otherCap : Primitives.Sample cap other request.index collar.box) :
    request.SharedCaps (request.evaluateEntries externalFloor firstCap otherCap) firstCap otherCap := by
  intro i
  dsimp only [evaluateEntries,
    -eq_self, -iff_self]
  rw [DependentVector.ofFn_get, ChartRequest.evaluate_samples]
  exact ⟨rfl, rfl⟩

/-- The actual boundary certificates dependent on the original retained parent evaluations. -/
@[expose] def Certificates (entries : request.Entries) :=
  Data.Vector.DependentVector (fun i => (request.plans.get i).Certificate (entries.get i))

/-- The actual radial fan plans on the original retained parent evaluations. -/
@[expose] def FanPlans (entries : request.Entries) :=
  Data.Vector.DependentVector (fun i => CommonChartFanBank.FanBankRequest (entries.get i) (request.plans.get
    i).allowance minimum)

/-- The radial depth selected by this retained original parent fan plan. -/
@[expose] def fanDepthWeight {entries : request.Entries} (i : Fin original.plans.length)
    (plan : CommonChartFanBank.FanBankRequest (entries.get i) (request.plans.get i).allowance minimum) : Nat :=
      plan.fan.depth

/-- Every original retained parent certificate uses the supplied exact common radial depth. -/
@[expose] def CommonRadialDepth (entries : request.Entries) (certificates : request.Certificates entries)
    (depth : Nat) : Prop := ∀ i, (certificates.get i).fanRequest.fan.depth = depth

/-- Every original retained parent evaluation keeps the same supplied external reading floor. -/
@[expose] def ReadingFloors (entries : request.Entries) (externalFloor : Nat) : Prop :=
  ∀ i, (entries.get i).externalFloor = externalFloor

/-- The complete original connector and outer radial boundary sum over all retained parents. -/
@[expose] def OpenEnds (entries : request.Entries) (certificates : request.Certificates entries) : Gaussian :=
  FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (FanBankRequest.ConnectorArea (evaluated := entries.get i)) +
    FanBankRequest.OuterRadialBoundary (evaluated := entries.get i) (certificates.get i).fanRequest.fan.depth)

set_option genInjectivity false in
/-- The acquired original parent boundary family with shared caps and a common radial mesh.

Cached source, correction and open-end sums retain their exact decomposition, with no assumption that different parents
close their roots. -/
structure Evaluation where
  /-- The first original cap sample shared by every retained parent. -/ firstCap : Primitives.Sample cap differential
    request.index collar.box
  /-- The second original cap sample shared by every retained parent. -/ otherCap : Primitives.Sample cap other
    request.index collar.box
  /-- The actual parent evaluations on the retained common model stage. -/ entries : request.Entries
  /-- Every actual retained parent evaluation reuses the two exact cached original cap samples. -/ shared :
    request.SharedCaps entries firstCap otherCap
  /-- The retained external root-reading stage floor. -/ externalFloor : Nat
  /-- Every original evaluation retains that same external reading floor. -/ readingFloors : request.ReadingFloors
    entries externalFloor
  /-- The actual retained open-boundary certificate for each original parent. -/ certificates : request.Certificates
    entries
  /-- The cached common radial depth of every original parent certificate. -/ radialDepth : Nat
  /-- All actual parent certificates use exactly the retained common radial depth. -/ commonDepth :
    request.CommonRadialDepth entries certificates radialDepth
  /-- The cached sum of all original certified open-boundary areas. -/ area : InverseRootPolynomial.Gaussian
  /-- The area cache is exactly the finite sum of the retained original certificate areas. -/ area_eq : area =
    FiniteSum.Fin.sumFin (fun i => (certificates.get i).area)
  /-- The complete actual open-boundary area satisfies the original whole target. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq area < requested
  /-- The cached total of the original parent source areas. -/ sourceArea : InverseRootPolynomial.Gaussian
  /-- The source-area cache is exactly the sum of the retained parent source areas. -/ sourceArea_eq : sourceArea =
    FiniteSum.Fin.sumFin (fun i => (entries.get i).sourceArea)
  /-- The cached total of the original parent restoration corrections. -/ correction : InverseRootPolynomial.Gaussian
  /-- The correction cache is exactly the sum of the retained original restoration terms. -/ correction_eq : correction
    = FiniteSum.Fin.sumFin (fun i => (entries.get i).correction)
  /-- The cached complete original connector and radial-end correction. -/ openEnds : InverseRootPolynomial.Gaussian
  /-- The open-end cache equals the actual original connector and radial boundary sum. -/ openEnds_eq : openEnds =
    request.OpenEnds entries certificates
  /-- The certified area is the original source area minus restoration correction plus all retained open ends. -/
    decomposition : area = sourceArea - correction + openEnds

constructive_injectivity Evaluation

/-- Sampling is shared across the family; every subsequent total reads the retained parent certificates. No cross-parent
root closure is assumed. -/
@[expose] def acquire (externalFloor : Nat) (branch : HyperellipticReciprocal.originOrder curve = 1) :
  request.Evaluation := by
  let firstCap := Primitives.Sample.build cap differential request.index collar.box
  let otherCap := Primitives.Sample.build cap other request.index collar.box
  let entries := request.evaluateEntries externalFloor firstCap otherCap
  have readingFloors : request.ReadingFloors entries externalFloor := by
    intro i
    dsimp only [entries,
      evaluateEntries, -eq_self,
      -iff_self]
    rw [DependentVector.ofFn_get]
    rfl
  let fanPlans : request.FanPlans entries := DependentVector.ofFn (fun i =>
    FanBankRequest.build
      (entries.get i) (request.plans.get i).allowance (request.plans.get i).positive minimum)
  let radialDepth := fanPlans.maximum
    (fanDepthWeight request)
  let certificates := DependentVector.ofFn (fun i => (request.plans.get i).certify (entries.get i)
    ((fanPlans.get i).atDepth radialDepth (DependentVector.get_le_maximum
      (fanDepthWeight request)
      fanPlans i)) branch)
  have commonDepth : request.CommonRadialDepth entries certificates radialDepth := by
    intro i
    dsimp only [certificates, -eq_self, -iff_self]
    rw [DependentVector.ofFn_get]
    rfl
  let area := FiniteSum.Fin.sumFin (fun i => (certificates.get i).area)
  let sourceArea := FiniteSum.Fin.sumFin (fun i => (entries.get i).sourceArea)
  let correction := FiniteSum.Fin.sumFin (fun i => (entries.get i).correction)
  let openEnds := area - sourceArea + correction
  have estimate := Indexed.normSq_sumFin_le (fun i => (certificates.get i).area)
    request.allowance (fun i => (certificates.get i).accurate.le)
  have paid : (original.plans.length : InverseRootPolynomial.Coordinate)^2 * request.allowance < requested :=
    (by ring1 : (original.plans.length : InverseRootPolynomial.Coordinate)^2 * request.allowance =
      (original.plans.length : InverseRootPolynomial.Coordinate) * ((original.plans.length :
        InverseRootPolynomial.Coordinate) * request.allowance)).trans_lt request.paid
  have boundary : openEnds = request.OpenEnds entries certificates := by
    have each := FiniteSum.Fin.sumFin_congr (fun i => (certificates.get i).area_eq)
    change FiniteSum.Fin.sumFin (fun i => (certificates.get i).area) - sourceArea + correction = _
    rw [each]
    unfold Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartArcComparison.sourceOpenBoundary
      OpenEnds
    rw [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_add]
    dsimp only [sourceArea, correction, -eq_self, -iff_self]
    ring1
  exact ⟨firstCap, otherCap, entries, request.shared externalFloor firstCap otherCap, externalFloor, readingFloors,
    certificates, radialDepth, commonDepth, area, rfl,
    estimate.trans_lt paid, sourceArea, rfl, correction, rfl, openEnds, boundary, by
      dsimp only [openEnds, -eq_self, -iff_self];
      ring1⟩

/-- The original source area with its full retained correction and open ends satisfies the requested target. -/
theorem Evaluation.corrected_bounded (evaluated : request.Evaluation) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.sourceArea - evaluated.correction + evaluated.openEnds) <
      requested :=
  evaluated.decomposition ▸ evaluated.bounded

/-- The actual retained open boundary uses a single mesh across parents, including when their source charts chose
different depths. -/
theorem Evaluation.openEnds_common (evaluated : request.Evaluation) :
    evaluated.openEnds = FiniteSum.Fin.sumFin (fun i =>
      FiniteSum.Fin.sumFin (FanBankRequest.ConnectorArea (evaluated := evaluated.entries.get i)) +
        FanBankRequest.OuterRadialBoundary (evaluated := evaluated.entries.get i) evaluated.radialDepth) := by
  rw [evaluated.openEnds_eq]
  exact FiniteSum.Fin.sumFin_congr (fun i => congrArg
    (fun depth => FiniteSum.Fin.sumFin (FanBankRequest.ConnectorArea (evaluated := evaluated.entries.get i)) +
      FanBankRequest.OuterRadialBoundary (evaluated := evaluated.entries.get i) depth) (evaluated.commonDepth i))

/-- Each actual retained parent source area is its original complete dyadic bilinear area at the retained combined
depth. -/
theorem Evaluation.source_readback (evaluated : request.Evaluation) (i : Fin original.plans.length) :
    (evaluated.entries.get i).sourceArea = DyadicBilinearBoundaryRibbon.dyadicArea
      (CommonRibbonRequest.sourceValues (evaluated.entries.get i).samples.source (evaluated.entries.get
        i).samples.otherSource)
      ((PairedParentCharts.ChartParent original i).common.depth + (request.plans.get i).depth) 0 1 :=
  (evaluated.entries.get i).sourceArea_full

end BoundaryBankRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries
