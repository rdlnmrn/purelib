module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedPairedRadialRibbon
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints
import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
import Init.Data.Fin.Basic
import Init.Data.List.Lemmas
import Init.Data.Nat.Basic
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Cross-parent radial cancellation consumes the retained source chain.
Physical endpoint equality alone is not used to close a root sheet. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure

open Purelib
open Purelib.Algebra
open Purelib.Approximation
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Geometry.Path.Gaussian
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Riemann.RootContinuation.RootRadialGeometry
open Purelib.Riemann.Topology
open Purelib.Topology.Polygon
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request Plan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries (BoundaryBankRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts (ChartParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints.BoundaryBankRequest (EndpointJoin
  JunctionRequest endpointJoin)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub sumFin_add)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.RootContinuation
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}

/-- Physical endpoint agreement between two adjacent original parents at the supplied retained list bound. -/
@[expose] def PhysicalAt (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)) (k : Nat) (h :
  k + 1 < parents.length) : Prop :=
  (parents[k]'((Nat.lt_succ_self k).trans h)).edge.point 1 = (parents[k + 1]'h).edge.point 0

/-- Named root equivalence between the adjacent original parent endpoints at the supplied retained list bound. -/
@[expose] def RootAt (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)) (k : Nat) (h : k +
  1 < parents.length) :=
  Gaussian.Equivalence.NamedEquivalent ((parents[k]'((Nat.lt_succ_self k).trans h)).edge.rootName 1 (by decide))
    ((parents[k + 1]'h).edge.rootName 0 (parents[k + 1]'h).edge.baseInside)

/-- The actual first parent of a retained direct path starts at the original lifted coordinate. -/
private theorem chain_start {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {parent :
  PreparedSubdivisionModelCore.CenteredEdge curve differential}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : PreparedDirectDyadicRefinements.DirectPathChain (parent :: parents) (start := start) (finish := finish)) :
    start.coordinate = parent.edge.point 0 := by
  cases chain
  exact parent.edge.point_zero.symm

/-- The original direct parent chain supplies physical endpoint equality at every bounded adjacent occurrence. -/
theorem physicalAt {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {start finish :
  Lifted.Basic.LiftedPoint 2}
    (chain : PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)) :
    ∀ k h, PhysicalAt parents k h := by
  induction chain with
  | nil => intro k h; exact (Nat.not_lt_zero _ h).elim
  | @cons parent remaining finish tail ih =>
      intro k h
      cases k with
      | zero =>
          cases remaining with
          | nil => exact (Nat.lt_irrefl 1 h).elim
          | cons next rest =>
            exact parent.edge.point_one.trans
              (chain_start tail)
      | succ k => exact ih k (Nat.lt_of_succ_lt_succ h)

/-- Read the actual adjacent root equivalence from the original retained parent root chain.

The supplied position and retained list bound select the same original comparison and its exact endpoint names by
structural spine and natural elimination. -/
@[expose] def rootAt : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    {first last : Gaussian.Name.Basic.Named} → PreparedRefinementRootChains.RootChain parents first last →
    (k : Nat) → (h : k + 1 < parents.length) → PairedBoundaryClosure.RootAt parents k h
  | _, _, _, .nil _, _, h => (Nat.not_lt_zero _ h).elim
  | parent :: parents, _, _, .cons _ _ tail, k, h =>
      Nat.casesOn (motive := fun k => (h : k + 1 < (parent :: parents).length) →
        PairedBoundaryClosure.RootAt (parent :: parents) k h) k
        (fun h => match tail, h with
          | .nil _, h => (Nat.lt_irrefl 1 h).elim
          | .cons _ entry _, _ => entry)
        (fun k h => PairedBoundaryClosure.rootAt tail k (Nat.lt_of_succ_lt_succ h)) h

variable {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (CenteredEdge curve differential)} {target
    requested : Coordinate} {minimum : Nat}
  {original : Request regular other parents
    target minimum} (request :
    BoundaryBankRequest original requested)

/-- The retained left parent index of an actual adjacent pair. -/
@[expose] def leftParent (i : Fin (original.plans.length - 1)) : Fin original.plans.length := ⟨i.val, by omega0⟩
/-- The retained right parent index of an actual adjacent pair. -/
@[expose] def rightParent (i : Fin (original.plans.length - 1)) : Fin original.plans.length := ⟨i.val + 1, by omega0⟩

/-- All internal joins are obtained from the original retained source chain, then transported to the actual common-chart
endpoint owners. -/
@[expose] def sourceJoins {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain parents first last)
    (i : Fin (original.plans.length - 1)) : BoundaryBankRequest.EndpointJoin request
      (leftParent i)
      (rightParent i) := by
  have physical : ∀ k h, PhysicalAt
    (original.plans.map Plan.parent) k h := by
    obtain ⟨chain⟩ := chain
    exact physicalAt (original.parents_eq.symm ▸
      chain)
  let retained : PreparedRefinementRootChains.RootChain (original.plans.map Plan.parent) first last :=
    original.parents_eq.symm ▸ roots
  have bound : i.val + 1 < (original.plans.map Plan.parent).length := by
    rw [Data.List.Map.length_map]
    exact (rightParent i).isLt
  have same := physical i.val bound
  let link := rootAt retained i.val bound
  have leftMapped := Data.List.Map.getElem_map Plan.parent original.plans i.val
    (PairedBoundaryClosure.leftParent i).isLt ((Nat.lt_succ_self i.val).trans bound)
  have rightMapped := Data.List.Map.getElem_map Plan.parent original.plans (i.val + 1)
    (PairedBoundaryClosure.rightParent i).isLt bound
  rw [PairedBoundaryClosure.PhysicalAt, leftMapped, rightMapped] at same
  rw [PairedBoundaryClosure.RootAt, leftMapped, rightMapped] at link
  apply BoundaryBankRequest.endpointJoin request
    (leftParent i)
    (rightParent i)
  · dsimp only [PairedParentCharts.ChartParent, PairedBoundaryClosure.leftParent, PairedBoundaryClosure.rightParent]
    convert same using 1 <;> rfl
  · dsimp only [PairedParentCharts.ChartParent, PairedBoundaryClosure.leftParent, PairedBoundaryClosure.rightParent]
    convert link using 1 <;> rfl

/-- The dependent vector of original sheet-aware endpoint joins for every actual adjacent parent pair. -/
@[expose] def InternalJoins := Data.Vector.DependentVector (fun i => BoundaryBankRequest.EndpointJoin request
  (leftParent i)
  (rightParent i))

/-- The dependent coordinate comparison requests on the exact original retained parent joins. -/
@[expose] def JunctionPlans (joins : InternalJoins
  request) (allowance : InverseRootPolynomial.Coordinate) :=
  Data.Vector.DependentVector (fun i => BoundaryBankRequest.JunctionRequest request
    (leftParent i)
    (rightParent i) (joins.get i) allowance minimum)

/-- The actual common reading stage required by the retained original junction plan. -/
@[expose] def junctionIndexWeight {joins :
  InternalJoins request} {allowance :
  InverseRootPolynomial.Coordinate}
    (i : Fin (original.plans.length - 1))
    (plan : BoundaryBankRequest.JunctionRequest request
      (leftParent i)
      (rightParent i) (joins.get i) allowance minimum)
      : Nat := plan.index

set_option genInjectivity false in
/-- The complete paid junction schedule for the original retained parent boundary family.

It keeps each sheet-aware endpoint join and pays both connector insertion and the whole junction error sum. -/
structure LinkedRequest (junctionTarget : InverseRootPolynomial.Coordinate) where
  /-- The original retained endpoint-owner joins on every actual adjacent parent pair. -/ joins :
    InternalJoins request
  /-- The cached connector insertion scale from the original parent count and source slope. -/ insertionScale :
    InverseRootPolynomial.Coordinate
  /-- The insertion scale is exactly the retained fourth-power count and source-slope expression. -/ insertionScale_eq :
    insertionScale = 32 * ((2 * original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^4 * (4 *
    (original.slope + 1))
  /-- The cached common positive allowance paid to every original junction. -/ allowance :
    InverseRootPolynomial.Coordinate
  /-- The common allowance is the minimum of the aggregate target, unit ceiling and retained insertion budget. -/
    allowance_eq : allowance = min (Aggregate.perTerm junctionTarget (original.plans.length - 1))
    (min 1 (Weighted.allowance (junctionTarget / 2) insertionScale))
  /-- The actual common retained junction allowance is strictly positive. -/ positive : 0 < allowance
  /-- The retained junction allowance is at most one. -/ small : allowance ≤ 1
  /-- The cached insertion scale times the original allowance is below the complete junction target. -/ insertion_paid :
    insertionScale * allowance < junctionTarget
  /-- The complete original adjacent-parent count pays the sum of all retained junction errors. -/ paid :
    ((original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate) *
    (((original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate) * allowance) < junctionTarget
  /-- The dependent actual comparison plan on each original retained endpoint join. -/ junctions :
    JunctionPlans request joins allowance
  /-- The cached common reading stage paying the complete junction plan bank. -/ index : Nat
  /-- The cached junction stage is exactly the maximum of the original retained plan stages. -/ index_eq : index =
    junctions.maximum (junctionIndexWeight request)

constructive_injectivity LinkedRequest

/-- Retain every actual source-chain endpoint join, compute both connector and aggregate budgets, and prepare the
complete junction plan bank. -/
@[expose] def LinkedRequest.build (junctionTarget : InverseRootPolynomial.Coordinate) (positive : 0 < junctionTarget)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain parents first last) :
      LinkedRequest request junctionTarget := by
  let joins := DependentVector.ofFn (sourceJoins
    request chain roots)
  let insertionScale : Coordinate := 32 * ((2 * original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^4 *
    (4 * (original.slope + 1))
  have scaleNonnegative : 0 ≤ insertionScale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg original.slope_nonnegative (by decide)))
  have halfPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2)
  let allowance := min (Aggregate.perTerm junctionTarget (original.plans.length - 1))
    (min 1 (Weighted.allowance (junctionTarget / 2) insertionScale))
  have allowancePositive : 0 < allowance := Fraction.Order.Basic.lt_min (Aggregate.perTerm_positive positive _)
    (Fraction.Order.Basic.lt_min (by decide) (Weighted.allowance_positive halfPositive scaleNonnegative))
  have countNonnegative : (0 : InverseRootPolynomial.Coordinate) ≤ ((original.plans.length - 1 : Nat) :
    InverseRootPolynomial.Coordinate) := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have countPaid : ((original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate) *
      (((original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate) * allowance) < junctionTarget :=
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_left _ _) countNonnegative)
      countNonnegative).trans_lt
    (Aggregate.count_mul_perTerm_lt positive (original.plans.length - 1))
  have halfEq : junctionTarget / 2 + junctionTarget / 2 = junctionTarget :=
    (by ring1 : junctionTarget / 2 + junctionTarget / 2 = (junctionTarget / 2) * 2).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  have halfLess := (Fraction.Field.zero_add _ ▸ Fraction.Order.Arithmetic.add_lt_add_right_direct halfPositive
    _).trans_eq halfEq
  have insertionPaid : insertionScale * allowance < junctionTarget :=
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ((Fraction.Order.Basic.min_le_right _ _).trans
      (Fraction.Order.Basic.min_le_right _ _)) scaleNonnegative).trans
      (Weighted.mul_allowance_le halfPositive.le scaleNonnegative)).trans_lt halfLess
  let junctions := DependentVector.ofFn (fun i => JunctionRequest.build request
    (leftParent i)
    (rightParent i)
    (joins.get i) allowance allowancePositive minimum)
  exact ⟨joins, insertionScale, rfl, allowance, rfl, allowancePositive, (Fraction.Order.Basic.min_le_right _ _).trans
    (Fraction.Order.Basic.min_le_left _ _), insertionPaid, countPaid,
    junctions, junctions.maximum (junctionIndexWeight
      request), rfl⟩

variable {request}

/-- The first retained value minus the last retained value, with zero for an empty bank. -/
@[expose] def endDifference {n : Nat} (first last : Fin n → InverseRootPolynomial.Gaussian) : Gaussian :=
  match n, first, last with
  | 0, _, _ => 0
  | n + 1, first, last => first 0 - last (Fin.last n)

/-- For a nonempty retained bank the endpoint difference reads its actual first and last indices. -/
private theorem endDifference_nonempty {n : Nat} (first last : Fin n → InverseRootPolynomial.Gaussian) (positive : 0 <
  n) :
    endDifference first last = first ⟨0, positive⟩ -
      last ⟨n - 1, by omega0⟩ := by
  cases n with
  | zero => exact (Nat.not_lt_zero _ positive).elim
  | succ _ => rfl

/-- The endpoint difference of an empty retained bank is zero. -/
private theorem endDifference_empty {n : Nat} (first last : Fin n → InverseRootPolynomial.Gaussian) (absent : n = 0) :
    endDifference first last = 0 := by
  cases absent;
  rfl

/-- The full endpoint-difference sum minus all actual adjacent gaps is the original outer endpoint difference. -/
private theorem telescope {n : Nat} (first last : Fin (n + 1) → InverseRootPolynomial.Gaussian) :
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

/-- The same complete endpoint cancellation holds for every finite bank, including the empty case. -/
private theorem telescope_all {n : Nat} (first last : Fin n → InverseRootPolynomial.Gaussian) :
    FiniteSum.Fin.sumFin (fun i => first i - last i) -
      FiniteSum.Fin.sumFin (fun i : Fin (n - 1) => first ⟨i.val + 1, by omega0⟩ - last ⟨i.val, by omega0⟩) =
      endDifference first last := by
  cases n with
  | zero => change (0 : InverseRootPolynomial.Gaussian) - 0 = 0; ring1
  | succ n => exact telescope first last

/-- The actual paired radial potential at the retained first coordinate of one original parent. -/
@[expose] def Evaluation.firstPotential (evaluated : request.Evaluation) (i : Fin original.plans.length) : Gaussian :=
  Bilinear.radialArea (Evaluation.radialValues evaluated) evaluated.radialDepth ((Evaluation.firstCoordinate evaluated)
    i)

/-- The actual paired radial potential at the retained last coordinate of one original parent. -/
@[expose] def Evaluation.lastPotential (evaluated : request.Evaluation) (i : Fin original.plans.length) : Gaussian :=
  Bilinear.radialArea (Evaluation.radialValues evaluated) evaluated.radialDepth ((Evaluation.lastCoordinate evaluated)
    i)

/-- The original parent bank's complete outer radial endpoint difference. -/
@[expose] def Evaluation.outerBoundary (evaluated : request.Evaluation) : Gaussian :=
  endDifference
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.firstPotential evaluated)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.lastPotential evaluated)

/-- A nonempty original bank's outer radial boundary reads its actual first and last retained potentials. -/
theorem Evaluation.outerBoundary_nonempty (evaluated : request.Evaluation) (positive : 0 < original.plans.length) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.outerBoundary evaluated =
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.firstPotential evaluated ⟨0,
      positive⟩ -
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.lastPotential evaluated
        ⟨original.plans.length - 1, by omega0⟩ :=
  endDifference_nonempty _ _ positive

/-- The original empty parent bank has zero outer radial boundary. -/
theorem Evaluation.outerBoundary_empty (evaluated : request.Evaluation) (absent : original.plans.length = 0) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.outerBoundary evaluated = 0 :=
      endDifference_empty _ _ absent

/-- The actual paired primitive edge area joining one retained parent's last coordinate to the next first coordinate. -/
@[expose] def Evaluation.parentConnector (evaluated : request.Evaluation) (i : Fin (original.plans.length - 1)) :
  Gaussian :=
  Stokes.edgeArea (Evaluation.radialValues evaluated ((Evaluation.lastCoordinate evaluated)
    (leftParent i)))
    (Evaluation.radialValues evaluated ((Evaluation.firstCoordinate evaluated)
      (rightParent i)))

/-- Every actual parent's radial value function uses exactly the original two cap samples shared by the full bank. -/
private theorem radialValues_eq (evaluated : request.Evaluation) (i : Fin original.plans.length) :
    CommonChartRadialJunctions.radialValues (evaluated.entries.get i) = Evaluation.radialValues evaluated :=
  (congrArg (fun sample : Primitives.Sample cap differential request.index collar.box =>
    fun point => (⟨sample.primitive.value.eval point, (evaluated.entries.get i).samples.otherCap.primitive.value.eval
      point⟩ :
      Stokes.PrimitivePoint)) (evaluated.shared i).1).trans
    (congrArg (fun sample : Primitives.Sample cap other request.index collar.box =>
      fun point => (⟨evaluated.firstCap.primitive.value.eval point, sample.primitive.value.eval point⟩ :
        Stokes.PrimitivePoint)) (evaluated.shared i).2)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans.FanBankRequest (ConnectorArea
  OuterRadialBoundary)

/-- Each retained parent's full outer radial boundary is its actual first potential minus its last potential. -/
private theorem outer_readback (evaluated : request.Evaluation) (i : Fin original.plans.length) :
    FanBankRequest.OuterRadialBoundary (evaluated := evaluated.entries.get i) evaluated.radialDepth =
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.firstPotential evaluated i -
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.lastPotential evaluated i := by
  rw [FanBankRequest.outerRadialBoundary_eq
    evaluated.radialDepth (PairedParentCharts.ChartParent original i).common.nonempty]
  unfold CommonChartRadialJunctions.radialPotential
  rw [radialValues_eq evaluated i]
  rfl

/-- The complete sum of all actual within-parent common-chart connector areas. -/
@[expose] def Evaluation.internalConnectors (evaluated : request.Evaluation) : Gaussian :=
  FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (FanBankRequest.ConnectorArea (evaluated := evaluated.entries.get
    i)))

/-- The full original source area with restoration correction, internal and cross-parent connectors, and outer radial
ends retained. -/
@[expose] def Evaluation.linkedBoundary (evaluated : request.Evaluation) : Gaussian :=
  evaluated.sourceArea - evaluated.correction +
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.internalConnectors evaluated +
    FiniteSum.Fin.sumFin (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.parentConnector
      evaluated) + Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.outerBoundary evaluated

/-- The complete linked boundary equals the original acquired boundary area minus every actual cross-parent junction
error. -/
theorem Evaluation.linkedBoundary_eq (evaluated : request.Evaluation) :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.linkedBoundary evaluated =
      evaluated.area -
      FiniteSum.Fin.sumFin (fun i => Evaluation.junctionError evaluated
        (leftParent i)
        (rightParent i)) := by
  have outer := FiniteSum.Fin.sumFin_congr
    (outer_readback evaluated)
  have telescoping := telescope_all
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.firstPotential evaluated)
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.lastPotential evaluated)
  rw [evaluated.decomposition, evaluated.openEnds_common, FiniteSum.Fin.sumFin_add, outer]
  have errors : FiniteSum.Fin.sumFin (fun i => Evaluation.junctionError evaluated
    (leftParent i)
    (rightParent i)) =
      FiniteSum.Fin.sumFin (fun i =>
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.firstPotential evaluated
        (rightParent i) -
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.lastPotential evaluated
        (leftParent i)) -
        FiniteSum.Fin.sumFin
          (Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.parentConnector evaluated) :=
          FiniteSum.Fin.sumFin_sub _ _
  rw [errors]
  change FiniteSum.Fin.sumFin (fun i =>
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.firstPotential evaluated i -
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.lastPotential evaluated i) -
    FiniteSum.Fin.sumFin (fun i =>
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.firstPotential evaluated
      (rightParent i) -
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.lastPotential evaluated
      (leftParent i)) =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.outerBoundary evaluated at telescoping
  unfold Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.linkedBoundary
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.internalConnectors
  rw [← telescoping]
  ring1

set_option genInjectivity false in
/-- The acquired original boundary family with every paid junction correction cached.

Its actual error vector and complete linked area retain exact readbacks and the requested whole bound. -/
structure LinkedRequest.Certificate {junctionTarget : InverseRootPolynomial.Coordinate} (linked :
  LinkedRequest request junctionTarget) where
  /-- The actual original parent boundary acquisition at the shared external reading floor. -/ boundary :
    request.Evaluation
  /-- The retained boundary reading floor pays the complete original junction schedule. -/ readingFloor_le :
    linked.index ≤ boundary.externalFloor
  /-- Every actual retained cross-parent primitive increment satisfies the common paid junction allowance. -/
    increments_bounded : ∀ i, PrimitivePoint.Bounded
    (Evaluation.junctionIncrement boundary (leftParent
      i) (rightParent i)) linked.allowance
  /-- The cached actual junction-error vector in original adjacent-parent order. -/ errors : Data.Vector
    InverseRootPolynomial.Gaussian (original.plans.length - 1)
  /-- Each cached error is exactly its original retained adjacent-parent junction error. -/ errors_eq : ∀ i, errors i =
    Evaluation.junctionError boundary (leftParent i)
    (rightParent i)
  /-- The cached sum of all actual retained junction errors. -/ error : InverseRootPolynomial.Gaussian
  /-- The complete error cache is exactly the sum of the original error vector. -/ error_eq : error =
    FiniteSum.Fin.sumFin errors
  /-- The complete retained error sum satisfies the requested strict junction bound. -/ error_bounded :
    Data.Gaussian.Norm.Basic.normSq error < junctionTarget
  /-- The cached actual linked boundary area after all retained junction errors are subtracted. -/ area :
    InverseRootPolynomial.Gaussian
  /-- The linked area cache equals the actual original boundary area minus its cached total junction error. -/ area_eq :
    area = boundary.area - error
  /-- The linked area cache reads the complete original source, connector and radial-boundary decomposition. -/
    boundary_eq : area = Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.linkedBoundary
    boundary
  /-- The actual linked area satisfies the combined original boundary and junction target bound. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq area < 2 * (requested + junctionTarget)

constructive_injectivity LinkedRequest.Certificate

/-- Acquire the original boundary once at a paid floor, cache every actual junction error, and retain the complete
linked area and bounds. -/
@[expose] def LinkedRequest.acquire {junctionTarget : InverseRootPolynomial.Coordinate} (linked :
  LinkedRequest request junctionTarget)
    (externalFloor : Nat) (later : linked.index ≤ externalFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.LinkedRequest.Certificate linked := by
  let boundary := request.acquire externalFloor branch
  let errors := Data.Vector.Basic.vectorOfFn (fun i => Evaluation.junctionError boundary
    (leftParent i)
    (rightParent i))
  have errorsEq : ∀ i, errors i = Evaluation.junctionError boundary
    (leftParent i)
    (rightParent i) := fun i =>
    Data.Vector.Basic.vectorOfFn_apply _ i
  have each : ∀ i, Data.Gaussian.Norm.Basic.normSq (errors i) < linked.allowance := by
    intro i
    rw [errorsEq]
    exact JunctionRequest.accurate (linked.junctions.get i) boundary
      (((DependentVector.get_le_maximum
        (junctionIndexWeight request) linked.junctions
        i).trans_eq linked.index_eq.symm).trans later) branch
  let error := FiniteSum.Fin.sumFin errors
  have estimate := Indexed.normSq_sumFin_le errors linked.allowance (fun i => (each i).le)
  have paid : (((original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^2) * linked.allowance <
    junctionTarget :=
    (by ring1 : (((original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^2) * linked.allowance =
      ((original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate) *
        (((original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate) * linked.allowance)).trans_lt
          linked.paid
  have errorBound : Data.Gaussian.Norm.Basic.normSq error < junctionTarget := estimate.trans_lt paid
  have bound := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two boundary.area error).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct boundary.bounded errorBound))
  have boundaryEq : boundary.area - error =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.linkedBoundary boundary := by
    rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.linkedBoundary_eq boundary]
    exact congrArg (fun value => boundary.area - value) (FiniteSum.Fin.sumFin_congr errorsEq)
  have incrementsBounded := fun i => JunctionRequest.increment_accurate (linked.junctions.get i) boundary
    (((DependentVector.get_le_maximum
      (junctionIndexWeight request) linked.junctions
      i).trans_eq linked.index_eq.symm).trans later) branch
  exact ⟨boundary, later, incrementsBounded, errors, errorsEq, error, rfl, errorBound,
    boundary.area - error, rfl, boundaryEq, bound⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure
