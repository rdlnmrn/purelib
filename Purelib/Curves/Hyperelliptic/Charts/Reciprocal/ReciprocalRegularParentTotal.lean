module
import Purelib.Data.Nat.Order
import Purelib.Data.List.OfFn.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.JoinedTraceIncrements
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentReadings
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Transfer the closed regular chart total to the literal raw source path.
All parent joins use one reading floor and the original shared cap samples. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTotal

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentReadings
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Geometry.Path.Gaussian
open Purelib.Integration.Path
open Purelib.Integration.Path.JoinedTraceIncrements
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts (ChartBankRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints (RegularEndpointRequest)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_neg normSq_zero)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {target requested : Coordinate} {minimum depth : Nat}
  {original : Request regular other parents
    target minimum}
  {request : ChartBankRequest original depth
    requested}

/-- The raw source total is small on a closed root chain. The shared reading floor and every connector tolerance are
chosen inside the proof. -/
private theorem regular_source_total_bound_nonempty (evaluated : request.Evaluation)
    (present : 0 < original.plans.length) (small : request.allowance ≤ 1)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain parents first last)
    (closed : start.coordinate = finish.coordinate)
    (returned : Gaussian.Equivalence.NamedEquivalent last first)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    PrimitivePoint.Bounded (PairedIncrementArea.total evaluated.sourcePaths.flatten) (33 * requested) := by
  have countNonnegative : (0 : InverseRootPolynomial.Coordinate) ≤ original.plans.length :=
    Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have positive : 0 < requested :=
    (Fraction.Order.Arithmetic.mul_nonneg_direct countNonnegative (Fraction.Order.Arithmetic.mul_nonneg_direct
      countNonnegative request.positive.le)).trans_lt request.paid
  let count : Coordinate := (2 * original.plans.length - 1 : Nat)
  let weight : Coordinate := 4 * (count^2 + 1)
  have weightNonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct count) (by decide))
  let error := Weighted.allowance requested weight
  have errorPositive : 0 < error := Weighted.allowance_positive positive weightNonnegative
  let joins := ReciprocalRegularParentTrace.sourceJoins request chain roots
  let endpoints := DependentVector.ofFn (fun i : Fin (original.plans.length - 1) =>
    RegularEndpointRequest.build evaluated _ _ (joins i) error errorPositive minimum)
  let closing := ReciprocalRegularParentTrace.closingJoin request present chain roots closed returned
  let finalEndpoint := RegularEndpointRequest.build evaluated _ _ closing error errorPositive minimum
  let endpointWeight := fun (i : Fin (original.plans.length - 1))
    (entry : ReciprocalRegularParentEndpoints.RegularEndpointRequest evaluated _ _ (joins i) error minimum) =>
      entry.index
  let stage := max finalEndpoint.index (endpoints.maximum endpointWeight)
  let retained := Evaluation.atReadingFloor evaluated stage
  have gaps : ∀ i : Fin (original.plans.length - 1),
      PrimitivePoint.Bounded ((Evaluation.chartTrace (retained.entries.get ⟨i.val + 1, by omega0⟩)).first.sub
        (Evaluation.chartTrace (retained.entries.get ⟨i.val, by omega0⟩)).last) error := by
    intro i
    have later := endpoints.get_le_maximum endpointWeight i
    dsimp only [endpoints, endpointWeight, -eq_self, -iff_self] at later
    rw [DependentVector.ofFn_get] at later
    exact RegularEndpointRequest.atReadingFloor_bound evaluated _ _ (joins i) error errorPositive minimum stage
      (later.trans (Data.Nat.Order.le_max_right _ _)) unramified
  have closingBound := RegularEndpointRequest.atReadingFloor_bound evaluated _ _ closing error errorPositive minimum
    stage (Data.Nat.Order.le_max_left _ _) unramified
  have totalBound : PrimitivePoint.Bounded (PairedIncrementArea.total (VertexTrace.increments (Evaluation.regularTrace
    retained) id)) error := by
    rw [Evaluation.regularTrace_increment_total retained, Evaluation.regularTrace_last retained present,
      Evaluation.regularTrace_first retained present]
    have reverse (a b : InverseRootPolynomial.Gaussian) : Data.Gaussian.Basic.Canonical.normSq (a - b) =
      Data.Gaussian.Basic.Canonical.normSq (b - a) := by
      rw [show a - b = -(b - a) by ring1, Data.Gaussian.Basic.Canonical.normSq_neg]
    exact ⟨(reverse _ _).trans_le closingBound.1, (reverse _ _).trans_le closingBound.2⟩
  have inserted := Evaluation.regularTrace_total_insertion retained errorPositive.le gaps
  have source := Evaluation.source_parent_totals_bound retained small
  have paid : (original.plans.length : InverseRootPolynomial.Coordinate)^2 * (16 * request.allowance) ≤ 16 * requested
    :=
    (by ring1 : (original.plans.length : InverseRootPolynomial.Coordinate)^2 * (16 * request.allowance) =
      16 * ((original.plans.length : InverseRootPolynomial.Coordinate) * ((original.plans.length :
        InverseRootPolynomial.Coordinate) * request.allowance))).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.paid.le (by decide))
  have connectorPaid : weight * error ≤ requested :=
    Weighted.mul_allowance_le positive.le weightNonnegative
  have scalar (a b c : InverseRootPolynomial.Gaussian) (sourceBound : Data.Gaussian.Norm.Basic.normSq (a - b) ≤
    16 * requested)
      (insertedBound : Data.Gaussian.Norm.Basic.normSq (b - c) ≤ count^2 * error) (closedBound :
        Data.Gaussian.Norm.Basic.normSq c ≤ error) :
      Data.Gaussian.Norm.Basic.normSq a ≤ 33 * requested := by
    have middle := Data.Gaussian.Norm.Bounds.normSq_sub_le_via b c 0
    rw [Data.Gaussian.Basic.sub_zero, Data.Gaussian.Basic.sub_zero] at middle
    have middleBound := middle.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct insertedBound closedBound) (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
    have outer := Data.Gaussian.Norm.Bounds.normSq_sub_le_via a b 0
    rw [Data.Gaussian.Basic.sub_zero, Data.Gaussian.Basic.sub_zero] at outer
    have before := outer.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct sourceBound middleBound) (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
    have identity : 2 * (16 * requested + 2 * (count^2 * error + error)) = 32 * requested + weight * error := by
      dsimp only [weight, -eq_self, -iff_self]
      ring1
    exact before.trans (identity.trans_le ((Fraction.Order.Arithmetic.add_le_add_direct le_rfl connectorPaid).trans_eq
      (by ring1)))
  have oldBound {value : Data.Gaussian.Basic.Canonical} {limit : InverseRootPolynomial.Coordinate}
      (bound : Data.Gaussian.Basic.Canonical.normSq value ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using bound
  have canonicalBound {value : Data.Gaussian.Basic.Canonical} {limit : InverseRootPolynomial.Coordinate}
      (bound : Data.Gaussian.Norm.Basic.normSq value ≤ limit) :
      Data.Gaussian.Basic.Canonical.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using bound
  have bounded : PrimitivePoint.Bounded (PairedIncrementArea.total retained.sourcePaths.flatten) (33 * requested) :=
    ⟨canonicalBound (scalar _ _ _ (oldBound (source.1.trans paid)) (oldBound inserted.1) (oldBound totalBound.1)),
      canonicalBound (scalar _ _ _ (oldBound (source.2.trans paid)) (oldBound inserted.2) (oldBound totalBound.2))⟩
  rw [Evaluation.atReadingFloor_sourcePaths] at bounded
  exact bounded

/-- The same raw-source bound includes an empty parent bank. A numerical request at most one supplies the local block
comparison's smallness bound. -/
theorem Evaluation.regular_source_total_bound (evaluated : request.Evaluation)
    (small : requested ≤ 1)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain parents first last)
    (closed : start.coordinate = finish.coordinate)
    (returned : Gaussian.Equivalence.NamedEquivalent last first)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    PrimitivePoint.Bounded (PairedIncrementArea.total evaluated.sourcePaths.flatten) (33 * requested) := by
  rcases Nat.eq_zero_or_pos original.plans.length with empty | present
  · have pathsEmpty : evaluated.sourcePaths = [] := List.eq_nil_of_length_eq_zero (by
      rw [Evaluation.sourcePaths, Data.List.OfFn.Basic.length_ofFn, empty])
    have positive : 0 < requested := by
      have paid := request.paid
      simpa only [empty, Nat.cast_zero, zero_mul, -eq_self, -iff_self] using paid
    rw [pathsEmpty]
    have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 33) positive.le
    exact ⟨normSq_zero.trans_le nonnegative, Data.Gaussian.Norm.Basic.normSq_zero.trans_le nonnegative⟩
  · have count : (1 : InverseRootPolynomial.Coordinate) ≤ original.plans.length := Fraction.Cast.Order.natCast_le_direct
      present
    have square := Fraction.Order.Arithmetic.pow_le_pow_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)
      count 2
    rw [show (1 : InverseRootPolynomial.Coordinate)^2 = 1 by decide] at square
    have allowance := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct square request.positive.le
    rw [Fraction.Field.one_mul] at allowance
    have paid : (original.plans.length : InverseRootPolynomial.Coordinate)^2 * request.allowance < requested :=
      (by ring1 : (original.plans.length : InverseRootPolynomial.Coordinate)^2 * request.allowance =
        (original.plans.length : InverseRootPolynomial.Coordinate) * ((original.plans.length :
          InverseRootPolynomial.Coordinate) * request.allowance)).trans_lt request.paid
    exact regular_source_total_bound_nonempty
      evaluated present (allowance.trans (paid.le.trans small))
      chain roots closed returned unramified

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTotal
