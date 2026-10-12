module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Division.Obstruction.Zero
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Residual.Global.Assignment
import Purelib.RootIsolation.Residual.Global.Bounds

public import Purelib.Riemann.RootContinuation.SquareRootProvenance
public import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Winding ownership of an existing operational square-root channel

Localize one sufficiently accurate sample, retaining a small winding-one
track near that sample. Channel coherence and a positive root bound keep the
two channels on the same occurrence. The quadratic product identity then
turns their square residuals into arbitrarily accurate root comparisons.
No completed root, root-choice axiom, or caller ownership equality is used.
-/

namespace Purelib.Riemann.RootContinuation.SquareRootChannelOwnership

open Purelib.Riemann.RootContinuation.SquareRootProvenance
open Purelib.Riemann.RootContinuation.SquareRootReconditioning

open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of the retained square-root parameter. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Data.Rat in
/-- The rational coordinate carrier of the root ownership bounds. -/
abbrev Coordinate := Fraction.Rational
/-- The original coherent executable Gaussian channel carrier. -/
abbrev CoherentNamed := Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
/-- Equivalence of the original executable Gaussian names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
open Purelib.Approximation.Gaussian in
/-- The original executable Gaussian approximation carrier. -/
abbrev Approximation := Sequence.ApproximationData
/-- The retained executable apartness evidence for an original Gaussian name. -/
abbrev Apart := Purelib.Approximation.Gaussian.Name.Basic.Named.Apart
/-- The original square-root continuation owner at its exact parameter. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.RootContinuation.SquareRootProvenance (SquareIdentity sampled_square)
open SquareRootReconditioning (rootPolynomial isolationInput)

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- An apart certified square-root channel has nonzero parameter. -/
theorem parameter_nonzero {parameter : Gaussian} (source : CertifiedSquareRoot.Certificate parameter) :
    parameter ≠ 0 := by
  intro zero
  have square : SquareIdentity source.value 0 := by
    simpa only [SquareIdentity, Name.Coherent.CoherentNamed.Coherence.exact, zero] using source.square
  exact Division.Obstruction.Zero.ZeroIdentity.incompatible_apart
    (SquareRootProvenance.zero_of_square square) source.apart

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- A near pair retains a lower norm bound on its sum from the first root's lower bound. -/
private theorem sum_lower {left right : Gaussian} {lower : Coordinate}
    (rootLower : lower ≤ normSq left) (near : normSq (left - right) ≤ lower) :
    lower ≤ normSq (left + right) := by
  have doubled : normSq (left + left) = 4 * normSq left := by
    simp only [normSq, Basic.add_re, Basic.add_im]
    ring1
  have identity : left + left - (left - right) = left + right := by ring1
  have estimate := Norm.Bounds.half_normSq_sub_le_normSq_sub (left + left) (left - right)
  simp only [Norm.Basic.normSq_eq_canonical] at estimate
  rw [doubled, identity] at estimate
  calc
    lower = 2 * lower - lower := by ring1
    _ ≤ 2 * normSq left - normSq (left - right) :=
      Fraction.Order.Arithmetic.sub_le_sub_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rootLower (by decide)) near
    _ = 4 * normSq left / 2 - normSq (left - right) := by
      have half : 4 * normSq left / 2 = 2 * normSq left := by
        apply Fraction.Field.mul_right_cancel_of_ne (show (2 : Coordinate) ≠ 0 by decide)
        rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
        ring1
      rw [half]
    _ ≤ _ := estimate

/-- Small square residuals and a retained near-root witness force the requested root-distance bound.

The positive lower norm and closeness assumptions bound the sum away from zero, allowing the original
difference-of-squares estimate to control the root difference. -/
theorem root_distance {left right parameter : Gaussian} {lower target : Coordinate}
    (lowerPositive : 0 < lower) (rootLower : lower ≤ normSq left)
    (near : normSq (left - right) ≤ lower)
    (leftResidual : normSq (left * left - parameter) < target * lower / 4)
    (rightResidual : normSq (right * right - parameter) < target * lower / 4) :
    normSq (left - right) < target := by
  have sumLower := sum_lower rootLower near
  have residualBound : normSq (left * left - right * right) < target * lower := by
    have identity : left * left - right * right =
        (left * left - parameter) - (right * right - parameter) := by ring1
    rw [identity]
    calc
      _ ≤ 2 * (normSq (left * left - parameter) + normSq (right * right - parameter)) :=
        by
          have scalar := Norm.Bounds.normSq_sub_le_two
            (left * left - parameter) (right * right - parameter)
          simpa only [Norm.Basic.normSq_eq_canonical] using scalar
      _ < 2 * (target * lower / 4 + target * lower / 4) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
          (Fraction.Order.Arithmetic.add_lt_add_direct leftResidual rightResidual)
      _ = (target * lower / 4) * 4 := by ring1
      _ = _ := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := lower) _ lowerPositive
  calc
    normSq (left - right) * lower ≤ normSq (left - right) * normSq (left + right) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumLower (Basic.Canonical.normSq_nonneg _)
    _ = normSq (left * left - right * right) := by
      rw [← Basic.Canonical.normSq_mul, show (left - right) * (left + right) = left * left - right * right by ring1]
    _ < _ := residualBound

end

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Data in
/-- Compare original square-root channels using retained square identities, apartness and eventual proximity.

The returned comparison preserves both requested index floors and derives its residual target from the original
apartness lower bound. -/
def equivalent_of_near {left right : CoherentNamed} {parameter : Gaussian}
    (leftSquare : SquareIdentity left parameter) (rightSquare : SquareIdentity right parameter)
    (apart : Apart left.name) (base : Nat)
    (near : ∀ leftIndex rightIndex, base ≤ leftIndex →
      normSq ((Name.Sampling.approximation left.name).sample leftIndex -
        (Name.Sampling.approximation right.name).sample rightIndex) ≤ apart.certificate.lowerSq) :
    NamedEquivalent left.name right.name where
  compare := by
    intro leftStart rightStart target positive
    let residualTarget := target * apart.certificate.lowerSq / 4
    have residualPositive : 0 < residualTarget :=
      Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Arithmetic.mul_pos_direct positive apart.certificate.positive) (by decide)
    have baseBound : base ≤ max base leftStart := by
      rw [Nat.Order.max_eq_natMax]
      exact Nat.Order.le_max_left _ _
    have startBound : leftStart ≤ max base leftStart := by
      rw [Nat.Order.max_eq_natMax]
      exact Nat.Order.le_max_right _ _
    let first := (sampled_square leftSquare).compare (max base leftStart) 0 residualTarget residualPositive
    let second := (sampled_square rightSquare).compare rightStart 0 residualTarget residualPositive
    refine
      { leftIndex := first.leftIndex
        rightIndex := second.leftIndex
        left_ge := startBound.trans first.left_ge
        right_ge := second.left_ge
        close := ?_ }
    intro leftLater rightLater leftOrder rightOrder
    have leftResidual := first.close leftOrder (Nat.le_refl first.rightIndex)
    have rightResidual := second.close rightOrder (Nat.le_refl second.rightIndex)
    rw [Norm.Basic.normSq_eq_canonical] at leftResidual rightResidual
    change normSq ((Name.Sampling.approximation left.name).sample leftLater *
      (Name.Sampling.approximation left.name).sample leftLater - parameter) < residualTarget at leftResidual
    change normSq ((Name.Sampling.approximation right.name).sample rightLater *
      (Name.Sampling.approximation right.name).sample rightLater - parameter) < residualTarget at rightResidual
    have rootLower := Name.Apart.Sampling.sampled_lower left apart leftLater
    rw [Norm.Basic.normSq_eq_canonical] at rootLower
    rw [Norm.Basic.normSq_eq_canonical]
    exact root_distance apart.certificate.positive rootLower
      (near leftLater rightLater (baseBound.trans (first.left_ge.trans leftOrder)))
      leftResidual rightResidual

open Purelib.Approximation.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation.Residual in
set_option genInjectivity false in
/-- An authenticated square-root sample with retained tail proximity and root-isolation evidence.

The sample keeps its exact channel index, positive lower bound and dyadic radius, together with containment in the
original root polynomial's box and its residual target. -/
structure Anchor (source : CoherentNamed) (parameter : Gaussian) where
  /-- The original root parameter is nonzero. -/ nonzero : parameter ≠ 0
  /-- The retained positive apartness lower bound from the original channel. -/ lower : Coordinate
  /-- Strict positivity of the original lower bound. -/ positive : 0 < lower
  /-- The retained dyadic root-assignment radius. -/ radius : Coordinate
  /-- Strict positivity of the retained radius. -/ radiusPositive : 0 < radius
  /-- The radius squared is below the original lower bound divided by 1024. -/ radiusSmall : radius ^ 2 < lower / 1024
  /-- The original channel's retained sample index. -/ index : Nat
  /-- The authenticated original Gaussian sample. -/ value : Gaussian
  /-- Exact equality with the original channel sample at the retained index. -/ value_eq : value =
    (Name.Sampling.approximation source.name).sample index
  /-- Every later original sample stays within lower-bound divided by eight of this sample. -/ tailNear : ∀ later, index
    ≤ later →
    normSq ((Name.Sampling.approximation source.name).sample later - value) ≤ lower / 8
  /-- The actual sample lies in the original root polynomial's certified large box. -/ inside :
    (Bounds.RootRadius.Box.largeSquareBox (rootPolynomial parameter)).Contains value
  /-- The actual sample satisfies the original inside-assignment residual target at this radius. -/ residual : normSq
    ((rootPolynomial parameter).eval value) <
    Global.Assignment.insideResidualTarget (isolationInput nonzero) radius

constructive_injectivity Anchor

open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.Residual in
/-- Acquire an authenticated original square-root sample satisfying the retained isolation and tail bounds.

The radius is chosen below lower-bound divided by 1024; the actual sample satisfies both inside/outside residual
thresholds and retains later-sample proximity at lower-bound divided by eight. -/
def Anchor.build {parameter : Gaussian} (source : CertifiedSquareRoot.Certificate parameter) :
    Anchor source.value parameter := by
  let nonzero := parameter_nonzero source
  let input := isolationInput nonzero
  let lower := source.apart.certificate.lowerSq
  let radius := SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius (lower / 1024)
  have lowerPositive : 0 < lower := source.apart.certificate.positive
  have radiusPositive : 0 < radius := SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_positive _
  let target := min (Global.Bounds.outsideResidualThreshold (rootPolynomial parameter))
    (Global.Assignment.insideResidualTarget input radius)
  have targetPositive : 0 < target := Fraction.Order.Basic.lt_min
    (Global.Bounds.outsideResidualThreshold_pos input.degreePositive)
    (Global.Assignment.insideResidualTarget_pos input radiusPositive)
  let comparison := (sampled_square source.square).compare 0 0 target targetPositive
  let approximation := Name.Sampling.approximation source.value.name
  have nearPositive : 0 < lower / 8 := Fraction.Order.Field.div_pos_direct lowerPositive (by decide)
  let index := approximation.refineIndex comparison.leftIndex (lower / 8) nearPositive
  let value := approximation.sample index
  have residual : normSq ((rootPolynomial parameter).eval value) < target := by
    rw [rootPolynomial, Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval]
    change normSq (value ^ 2 - parameter) < target
    rw [pow_two]
    have scalar := comparison.close (approximation.refineIndex_ge comparison.leftIndex (lower / 8) nearPositive)
      (Nat.le_refl comparison.rightIndex)
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    change normSq (value * value - parameter) < target at scalar
    exact scalar
  have inside : (Bounds.RootRadius.Box.largeSquareBox (rootPolynomial parameter)).Contains value := by
    by_cases contains : (Bounds.RootRadius.Box.largeSquareBox (rootPolynomial parameter)).Contains value
    · exact contains
    · have outside := Global.Bounds.outsideResidualThreshold_le input.degreeAtLeastTwo value contains
      rw [Norm.Basic.normSq_eq_canonical] at outside
      exact ((not_lt_of_ge outside) (residual.trans_le (Fraction.Order.Basic.min_le_left _ _))).elim
  exact
    { nonzero := nonzero
      lower := lower
      positive := lowerPositive
      radius := radius
      radiusPositive := radiusPositive
      radiusSmall := SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_sq_lt
        (Fraction.Order.Field.div_pos_direct lowerPositive (by decide +kernel))
      index := index
      value := value
      value_eq := rfl
      tailNear := fun later order => by
        have scalar := (approximation.later_close order).trans
          (approximation.refineIndex_accurate comparison.leftIndex (lower / 8) nearPositive).le
        simpa only [Norm.Basic.normSq_eq_canonical] using scalar
      inside := inside
      residual := residual.trans_le (Fraction.Order.Basic.min_le_right _ _) }

open Purelib.Data.Rat in
/-- A radius squared below lower-bound divided by 1024 pays the retained eighteen-times-radius band bound.

Multiplication by eighteen preserves the retained nonnegative scalar bound. Exact rational constants compare the
resulting radius payment with the original positive lower bound divided by eight. -/
theorem band_small {lower radius : Coordinate} (positive : 0 < lower)
    (small : radius ^ 2 < lower / 1024) : 18 * radius ^ 2 ≤ lower / 8 := by
  calc
    _ ≤ 18 * (lower / 1024) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small.le (by decide)
    _ = (18 / 1024 : Coordinate) * lower := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ ≤ (1 / 8 : Coordinate) * lower :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel) positive.le
    _ = _ := by simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1

open Purelib.Approximation.Gaussian in
set_option genInjectivity false in
/-- An original root owner with an equivalence to the supplied source name.

The name projection is applied to that exact owner, preserving the original parameter and explicit source-to-owner
comparison witness. -/
structure OwnerNameAttachment (parameter : Gaussian)
    (name : Owner parameter → Name.Basic.Named) (source : Name.Basic.Named) where
  /-- The retained original continuation root owner. -/ owner : Owner parameter
  /-- The supplied source name is equivalent to this exact owner's projected name. -/ equivalent : NamedEquivalent
    source (name owner)

constructive_injectivity OwnerNameAttachment

/-- An original coherent channel attached to the certificate name of its retained root owner. -/
abbrev Attachment (source : CoherentNamed) (parameter : Gaussian) :=
  OwnerNameAttachment parameter (fun owner => (owner.certificate owner.parameterNonzero).value.name) source.name

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation.Residual in
/-- Attach the certified original channel to a residual-isolation root owner.

The same authenticated sample and radius select the original isolation track; tail proximity and its retained
sample-band bound certify equivalence to that actual owner's channel. -/
def attach {parameter : Gaussian} (source : CertifiedSquareRoot.Certificate parameter) :
    Attachment source.value parameter := by
  let anchor := Anchor.build source
  let assigned := Global.Assignment.assignInside (isolationInput anchor.nonzero) anchor.value
    anchor.inside anchor.radiusPositive (by simpa only [Norm.Basic.normSq_eq_canonical] using anchor.residual)
  let owner : Owner parameter :=
    { parameterNonzero := anchor.nonzero
      ambient := Bounds.RootRadius.Box.largeSquareBox (rootPolynomial parameter)
      track := assigned.track }
  refine ⟨owner, equivalent_of_near source.square (owner.certificate owner.parameterNonzero).square
    source.apart anchor.index ?_⟩
  intro leftIndex rightIndex order
  let left := (Name.Sampling.approximation source.value.name).sample leftIndex
  let rightName := (owner.certificate owner.parameterNonzero).value.name
  let right := (Name.Sampling.approximation rightName).sample rightIndex
  have contained : assigned.state.box.Contains right := by
    have inside := owner.certificate_candidate_in_initial_box owner.parameterNonzero _
      (Process.Sampling.witnessAt_possible rightName.process rightName.state rightIndex)
    change assigned.track.initial.box.Contains right at inside
    rw [assigned.trackInitial] at inside
    exact inside
  have rightNear : normSq (anchor.value - right) ≤ anchor.lower / 8 := by
    rw [show anchor.value - right = -(right - anchor.value) by ring1, Basic.Canonical.normSq_neg]
    have scalar := assigned.bandNearSample right contained
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar.trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.pow_le_pow_direct assigned.radiusPositive.le assigned.radiusLeRequested 2)
        (by decide)).trans (band_small anchor.positive anchor.radiusSmall))
  calc
    _ ≤ 2 * (normSq (left - anchor.value) + normSq (anchor.value - right)) := by
      have scalar := Norm.Bounds.normSq_sub_le_via left anchor.value right
      simpa only [Norm.Basic.normSq_eq_canonical] using scalar
    _ ≤ 2 * (anchor.lower / 8 + anchor.lower / 8) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct (anchor.tailNear leftIndex order) rightNear) (by decide)
    _ = (1 / 2 : Coordinate) * anchor.lower := by
      apply Fraction.Field.mul_right_cancel_of_ne (show (8 : Coordinate) ≠ 0 by decide)
      calc
        _ = (anchor.lower / 8 * 8) * 4 := by ring1
        _ = anchor.lower * 4 := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
        _ = _ := by
          rw [Fraction.Field.div_eq_mul_inv_direct,
            show (2 : Coordinate)⁻¹ = (1 / 2 : Coordinate) from rfl]
          have cancel : (1 / 2 : Coordinate) * 8 = 4 := by decide
          calc
            _ = ((1 / 2 : Coordinate) * 8) * anchor.lower := by rw [cancel]; ring1
            _ = _ := by ring1
    _ ≤ 1 * anchor.lower :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) anchor.positive.le
    _ = source.apart.certificate.lowerSq := by rw [Fraction.Field.one_mul]; rfl

end Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
