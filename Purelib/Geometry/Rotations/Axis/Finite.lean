module

public import Purelib.Geometry.Rotations.Axis.Parameters
public import Purelib.Algebra.Field.Finite.Odd.SquareFibers
import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Inverse
import Purelib.Algebra.Field.Characteristic.Nonzero
-- The exposed amount certificate retains the original Boolean conjunction proof.
public import Purelib.Data.Bool.Decide
import Purelib.Data.List.Bijection
import Purelib.Data.List.CountWhere
public import Purelib.Data.List.Filter
import Purelib.Data.List.Map
import Purelib.Data.List.Fold
import Purelib.Data.List.Nodup
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Subtraction
import Purelib.Tactic.Ring

/-!
# Admissible amounts on an axis over a displayed odd finite field

The original field carrier and square-root table enumerate the half spreads
supported by a supplied nonzero axis quadrance. Each accepted amount retains
its original nonzero square certificate. The scalar anchor parameter maps
two opposite nonzero scales to each amount; its forbidden denominator is
controlled by the square roots of the negative original axis quadrance.
-/

public section

namespace Purelib.Geometry.Rotations.Axis.Parameters

open Purelib.Algebra.Field
open Purelib.Algebra.Field.Characteristic
open Purelib.Algebra.Field.Finite.Odd.Presentation (FiniteOddFieldPresentation)
open Purelib.Algebra.Field.Squares
open Purelib.Data.Bool
open Purelib.Data.List

open scoped Purelib.Data.List.Membership Purelib.Data.Nat

variable {K : Type*} [ExplicitField K]

/-- The cap denominator of the scalar anchor with the supplied original axis quadrance. -/
@[expose] def scaleDenominator (quadrance scale : K) : K := 1 + scale ^ 2 * quadrance

/-- Read the half spread of the scalar anchor with the supplied original axis quadrance. -/
@[expose] def halfSpreadOfScale (quadrance scale : K) : K := scale ^ 2 * quadrance / scaleDenominator quadrance scale

/-- The half spread's unit complement is the reciprocal of the same nonzero scale denominator. -/
theorem one_sub_halfSpreadOfScale (quadrance scale : K) (defined : scaleDenominator quadrance scale ≠ 0) :
    1 - halfSpreadOfScale quadrance scale = (scaleDenominator quadrance scale)⁻¹ := by
  have cancel := ExplicitField.mul_inv_cancel _ defined
  unfold halfSpreadOfScale
  rw [ExplicitField.div_eq_mul_inv]
  calc
    _ = (scaleDenominator quadrance scale) * (scaleDenominator quadrance scale)⁻¹ -
        scale ^ 2 * quadrance * (scaleDenominator quadrance scale)⁻¹ := by rw [cancel]
    _ = _ := by unfold scaleDenominator; ring1

/-- A nonzero scalar anchor on a non-null axis has nonzero half spread when its original denominator is nonzero. -/
theorem halfSpreadOfScale_nonzero (quadrance scale : K) (quadranceNonzero : quadrance ≠ 0)
    (scaleNonzero : scale ≠ 0) (defined : scaleDenominator quadrance scale ≠ 0) :
    halfSpreadOfScale quadrance scale ≠ 0 :=
  ExplicitField.div_ne_zero
    (ExplicitField.mul_ne_zero (ExplicitField.square_nonzero_of_nonzero scaleNonzero) quadranceNonzero) defined

/-- The original scalar cap half spread differs from one at every defined scale. -/
theorem halfSpreadOfScale_ne_one (quadrance scale : K) (defined : scaleDenominator quadrance scale ≠ 0) :
    halfSpreadOfScale quadrance scale ≠ 1 := by
  intro one
  have complement := one_sub_halfSpreadOfScale quadrance scale defined
  rw [one, sub_self] at complement
  exact ExplicitField.inv_ne_zero defined complement.symm

/-- The scalar cap half spread has the original scale's half-twist equation. -/
theorem halfTwist_halfSpreadOfScale (quadrance scale : K) (defined : scaleDenominator quadrance scale ≠ 0) :
    scale ^ 2 * quadrance = halfSpreadOfScale quadrance scale / (1 - halfSpreadOfScale quadrance scale) := by
  rw [one_sub_halfSpreadOfScale quadrance scale defined]
  have inverseInverse : ((scaleDenominator quadrance scale)⁻¹)⁻¹ = scaleDenominator quadrance scale := by
    apply Inverse.inverse_eq_of_mul_eq_one (ExplicitField.inv_ne_zero defined)
    exact (mul_comm _ _).trans (ExplicitField.mul_inv_cancel _ defined)
  unfold halfSpreadOfScale
  rw [ExplicitField.div_eq_mul_inv, ExplicitField.div_eq_mul_inv, inverseInverse]
  calc
    _ = scale ^ 2 * quadrance * ((scaleDenominator quadrance scale) * (scaleDenominator quadrance scale)⁻¹) := by
      rw [ExplicitField.mul_inv_cancel _ defined, mul_one]
    _ = _ := by ring1

/-- A supplied half-twist solution has nonzero original scale denominator and reads back the requested amount. -/
theorem halfSpreadOfScale_of_halfTwist (quadrance amount scale : K) (quadranceNonzero : quadrance ≠ 0)
    (amountNotOne : amount ≠ 1) (halfTwist : scale ^ 2 * quadrance = amount / (1 - amount)) :
    scaleDenominator quadrance scale ≠ 0 ∧ halfSpreadOfScale quadrance scale = amount := by
  have complementNonzero := ExplicitField.one_sub_ne_zero_of_ne_one amountNotOne
  have product : scaleDenominator quadrance scale * (1 - amount) = 1 := by
    unfold scaleDenominator
    rw [halfTwist]
    calc
      _ = (1 - amount) + (amount / (1 - amount)) * (1 - amount) := by ring1
      _ = 1 := by rw [ExplicitField.div_mul_cancel _ complementNonzero]; ring1
  have denominatorNonzero : scaleDenominator quadrance scale ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at product
    exact (Nonzero.one_ne_zero_of_nonzero quadranceNonzero) product.symm
  refine ⟨denominatorNonzero, ?_⟩
  have inverseEq := Inverse.inverse_eq_of_mul_eq_one denominatorNonzero product
  unfold halfSpreadOfScale
  rw [ExplicitField.div_eq_mul_inv, inverseEq, halfTwist, ExplicitField.div_mul_cancel _ complementNonzero]

section Enumeration

variable (presentation : FiniteOddFieldPresentation K)

/-- Test whether the original nonzero scalar anchor has a nonzero cap denominator. -/
@[expose] def admissibleScale (quadrance scale : K) : Bool := by
  letI : DecidableEq K := presentation.eqDecidable
  exact decide (scale ≠ 0 ∧ scaleDenominator quadrance scale ≠ 0)

/-- Enumerate all admissible scalar anchors in the original carrier order. -/
@[expose] def admissibleScales (quadrance : K) : List K :=
  presentation.carrier.filter (admissibleScale presentation quadrance)

/-- Test the nonendpoint half-spread condition using the original cached square-value table. -/
@[expose] def admissibleAmount (quadrance amount : K) : Bool := by
  letI : DecidableEq K := presentation.eqDecidable
  exact decide (amount ≠ 0 ∧ amount ≠ 1) && decide (squareValue quadrance amount ∈ presentation.squareValues)

/-- Enumerate the nonendpoint square-condition amounts in the original carrier order. -/
@[expose] def admissibleAmounts (quadrance : K) : List K :=
  presentation.carrier.filter (admissibleAmount presentation quadrance)

/-- The original finite scalar-anchor list contains exactly the nonzero scales with nonzero original denominators. -/
theorem mem_admissibleScales_iff (quadrance scale : K) :
    scale ∈ admissibleScales presentation quadrance ↔ scale ≠ 0 ∧ scaleDenominator quadrance scale ≠ 0 := by
  letI : DecidableEq K := presentation.eqDecidable
  constructor
  · intro member
    exact of_decide_eq_true (Filter.mem_filter.mp member).2
  · intro accepted
    exact Filter.mem_filter.mpr ⟨presentation.carrierComplete scale, decide_eq_true accepted⟩

/-- The original amount list contains exactly the nonendpoints with the original prescribed-axis square condition. -/
theorem mem_admissibleAmounts_iff (quadrance amount : K) :
    amount ∈ admissibleAmounts presentation quadrance ↔
      amount ≠ 0 ∧ amount ≠ 1 ∧ ∃ root : K, root ^ 2 = squareValue quadrance amount := by
  letI : DecidableEq K := presentation.eqDecidable
  constructor
  · intro member
    have both := (Decide.and_true_iff _ _).mp (Filter.mem_filter.mp member).2
    have endpoints : amount ≠ 0 ∧ amount ≠ 1 := of_decide_eq_true both.1
    exact ⟨endpoints.1, endpoints.2,
      (presentation.mem_squareValues_iff_hasSquareRoot _).mp (of_decide_eq_true both.2)⟩
  · rintro ⟨nonzero, notOne, root⟩
    apply Filter.mem_filter.mpr
    refine ⟨presentation.carrierComplete amount, ?_⟩
    apply (Decide.and_true_iff _ _).mpr
    exact ⟨decide_eq_true ⟨nonzero, notOne⟩,
      decide_eq_true ((presentation.mem_squareValues_iff_hasSquareRoot _).mpr root)⟩

/-- Read the original cached root as a nonzero prescribed-axis certificate for an enumerated amount.

The original amount membership proves both nonendpoint conditions. The
original square table supplies its retained root, and the nonzero original
axis quadrance ensures that root is nonzero.
-/
@[expose] def amountCertificate (quadrance amount : K) (quadranceNonzero : quadrance ≠ 0)
    (member : amount ∈ admissibleAmounts presentation quadrance) :
    Witness.NonzeroSquare (squareValue quadrance amount) := by
  letI : DecidableEq K := presentation.eqDecidable
  let retained := (Filter.mem_filter.mp member).2
  let both := (Decide.and_true_iff _ _).mp retained
  let endpoints : amount ≠ 0 ∧ amount ≠ 1 := of_decide_eq_true both.1
  let squareMember : squareValue quadrance amount ∈ presentation.squareValues := of_decide_eq_true both.2
  exact
  { root := presentation.squareRoot (squareValue quadrance amount)
    square := presentation.squareRoot_spec _ squareMember
    rootNonzero := by
      intro zero
      have square := presentation.squareRoot_spec _ squareMember
      rw [zero, zero_pow (by decide)] at square
      exact ExplicitField.mul_ne_zero (ExplicitField.mul_ne_zero quadranceNonzero endpoints.1)
        (ExplicitField.one_sub_ne_zero_of_ne_one endpoints.2) square.symm }

/-- Each admissible original scalar anchor reads back an amount in the original supported-amount enumeration. -/
theorem halfSpreadOfScale_mem (quadrance scale : K) (quadranceNonzero : quadrance ≠ 0)
    (member : scale ∈ admissibleScales presentation quadrance) :
    halfSpreadOfScale quadrance scale ∈ admissibleAmounts presentation quadrance := by
  have accepted := (mem_admissibleScales_iff presentation quadrance scale).mp member
  have notOne := halfSpreadOfScale_ne_one quadrance scale accepted.2
  let certificate := squareCertificate quadrance (halfSpreadOfScale quadrance scale) scale
    accepted.1 quadranceNonzero notOne (halfTwist_halfSpreadOfScale quadrance scale accepted.2)
  exact (mem_admissibleAmounts_iff presentation quadrance _).mpr
    ⟨halfSpreadOfScale_nonzero quadrance scale quadranceNonzero accepted.1 accepted.2, notOne,
      certificate.root, certificate.square⟩

/-- Every supported original amount has the root-derived anchor scale in the original admissible-scale enumeration. -/
theorem anchorScale_mem (quadrance amount : K) (quadranceNonzero : quadrance ≠ 0)
    (member : amount ∈ admissibleAmounts presentation quadrance) :
    let certificate := amountCertificate presentation quadrance amount quadranceNonzero member
    anchorScale quadrance amount certificate ∈ admissibleScales presentation quadrance ∧
      halfSpreadOfScale quadrance (anchorScale quadrance amount certificate) = amount := by
  let certificate := amountCertificate presentation quadrance amount quadranceNonzero member
  have accepted := (mem_admissibleAmounts_iff presentation quadrance amount).mp member
  refine ⟨(mem_admissibleScales_iff presentation quadrance _).mpr ?_, ?_⟩
  · exact ⟨anchorScale_nonzero quadrance amount certificate quadranceNonzero accepted.2.1,
      denominator_nonzero quadrance amount certificate quadranceNonzero accepted.2.1⟩
  · exact halfSpread quadrance amount certificate quadranceNonzero accepted.2.1

/-- The square of a scalar anchor with the specified nonendpoint half spread. -/
private def scaleSquare (quadrance amount : K) : K := amount / (1 - amount) / quadrance

/-- A nonzero nonendpoint amount on a non-null axis requires a nonzero scale square. -/
private theorem scaleSquare_nonzero (quadrance amount : K) (quadranceNonzero : quadrance ≠ 0)
    (amountNonzero : amount ≠ 0) (amountNotOne : amount ≠ 1) : scaleSquare quadrance amount ≠ 0 :=
  ExplicitField.div_ne_zero
    (ExplicitField.div_ne_zero amountNonzero (ExplicitField.one_sub_ne_zero_of_ne_one amountNotOne)) quadranceNonzero

/-- Count the admissible original scales reading back the supplied amount. -/
private def scaleFiber (quadrance amount scale : K) : Bool := by
  letI : DecidableEq K := presentation.eqDecidable
  exact admissibleScale presentation quadrance scale && decide (halfSpreadOfScale quadrance scale = amount)

/-- The original scalar fiber accepts precisely the admissible scales with the requested readback. -/
private theorem scaleFiber_true_iff (quadrance amount scale : K) :
    scaleFiber presentation quadrance amount scale = true ↔
      scale ≠ 0 ∧ scaleDenominator quadrance scale ≠ 0 ∧ halfSpreadOfScale quadrance scale = amount := by
  letI : DecidableEq K := presentation.eqDecidable
  constructor
  · intro accepted
    have both := (Decide.and_true_iff _ _).mp accepted
    have valid : scale ≠ 0 ∧ scaleDenominator quadrance scale ≠ 0 := of_decide_eq_true both.1
    exact ⟨valid.1, valid.2, of_decide_eq_true both.2⟩
  · rintro ⟨nonzero, defined, readback⟩
    exact (Decide.and_true_iff _ _).mpr ⟨decide_eq_true ⟨nonzero, defined⟩, decide_eq_true readback⟩

/-- At a nonendpoint amount, the original scalar fiber is exactly a square-root fiber. -/
private theorem scaleFiber_eq_square (quadrance amount scale : K) (quadranceNonzero : quadrance ≠ 0)
    (amountNonzero : amount ≠ 0) (amountNotOne : amount ≠ 1) :
    scaleFiber presentation quadrance amount scale =
      (letI : DecidableEq K := presentation.eqDecidable; decide (scale ^ 2 = scaleSquare quadrance amount)) := by
  letI : DecidableEq K := presentation.eqDecidable
  apply Decide.eq_of_true_iff
  constructor
  · intro accepted
    have valid := (scaleFiber_true_iff presentation quadrance amount scale).mp accepted
    apply decide_eq_true
    apply Inverse.eq_div_of_mul_eq quadranceNonzero
    have halfTwist := halfTwist_halfSpreadOfScale quadrance scale valid.2.1
    rw [valid.2.2] at halfTwist
    exact halfTwist
  · intro squareAccepted
    have square : scale ^ 2 = scaleSquare quadrance amount := of_decide_eq_true squareAccepted
    have scaleNonzero : scale ≠ 0 := by
      intro zero
      rw [zero, zero_pow (by decide)] at square
      exact scaleSquare_nonzero quadrance amount quadranceNonzero amountNonzero amountNotOne square.symm
    have halfTwist : scale ^ 2 * quadrance = amount / (1 - amount) := by
      rw [square]
      exact ExplicitField.div_mul_cancel _ quadranceNonzero
    have readback := halfSpreadOfScale_of_halfTwist quadrance amount scale quadranceNonzero amountNotOne halfTwist
    exact (scaleFiber_true_iff presentation quadrance amount scale).mpr ⟨scaleNonzero, readback.1, readback.2⟩

/-- Every accepted original amount has precisely two admissible opposite scalar anchors. -/
private theorem scaleFiber_count_of_member (quadrance amount : K) (quadranceNonzero : quadrance ≠ 0)
    (member : amount ∈ admissibleAmounts presentation quadrance) :
    CountWhere.listCountWhere presentation.carrier (scaleFiber presentation quadrance amount) = 2 := by
  letI : DecidableEq K := presentation.eqDecidable
  have endpoints := (mem_admissibleAmounts_iff presentation quadrance amount).mp member
  let certificate := amountCertificate presentation quadrance amount quadranceNonzero member
  have square : anchorScale quadrance amount certificate ^ 2 = scaleSquare quadrance amount :=
    Inverse.eq_div_of_mul_eq quadranceNonzero
      (anchorScale_quadrance quadrance amount certificate quadranceNonzero endpoints.2.1)
  have same := CountWhere.listCountWhere_congr presentation.carrier
    (scaleFiber presentation quadrance amount) (fun scale => decide (scale ^ 2 = scaleSquare quadrance amount))
    (fun scale _ => scaleFiber_eq_square presentation quadrance amount scale quadranceNonzero
      endpoints.1 endpoints.2.1)
  exact same.trans (presentation.squareRootCount_of_nonzero_square (scaleSquare quadrance amount)
    (anchorScale quadrance amount certificate)
    (scaleSquare_nonzero quadrance amount quadranceNonzero endpoints.1 endpoints.2.1) square)

/-- An amount outside the original accepted list has no admissible scalar anchor. -/
private theorem scaleFiber_count_of_not_member (quadrance amount : K) (quadranceNonzero : quadrance ≠ 0)
    (notMember : amount ∉ admissibleAmounts presentation quadrance) :
    CountWhere.listCountWhere presentation.carrier (scaleFiber presentation quadrance amount) = 0 := by
  apply CountWhere.listCountWhere_eq_zero_of_reject
  intro scale _
  apply Decide.bool_eq_false_of_not_eq_true
  intro accepted
  have valid := (scaleFiber_true_iff presentation quadrance amount scale).mp accepted
  have member := halfSpreadOfScale_mem presentation quadrance scale quadranceNonzero
    ((mem_admissibleScales_iff presentation quadrance scale).mpr ⟨valid.1, valid.2.1⟩)
  rw [valid.2.2] at member
  exact notMember member

/-- The scalar fiber count is two for each accepted amount and zero otherwise. -/
private theorem scaleFiber_count (quadrance amount : K) (quadranceNonzero : quadrance ≠ 0) :
    CountWhere.listCountWhere presentation.carrier (scaleFiber presentation quadrance amount) =
      if admissibleAmount presentation quadrance amount then 2 else 0 := by
  cases accepted : admissibleAmount presentation quadrance amount with
  | true =>
      exact scaleFiber_count_of_member presentation quadrance amount quadranceNonzero
        (Filter.mem_filter.mpr ⟨presentation.carrierComplete amount, accepted⟩)
  | false =>
      apply scaleFiber_count_of_not_member presentation quadrance amount quadranceNonzero
      intro member
      have valid := (Filter.mem_filter.mp member).2
      rw [accepted] at valid
      exact Bool.noConfusion valid

/-- Summing one scalar's readback fiber over the original carrier counts that scalar once exactly when admissible. -/
private theorem amountFiber_count (quadrance scale : K) :
    CountWhere.listCountWhere presentation.carrier (fun amount => scaleFiber presentation quadrance amount scale) =
      if admissibleScale presentation quadrance scale then 1 else 0 := by
  letI : DecidableEq K := presentation.eqDecidable
  cases accepted : admissibleScale presentation quadrance scale with
  | false =>
      apply CountWhere.listCountWhere_eq_zero_of_reject
      intro amount _
      unfold scaleFiber
      rw [accepted, Bool.false_and]
  | true =>
      have same := CountWhere.listCountWhere_congr presentation.carrier
        (fun amount => scaleFiber presentation quadrance amount scale)
        (fun amount => decide (amount = halfSpreadOfScale quadrance scale)) (by
          intro amount _
          unfold scaleFiber
          rw [accepted, Bool.true_and]
          apply Decide.eq_of_true_iff
          exact ⟨fun valid => decide_eq_true (of_decide_eq_true valid).symm,
            fun valid => decide_eq_true (of_decide_eq_true valid).symm⟩)
      exact same.trans (CountWhere.listCountWhere_eq_one_of_eq_target presentation.eqDecidable
        presentation.carrier presentation.carrierNodup (halfSpreadOfScale quadrance scale)
        (presentation.carrierComplete _))

/-- The admissible scalar-anchor list has twice the length of the original admissible-amount list.

The finite double count uses each scale's unique readback and each accepted
amount's two original opposite scales. Both sides use the original carrier.
-/
theorem admissibleScales_length (quadrance : K) (quadranceNonzero : quadrance ≠ 0) :
    (admissibleScales presentation quadrance).length =
      (admissibleAmounts presentation quadrance).length + (admissibleAmounts presentation quadrance).length := by
  have swap := CountWhere.listCountWhere_sum_swap presentation.carrier presentation.carrier
    (fun scale amount => scaleFiber presentation quadrance amount scale)
  have rows := Map.map_congr_left (values := presentation.carrier)
    (fun scale _ => amountFiber_count presentation quadrance scale)
  have columns := Map.map_congr_left (values := presentation.carrier)
    (fun amount _ => scaleFiber_count presentation quadrance amount quadranceNonzero)
  rw [rows, columns] at swap
  have doubled := Map.map_congr_left (values := presentation.carrier) (by
    intro amount _
    show (if admissibleAmount presentation quadrance amount then 2 else 0) =
      (if admissibleAmount presentation quadrance amount then 1 else 0) +
        (if admissibleAmount presentation quadrance amount then 1 else 0)
    cases admissibleAmount presentation quadrance amount <;> rfl)
  rw [doubled, Fold.foldr_add_map_pointwise_add,
    ← CountWhere.listCountWhere_eq_foldr_indicators,
    ← CountWhere.listCountWhere_eq_foldr_indicators] at swap
  exact swap

/-- Enumerate the original scalar anchors whose cap denominator vanishes. -/
@[expose] def denominatorZeroScales (quadrance : K) : List K := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.carrier.filter (fun scale => decide (scaleDenominator quadrance scale = 0))

/-- A vanishing original cap denominator gives a square root of the negative original axis quadrance. -/
private theorem square_of_denominator_zero (quadrance scale : K)
    (zero : scaleDenominator quadrance scale = 0) : (quadrance * scale) ^ 2 = -quadrance := by
  calc
    _ = (scaleDenominator quadrance scale - 1) * quadrance := by unfold scaleDenominator; ring1
    _ = -quadrance := by rw [zero]; ring1

/-- Dividing a root of the negative original axis quadrance by that quadrance gives a vanishing cap denominator. -/
private theorem denominator_zero_of_square (quadrance root : K) (quadranceNonzero : quadrance ≠ 0)
    (square : root ^ 2 = -quadrance) : scaleDenominator quadrance (root / quadrance) = 0 := by
  have cancel := ExplicitField.mul_inv_cancel quadrance quadranceNonzero
  calc
    _ = (quadrance + root ^ 2 * (quadrance * quadrance⁻¹)) * quadrance⁻¹ := by
      unfold scaleDenominator
      rw [ExplicitField.div_eq_mul_inv]
      rw [← cancel]
      ring1
    _ = (quadrance + root ^ 2) * quadrance⁻¹ := by rw [cancel, mul_one]
    _ = 0 := by rw [square]; ring1

/-- The forbidden original scales correspond to the original roots of the negative axis quadrance. -/
private def denominatorSquareRootBijection (quadrance : K) (quadranceNonzero : quadrance ≠ 0) :
    Bijection.ListBijection (denominatorZeroScales presentation quadrance)
      (presentation.squareRootFiber (-quadrance)) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact
  { forward := fun scale => quadrance * scale
    backward := fun root => root / quadrance
    forward_mem := by
      intro scale member
      apply (presentation.mem_squareRootFiber_iff _ _).mpr
      exact square_of_denominator_zero quadrance scale (of_decide_eq_true (Filter.mem_filter.mp member).2)
    backward_mem := by
      intro root member
      apply Filter.mem_filter.mpr
      exact ⟨presentation.carrierComplete _, decide_eq_true (denominator_zero_of_square quadrance root quadranceNonzero
        ((presentation.mem_squareRootFiber_iff _ _).mp member))⟩
    backward_forward := by
      intro scale _
      rw [mul_comm quadrance scale]
      exact ExplicitField.mul_div_cancel_right scale quadrance quadranceNonzero
    forward_backward := by
      intro root _
      rw [mul_comm quadrance (root / quadrance)]
      exact ExplicitField.div_mul_cancel root quadranceNonzero }

/-- The forbidden-scale count equals the original square-root count of the negative original quadrance. -/
theorem denominatorZeroScales_length (quadrance : K) (quadranceNonzero : quadrance ≠ 0) :
    (denominatorZeroScales presentation quadrance).length = presentation.squareRootCount (-quadrance) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact Bijection.ListBijection.length_eq (denominatorSquareRootBijection presentation quadrance quadranceNonzero)
    (Filter.pairwise_filter _ presentation.carrierNodup) (presentation.squareRootFiber_nodup _)

/-- Rejected original scales consist of zero and the disjoint vanishing-denominator scales. -/
private theorem rejectedScale_indicator (quadrance scale : K) (quadranceNonzero : quadrance ≠ 0) :
    (if !admissibleScale presentation quadrance scale then 1 else 0) =
      (letI : DecidableEq K := presentation.eqDecidable
       (if decide (scale = 0) then 1 else 0) + (if decide (scaleDenominator quadrance scale = 0) then 1 else 0)) := by
  letI : DecidableEq K := presentation.eqDecidable
  change (if !admissibleScale presentation quadrance scale then 1 else 0) =
    (if decide (scale = 0) then 1 else 0) + (if decide (scaleDenominator quadrance scale = 0) then 1 else 0)
  cases presentation.eqDecidable scale 0 with
  | isTrue zero =>
      have defined : scaleDenominator quadrance scale ≠ 0 := by
        rw [zero]
        change 1 + (0 : K) ^ 2 * quadrance ≠ 0
        rw [zero_pow (by decide), zero_mul, add_zero]
        exact Nonzero.one_ne_zero_of_nonzero quadranceNonzero
      have rejected : admissibleScale presentation quadrance scale = false :=
        decide_eq_false (fun accepted => accepted.1 zero)
      rw [rejected, Bool.not_false, decide_eq_true zero, decide_eq_false defined]
      rfl
  | isFalse nonzero =>
      cases presentation.eqDecidable (scaleDenominator quadrance scale) 0 with
      | isTrue zero =>
          have rejected : admissibleScale presentation quadrance scale = false :=
            decide_eq_false (fun accepted => accepted.2 zero)
          rw [rejected, Bool.not_false, decide_eq_false nonzero, decide_eq_true zero]
          rfl
      | isFalse defined =>
          have accepted : admissibleScale presentation quadrance scale = true := decide_eq_true ⟨nonzero, defined⟩
          rw [accepted, Bool.not_true, decide_eq_false nonzero, decide_eq_false defined]
          rfl

/-- The original carrier is partitioned by admissible scales, forbidden scales and the zero scale. -/
theorem admissibleScales_partition (quadrance : K) (quadranceNonzero : quadrance ≠ 0) :
    (admissibleScales presentation quadrance).length + presentation.squareRootCount (-quadrance) + 1 =
      presentation.carrier.length := by
  letI : DecidableEq K := presentation.eqDecidable
  have partition := CountWhere.listCountWhere_add_complement presentation.carrier
    (admissibleScale presentation quadrance)
  have indicators := Map.map_congr_left (values := presentation.carrier)
    (fun scale _ => rejectedScale_indicator presentation quadrance scale quadranceNonzero)
  rw [CountWhere.listCountWhere_eq_foldr_indicators presentation.carrier
    (fun scale => !admissibleScale presentation quadrance scale), indicators,
    Fold.foldr_add_map_pointwise_add, ← CountWhere.listCountWhere_eq_foldr_indicators,
    ← CountWhere.listCountWhere_eq_foldr_indicators,
    CountWhere.listCountWhere_eq_one_of_eq_target presentation.eqDecidable presentation.carrier
      presentation.carrierNodup 0 (presentation.carrierComplete 0)] at partition
  have forbidden := denominatorZeroScales_length presentation quadrance quadranceNonzero
  change CountWhere.listCountWhere presentation.carrier
    (fun scale => decide (scaleDenominator quadrance scale = 0)) = _ at forbidden
  rw [forbidden, Nat.add_comm 1, ← Nat.add_assoc] at partition
  exact partition

/-- Count the original supported nonendpoint amounts by the original negative-quadrance square-root table.

Each supported amount has two opposite original scales. The excluded scales
are zero and the roots of the negative quadrance after division by the same
nonzero quadrance. This gives the count without changing the field enumeration.
-/
theorem admissibleAmounts_length (quadrance : K) (quadranceNonzero : quadrance ≠ 0) :
    (admissibleAmounts presentation quadrance).length =
      (presentation.carrier.length - (presentation.squareRootCount (-quadrance) + 1)) / 2 := by
  have partition := admissibleScales_partition presentation quadrance quadranceNonzero
  rw [admissibleScales_length presentation quadrance quadranceNonzero, Nat.add_assoc] at partition
  have twice : 2 * (admissibleAmounts presentation quadrance).length =
      presentation.carrier.length - (presentation.squareRootCount (-quadrance) + 1) := by
    calc
      _ = (admissibleAmounts presentation quadrance).length + (admissibleAmounts presentation quadrance).length :=
        Nat.two_mul _
      _ = _ := by
        rw [← partition]
        exact (Purelib.Data.Nat.Subtraction.add_sub_cancel_right _ _).symm
  rw [← twice]
  exact (Purelib.Data.Nat.Division.mul_div_cancel_left _ (by decide : 0 < 2)).symm

/-- A square negative original axis quadrance permits precisely the field-size-minus-three half count. -/
theorem admissibleAmounts_length_of_square (quadrance root : K) (quadranceNonzero : quadrance ≠ 0)
    (square : root ^ 2 = -quadrance) :
    (admissibleAmounts presentation quadrance).length = (presentation.carrier.length - 3) / 2 := by
  have negativeNonzero : -quadrance ≠ 0 := by
    intro zero
    have original := congrArg (fun value => -value) zero
    rw [neg_neg, neg_zero] at original
    exact quadranceNonzero original
  rw [admissibleAmounts_length presentation quadrance quadranceNonzero,
    presentation.squareRootCount_of_nonzero_square (-quadrance) root negativeNonzero square]

/-- A nonsquare negative original axis quadrance permits precisely the field-size-minus-one half count. -/
theorem admissibleAmounts_length_of_nonsquare (quadrance : K) (quadranceNonzero : quadrance ≠ 0)
    (noRoot : ∀ root : K, root ^ 2 ≠ -quadrance) :
    (admissibleAmounts presentation quadrance).length = (presentation.carrier.length - 1) / 2 := by
  rw [admissibleAmounts_length presentation quadrance quadranceNonzero,
    presentation.squareRootCount_of_nonsquare (-quadrance) noRoot]

end Enumeration

end Purelib.Geometry.Rotations.Axis.Parameters
