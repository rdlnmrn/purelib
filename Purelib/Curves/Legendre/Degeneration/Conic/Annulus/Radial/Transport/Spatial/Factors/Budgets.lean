module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Factors
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Polynomial.Quadratic.Split
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Retained factor budgets on an original parallel spatial square

One normalized budget is computed on the supplied original source anchor's
known-root seed. The original prepared quarter's cofactor budget is reused
as its unchanged cache. Both budgets pay every physical point in the same
original sharp square; no source or target root is re-isolated or reattached.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {source : Transport.Reading actual first firstInside}

/-- The exact physical source square retains the original quarter reading and its labelled regularity. -/
@[expose] def sourceBox (anchor : Parameter.Anchor source.lift) : Box :=
  Clearance.box site parameter (Waist.direction quarter first) anchor.regular

/-- Compute a normalized movement budget on the identical retained original known-root seed.

One thirty-second of the original gap fourth power is above all normalized
movements in the sharp spatial square and below the source seed's internally
derived boundary clearance. The original owner and its box remain unchanged.
-/
def normalizedBudget (anchor : Parameter.Anchor source.lift) : FixedRootBoxBudget.Budget anchor.seed.owner :=
  FixedRootBoxBudget.Budget.acquire anchor.seed.owner
    ((1 / 32) * Norm.Basic.normSq (halfGap site parameter) ^ 2)
    (Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.sq_nonneg_direct _))
    ((Arithmetic.mul_lt_mul_of_pos_right_direct
      (by
        change (1 / 32 : Fraction.Rational) <
          ((729 : Nat) : Fraction.Rational) / ((16384 : Nat) : Fraction.Rational)
        rewrite [Fraction.Cast.natCast_eq_fromInt 729, Fraction.Cast.natCast_eq_fromInt 16384]
        decide +kernel)
      (Arithmetic.pow_pos_direct anchor.gapNorm_positive 2)).trans_le anchor.clearance_lower)

/-- The original normalized budget's retained movement is exactly one thirty-second of the gap fourth power. -/
theorem normalizedBudget_movement (anchor : Parameter.Anchor source.lift) :
    (normalizedBudget anchor).movement = (1 / 32) * Norm.Basic.normSq (halfGap site parameter) ^ 2 := by
  unfold normalizedBudget
  rfl

/-- One completed normalized budget and its whole original factory identity on the unchanged supplied source anchor. -/
@[expose] def Budgets (anchor : Parameter.Anchor source.lift) : Type :=
  { retained : FixedRootBoxBudget.Budget anchor.seed.owner // retained = normalizedBudget anchor }

namespace Budgets

variable {anchor : Parameter.Anchor source.lift}

/-- Retain a completed original normalized budget without acquiring it again. -/
@[expose] def ofCompleted (retained : FixedRootBoxBudget.Budget anchor.seed.owner)
    (retained_eq : retained = normalizedBudget anchor) : Budgets anchor := ⟨retained, retained_eq⟩

/-- Compute the normalized budget once while retaining the original source anchor and its owner as indices. -/
def build (anchor : Parameter.Anchor source.lift) : Budgets anchor :=
  let retained := normalizedBudget anchor
  ofCompleted retained rfl

/-- Read the complete original normalized budget retained by these physical factor channels. -/
@[expose] def normalized (budgets : Budgets anchor) : FixedRootBoxBudget.Budget anchor.seed.owner := budgets.val

/-- The normalized cache is the whole original factory on the identical retained source anchor and seed. -/
theorem normalized_eq (budgets : Budgets anchor) : budgets.normalized = normalizedBudget anchor := budgets.property

/-- Read the unchanged original quarter cofactor budget directly, without recomputing its owner or allowance. -/
@[expose] def unit (_budgets : Budgets anchor) : FixedRootBoxBudget.Budget actual.data.source := actual.data.budget

/-- The cofactor budget is the identical complete cache of the original supplied prepared quarter. -/
theorem unit_eq (budgets : Budgets anchor) : budgets.unit = actual.data.budget := rfl

/-- Every point of the same sharp spatial square pays the retained normalized budget internally. -/
theorem normalized_movement (budgets : Budgets anchor) {value : Canonical}
    (inside : (sourceBox anchor).Contains value) :
    Norm.Basic.normSq ((Parameter.sourcePoint site parameter (Waist.direction quarter first)).ordinate ^ 2 -
      Clearance.normalizedRadicand site parameter value) ≤ budgets.normalized.movement := by
  have actual := Clearance.normalized_movement_le site parameter (Waist.direction quarter first) anchor.regular inside
  rewrite [Norm.Bounds.normSq_sub_symm] at actual
  rewrite [budgets.normalized_eq, normalizedBudget_movement]
  exact actual.trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel : (Fraction.Cast.fromInt 3201 / Fraction.Cast.fromInt 131072 : Fraction.Rational) ≤ 1 / 32)
      (Arithmetic.sq_nonneg_direct _))

/-- Every point of the same spatial square pays the identical original quarter cofactor budget. -/
theorem unit_movement (budgets : Budgets anchor) {value : Canonical}
    (inside : (sourceBox anchor).Contains value) :
    Norm.Basic.normSq (UnitRoot.seed site ^ 2 - (unitPolynomial site).eval value) ≤ budgets.unit.movement := by
  rewrite [unit_eq, actual.data.movement_eq]
  exact Clearance.cofactor_movement_half site parameter (Waist.direction quarter first) anchor.regular
    actual.data.bound inside

/-- The original normalized quadratic remains nonzero throughout the same retained physical square. -/
theorem normalized_nonzero (_budgets : Budgets anchor) {value : Canonical}
    (inside : (sourceBox anchor).Contains value) : Clearance.normalizedRadicand site parameter value ≠ 0 := by
  have branches := Clearance.branch_lower site parameter (Waist.direction quarter first) anchor.regular inside
  have lowerNonnegative : 0 ≤ Norm.Basic.normSq (halfGap site parameter) / 64 :=
    Fraction.Order.Field.div_nonneg_direct (Norm.Basic.normSq_nonneg _) (by decide +kernel)
  have product := Arithmetic.mul_le_mul_direct branches.1 branches.2 lowerNonnegative
    (Norm.Basic.normSq_nonneg (value - criticalValue site))
  have formula := Polynomial.Quadratic.Split.product_eq (criticalValue site) parameter value
    (by decide +kernel : (2 : Canonical) ≠ 0)
  change (value - criticalValue site) * (value - parameter) =
    Clearance.normalizedRadicand site parameter value at formula
  rewrite [← Norm.Basic.normSq_mul, formula] at product
  have positive : 0 < (Norm.Basic.normSq (halfGap site parameter) / 64) *
      (Norm.Basic.normSq (halfGap site parameter) / 64) :=
    Arithmetic.mul_pos_direct
      (Fraction.Order.Field.div_pos_direct anchor.gapNorm_positive (by decide +kernel))
      (Fraction.Order.Field.div_pos_direct anchor.gapNorm_positive (by decide +kernel))
  intro zero
  rewrite [zero, show Norm.Basic.normSq (0 : Canonical) = 0 by decide +kernel] at product
  exact (positive.trans_le product).ne' rfl

/-- The original remaining affine factor remains nonzero throughout the identical retained spatial square. -/
theorem unit_nonzero (_budgets : Budgets anchor) {value : Canonical}
    (inside : (sourceBox anchor).Contains value) : (unitPolynomial site).eval value ≠ 0 := by
  have lower := Clearance.cofactor_lower site parameter (Waist.direction quarter first) anchor.regular
    actual.data.bound inside
  intro zero
  rewrite [zero, show Norm.Basic.normSq (0 : Canonical) = 0 by decide +kernel] at lower
  exact (by decide +kernel : ¬((1 / 16 : Fraction.Rational) ≤ 0)) lower

end Budgets

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors
