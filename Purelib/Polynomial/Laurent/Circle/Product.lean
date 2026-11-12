module

public import Purelib.Polynomial.Laurent.Circle
public import Purelib.Polynomial.Laurent.Normalization.Product
import Purelib.Polynomial.Winding.Circle.Operations
import Purelib.Polynomial.Winding.Circle.Comparison
import Purelib.Data.Int.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Independent circle comparison for actual Laurent products

Both original inputs and their independent circle comparisons remain the
parents. Their actual raw product is normalized once and receives its own
original chart-event reading and root inventory. The common extra shift
accounts for all cancelled pole powers before the index is compared.
-/

public section

namespace Purelib.Polynomial.Laurent.Circle.Product

open Purelib.Data
open Purelib.Polynomial.Laurent.Basic (LaurentPolynomial)
open Purelib.Polynomial.Laurent.Normalization (Normalized)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Polynomial.Clearance.Circle (Certificate)

variable {left right : LaurentPolynomial} {leftResult : Normalized left} {rightResult : Normalized right}
variable {leftPaths : Boundary.Substitutions leftResult.polynomial}
variable {rightPaths : Boundary.Substitutions rightResult.polynomial}
variable {leftClearance : Boundary.Clearance leftPaths} {rightClearance : Boundary.Clearance rightPaths}

/-- The same two original margins pay for the actual normalized product without a new boundary search. -/
@[expose] def polynomialMargin (product : Arithmetic.Product left right)
    (leftMargin : Certificate leftResult.polynomial) (rightMargin : Certificate rightResult.polynomial)
    (normalized : Normalized product.symbol) : Certificate normalized.polynomial :=
  { bound := leftMargin.bound * rightMargin.bound
    positive := Rat.Fraction.Order.Arithmetic.mul_pos_direct leftMargin.positive rightMargin.positive
    lower := by
      intro point unit
      rw [product.polynomial_normSq leftResult rightResult normalized point unit]
      exact Rat.Fraction.Order.Arithmetic.mul_le_mul_direct
        (leftMargin.lower point unit) (rightMargin.lower point unit) rightMargin.positive.le
        (Gaussian.Norm.Basic.normSq_nonneg _) }

/-- Independent raw product winding loses exactly four times the extra common polynomializing shift. -/
theorem polynomial_raw_add (product : Arithmetic.Product left right)
    (leftMargin : Certificate leftResult.polynomial) (rightMargin : Certificate rightResult.polynomial)
    (normalized : Normalized product.symbol) (paths : Boundary.Substitutions normalized.polynomial) :
    Winding.Circle.raw paths = Winding.Circle.raw leftPaths + Winding.Circle.raw rightPaths -
      4 * ((leftResult.poleOrder + rightResult.poleOrder - normalized.poleOrder : Nat) : Int) := by
  let extra := leftResult.poleOrder + rightResult.poleOrder - normalized.poleOrder
  let densePaths := Boundary.Substitutions.prepare (leftResult.polynomial * rightResult.polynomial)
  let shiftedPaths := Boundary.Substitutions.prepare (DensePolynomial.shift extra normalized.polynomial)
  have agreement := Winding.Circle.Comparison.raw_eq_of_eval_eq (leftMargin.product rightMargin)
    densePaths shiftedPaths (fun point _ => by
      rewrite [product.polynomial_identity leftResult rightResult normalized]
      rfl)
  have inputs := Winding.Circle.raw_mul leftMargin rightMargin leftPaths rightPaths densePaths
  have output := Winding.Circle.raw_shift (polynomialMargin product leftMargin rightMargin normalized)
    paths extra shiftedPaths
  have balance := output.symm.trans (agreement.trans inputs)
  calc
    _ = (Winding.Circle.raw paths + 4 * (extra : Int)) - (extra : Int) * 4 := by ring1
    _ = (Winding.Circle.raw leftPaths + Winding.Circle.raw rightPaths) - (extra : Int) * 4 :=
      congrArg (fun reading : Int => reading - (extra : Int) * 4) balance
    _ = _ := by ring1

set_option genInjectivity false in
/-- The actual normalized product comparison retaining both original independent input comparisons.

The product normalization, boundary substitutions and margin are materialized
once. The result is the original independent circle constructor on those same
caches; its winding and inside count are not supplied by either input integer.
-/
structure Comparison (product : Arithmetic.Product left right)
    (leftComparison : Circle.Comparison leftResult leftPaths leftClearance)
    (rightComparison : Circle.Comparison rightResult rightPaths rightClearance) where
  /-- The actual normalization of this same retained original raw product. -/
  normalized : Normalized product.symbol
  /-- The normalization uses the original nonzero-product constructor. -/
  normalized_eq : normalized = product.normalize leftResult rightResult
  /-- The actual pole-power compensation retained from these same normalized parents. -/
  extraShift : Nat
  /-- The retained compensation is the actual common shift minus the minimal product pole order. -/
  extraShift_eq : extraShift = leftResult.poleOrder + rightResult.poleOrder - normalized.poleOrder
  /-- The once-computed original numerator substitutions of the normalized product. -/
  paths : Boundary.Substitutions normalized.polynomial
  /-- The original substitution constructor consumes this same cached polynomial. -/
  paths_eq : paths = Boundary.Substitutions.prepare normalized.polynomial
  /-- The whole-circle payment is obtained from the same two original input margins. -/
  margin : Certificate normalized.polynomial
  /-- The original product norm identity transports exactly these retained margin payments. -/
  margin_eq : margin = polynomialMargin product leftComparison.polynomial.margin.toCertificate
    rightComparison.polynomial.margin.toCertificate normalized
  /-- Both original circle charts inherit this same stored product margin. -/
  clearance : Boundary.Clearance paths
  /-- The stored original substitutions and margin produce this same clearance. -/
  clearance_eq : clearance = margin.onBoundary paths
  /-- The actual independent product phase reading and complete root inventory. -/
  result : Circle.Comparison normalized paths clearance
  /-- The original automatic circle comparison consumes these same retained product caches. -/
  result_eq : result = Circle.Comparison.prepare normalized paths clearance

constructive_injectivity Comparison

namespace Comparison

variable {product : Arithmetic.Product left right}
variable {leftComparison : Circle.Comparison leftResult leftPaths leftClearance}
variable {rightComparison : Circle.Comparison rightResult rightPaths rightClearance}

/-- Compute the actual normalized product's independent circle comparison with the original input margins. -/
@[expose] def prepare (product : Arithmetic.Product left right)
    (leftComparison : Circle.Comparison leftResult leftPaths leftClearance)
    (rightComparison : Circle.Comparison rightResult rightPaths rightClearance) :
    Comparison product leftComparison rightComparison :=
  let normalized := product.normalize leftResult rightResult
  let paths := Boundary.Substitutions.prepare normalized.polynomial
  let margin := polynomialMargin product leftComparison.polynomial.margin.toCertificate
    rightComparison.polynomial.margin.toCertificate normalized
  let clearance := margin.onBoundary paths
  let result := Circle.Comparison.prepare normalized paths clearance
  { normalized, normalized_eq := rfl
    extraShift := leftResult.poleOrder + rightResult.poleOrder - normalized.poleOrder, extraShift_eq := rfl
    paths, paths_eq := rfl, margin, margin_eq := rfl, clearance, clearance_eq := rfl, result, result_eq := rfl }

/-- The actual product numerator's independent raw reading includes the exact retained zero-shift compensation. -/
theorem polynomial_raw_eq (comparison : Comparison product leftComparison rightComparison) :
    Winding.Circle.raw comparison.paths = Winding.Circle.raw leftPaths + Winding.Circle.raw rightPaths -
      4 * (comparison.extraShift : Int) := by
  rw [comparison.extraShift_eq]
  exact polynomial_raw_add product leftComparison.polynomial.margin.toCertificate
    rightComparison.polynomial.margin.toCertificate comparison.normalized comparison.paths

/-- The independently computed original product winding is the sum of the two independent original input windings. -/
theorem winding_add (comparison : Comparison product leftComparison rightComparison) :
    comparison.result.reading.winding = leftComparison.reading.winding + rightComparison.reading.winding := by
  have productRaw := (comparison.result.reading.raw_eq.symm.trans
    (Purelib.RationalFunctions.Winding.Circle.raw_eq_sub comparison.result.paths.quotient
      comparison.clearance comparison.result.paths.denominatorClearance)).trans
    (congrArg₂ (fun numerator denominator : Int => numerator - denominator)
      comparison.polynomial_raw_eq comparison.result.paths.denominator_raw)
  have leftRaw := (leftComparison.reading.raw_eq.symm.trans
    (Purelib.RationalFunctions.Winding.Circle.raw_eq_sub leftComparison.paths.quotient
      leftClearance leftComparison.paths.denominatorClearance)).trans
    (congrArg₂ (fun numerator denominator : Int => numerator - denominator)
      (Eq.refl _) leftComparison.paths.denominator_raw)
  have rightRaw := (rightComparison.reading.raw_eq.symm.trans
    (Purelib.RationalFunctions.Winding.Circle.raw_eq_sub rightComparison.paths.quotient
      rightClearance rightComparison.paths.denominatorClearance)).trans
    (congrArg₂ (fun numerator denominator : Int => numerator - denominator)
      (Eq.refl _) rightComparison.paths.denominator_raw)
  have poleBound := product.poleOrder_le leftResult rightResult comparison.normalized
  have shift := comparison.extraShift_eq
  have shiftBalance : (leftResult.poleOrder : Int) + (rightResult.poleOrder : Int) =
      (comparison.normalized.poleOrder : Int) + (comparison.extraShift : Int) := by omega0
  apply Purelib.Data.Int.Arithmetic.eq_of_mul_eq_mul_left (by decide : (4 : Int) ≠ 0)
  rw [productRaw]
  calc
    _ = (Winding.Circle.raw leftPaths - 4 * (leftResult.poleOrder : Int)) +
        (Winding.Circle.raw rightPaths - 4 * (rightResult.poleOrder : Int)) := by omega0
    _ = 4 * (leftComparison.reading.winding + rightComparison.reading.winding) := by
      rw [← leftRaw, ← rightRaw]
      ring1

/-- The actual inside multiplicities balance after including the original compensated zero roots. -/
theorem insideCount_balance (comparison : Comparison product leftComparison rightComparison) :
    comparison.result.polynomial.inventory.insideCount + comparison.extraShift =
      leftComparison.polynomial.inventory.insideCount + rightComparison.polynomial.inventory.insideCount := by
  have winding := comparison.winding_add
  rw [comparison.result.winding_eq, leftComparison.winding_eq, rightComparison.winding_eq] at winding
  have poleBound := product.poleOrder_le leftResult rightResult comparison.normalized
  have shift := comparison.extraShift_eq
  omega0

/-- The actual pole-minus-inside index of the independently constructed product is additive. -/
theorem index_add (comparison : Comparison product leftComparison rightComparison) :
    (comparison.normalized.poleOrder : Int) - (comparison.result.polynomial.inventory.insideCount : Int) =
      ((leftResult.poleOrder : Int) - (leftComparison.polynomial.inventory.insideCount : Int)) +
        ((rightResult.poleOrder : Int) - (rightComparison.polynomial.inventory.insideCount : Int)) := by
  rw [comparison.result.index_eq_neg_winding, leftComparison.index_eq_neg_winding,
    rightComparison.index_eq_neg_winding, comparison.winding_add]
  ring1

end Comparison
end Purelib.Polynomial.Laurent.Circle.Product

end
