module

import Purelib.Polynomial.Laurent.Normalization.Product
import Purelib.Polynomial.Laurent.Secant

/-!
# Original Laurent preparation clients

Each client executes the public preparation and reads the actual cached
support, pole order, dense coefficients and original zero-root multiplicity.
Cancellation examples also retain the source negative-power guard.
-/

namespace TestPurelib.Polynomial.Laurent.Normalization

open Purelib.Data
open Purelib.Polynomial.Laurent.Basic
open Purelib.Polynomial.Laurent.Normalization

/-- Read the actual successful preparation's support and polynomial data. -/
private def observed (source : LaurentPolynomial) :
    Option (Int × Int × Nat × List Gaussian.Basic.Canonical × Nat) :=
  match source.prepare with
  | .zero _ => none
  | .normalized result =>
      some (result.lower, result.upper, result.poleOrder, result.polynomial.coeffs, result.zeroMultiplicity)

/-- The coordinate symbol retains its genuine zero root without introducing a pole. -/
private theorem coordinate_preparation : observed ⟨[⟨1, .nonnegative 1⟩]⟩ = some (1, 1, 0, [1, 0], 1) := by decide

/-- A negative monomial polynomializes to its nonzero constant coefficient. -/
private theorem negative_monomial_preparation : observed ⟨[⟨1, .negative 1⟩]⟩ = some (-2, -2, 2, [1], 0) := by decide

/-- A nonreal coefficient uses the same original Laurent owner and dense scalar. -/
private theorem gaussian_constant_preparation : observed ⟨[⟨⟨1, 1⟩, .nonnegative 0⟩]⟩ =
    some (0, 0, 0, [⟨1, 1⟩], 0) := by decide

/-- Repeated signed exponents cancel before choosing the actual minimal pole order. -/
private theorem repeated_exponent_cancellation : observed ⟨[⟨1, .negative 0⟩, ⟨-1, .negative 0⟩, ⟨1, .nonnegative 2⟩]⟩ =
    some (2, 2, 0, [1, 0, 0], 2) := by decide

/-- Zero end coefficients do not inflate normalized support or pole order. -/
private theorem zero_endpoint_preparation : observed ⟨[⟨0, .negative 3⟩, ⟨2, .nonnegative 0⟩, ⟨0, .nonnegative 7⟩]⟩ =
    some (0, 0, 0, [2], 0) := by decide

/-- Exact cancellation returns the typed zero-symbol obstruction. -/
private theorem zero_symbol_rejected :
    observed ⟨[⟨⟨1, 1⟩, .negative 0⟩, ⟨⟨-1, -1⟩, .negative 0⟩]⟩ = none := by decide

/-- Cancellation does not remove the original expression's zero-input guard. -/
private theorem cancelled_guard_preserved : ¬(⟨[⟨1, .negative 0⟩, ⟨-1, .negative 0⟩, ⟨1, .nonnegative 0⟩]⟩ :
    LaurentPolynomial).DefinedAt 0 := by
  intro defined
  exact defined ⟨1, .negative 0⟩ List.mem_cons_self (by decide) rfl

/-- A larger shift is the original dense shift with the corresponding exact additional zero roots. -/
private theorem nonminimal_zero_count (source : LaurentPolynomial) (result : Normalized source) :
    (Purelib.Polynomial.Dense.Basic.DensePolynomial.shift 3 result.polynomial).zeroMultiplicity =
      result.zeroMultiplicity + 3 := result.nonminimal_zeroMultiplicity 3

/-- A zero preparation supplies an actual unit-boundary contact witness. -/
private theorem zero_obstruction_boundary (source : LaurentPolynomial)
    (obstruction : ZeroSymbol source) : source.eval 1 = 0 :=
  obstruction.boundary_contact

/-- Execute the actual original product and its automatic nonzero normalization once. -/
private def productObserved (left right : LaurentPolynomial) :
    Option (Int × Int × Nat × List Gaussian.Basic.Canonical × Nat) :=
  match left.prepare, right.prepare with
  | .normalized leftResult, .normalized rightResult =>
      let product := Purelib.Polynomial.Laurent.Arithmetic.multiply left right
      let result := product.normalize leftResult rightResult
      some (result.lower, result.upper, result.poleOrder, result.polynomial.coeffs, result.zeroMultiplicity)
  | _, _ => none

/-- Opposite signed monomials construct the constant product with its actual minimal shift. -/
private theorem opposite_monomial_product : productObserved ⟨[⟨1, .negative 0⟩]⟩ ⟨[⟨1, .nonnegative 1⟩]⟩ =
    some (0, 0, 0, [1], 0) := by decide

/-- An original negative-power product retains its zero guard despite becoming a constant symbol. -/
private theorem product_guard_preserved : ¬(Purelib.Polynomial.Laurent.Arithmetic.multiply
    ⟨[⟨1, .negative 0⟩]⟩ ⟨[⟨1, .nonnegative 1⟩]⟩).DefinedAt 0 := by
  intro defined
  exact defined.1 ⟨1, .negative 0⟩ List.mem_cons_self (by decide) rfl

/-- Nonreal cross-product coefficients combine duplicate exponents in the retained actual polynomial. -/
private theorem gaussian_convolution_product : productObserved ⟨[⟨⟨1, 1⟩, .negative 0⟩, ⟨2, .nonnegative 0⟩]⟩
    ⟨[⟨1, .nonnegative 1⟩, ⟨⟨0, 1⟩, .nonnegative 0⟩]⟩ =
      some (-1, 1, 1, [2, ⟨1, 3⟩, ⟨-1, 1⟩], 0) := by decide

/-- A product's positive lowest support remains as the polynomial's actual repeated zero root. -/
private theorem positive_product_zero_count : productObserved ⟨[⟨1, .nonnegative 3⟩]⟩ ⟨[⟨1, .negative 0⟩]⟩ =
    some (2, 2, 0, [1, 0, 0], 2) := by decide

end TestPurelib.Polynomial.Laurent.Normalization
