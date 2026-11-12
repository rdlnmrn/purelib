module

import Purelib.Polynomial.Laurent.Transport

/-!
# Original Laurent reversal and conjugation with cancelled and zero terms

The same original expression retains a negative zero-coefficient occurrence
and a cancelled pair. Actual normalization and its transports compute both
support endpoints, poles, zero-root compensation and coefficient readbacks.
-/

namespace TestPurelib.Polynomial.Laurent.Transport

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Laurent.Basic
open Purelib.Polynomial.Laurent.Normalization

/-- An original complex-coefficient Laurent expression with cancellations and a retained negative zero term. -/
private def source : LaurentPolynomial :=
  ⟨[⟨⟨1, 1⟩, .negative 1⟩, ⟨⟨2, -1⟩, .nonnegative 3⟩,
    ⟨1, .nonnegative 1⟩, ⟨-1, .nonnegative 1⟩, ⟨0, .negative 5⟩]⟩

/-- The same original expression has a nonzero value at one. -/
private theorem source_at_one : source.eval 1 ≠ 0 := by decide +kernel

/-- The original total preparation constructs this expression's actual nonzero normalization. -/
private def retained : Normalized source :=
  match source.prepare with
  | .normalized result => result
  | .zero obstruction => False.elim (by exact source_at_one obstruction.boundary_contact)

/-- The displayed zero term contributes its original raw negative-power guard. -/
private theorem raw_shift : retained.rawShift = 6 := by decide +kernel

/-- Cancellation leaves the actual original support endpoints minus two and three. -/
private theorem support : retained.lower = -2 ∧ retained.upper = 3 := by decide +kernel

/-- The actual normalization clears exactly two pole powers and introduces no zero root. -/
private theorem pole_zero : retained.poleOrder = 2 ∧ retained.zeroMultiplicity = 0 := by decide +kernel

/-- The actual reversed constructor swaps and negates the original support endpoints. -/
private theorem reversed_support : retained.reverse.lower = -3 ∧ retained.reverse.upper = 2 := by
  constructor
  · exact retained.reverse_lower retained.reverse |>.trans (congrArg Neg.neg support.2)
  · exact retained.reverse_upper retained.reverse |>.trans (congrArg Neg.neg support.1)

/-- The actual combined adjoint swaps the signed support endpoints with the same correct signs. -/
private theorem adjoint_support : retained.adjoint.lower = -3 ∧ retained.adjoint.upper = 2 := by
  constructor
  · exact (retained.adjoint_lower retained.adjoint).trans (congrArg Neg.neg support.2)
  · exact (retained.adjoint_upper retained.adjoint).trans (congrArg Neg.neg support.1)

/-- The actual conjugate constructor preserves the original pole and zero-root count. -/
private theorem conjugate_pole_zero : retained.conjugate.poleOrder = 2 ∧ retained.conjugate.zeroMultiplicity = 0 := by
  constructor
  · exact (retained.conjugate_poleOrder retained.conjugate).trans pole_zero.1
  · exact (retained.conjugate_zeroMultiplicity retained.conjugate).trans pole_zero.2

/-- The actual conjugate polynomial cache is the original mapped coefficient table. -/
private theorem conjugate_coefficients : retained.conjugate.polynomial =
    Purelib.Polynomial.Dense.Gaussian.Conjugate.polynomial retained.polynomial :=
  retained.conjugate_polynomial retained.conjugate

/-- Even a zero coefficient with positive exponent becomes an actual negative-domain guard on reversal. -/
private def guarded : LaurentPolynomial := ⟨[⟨0, .nonnegative 1⟩, ⟨1, .nonnegative 0⟩]⟩

/-- The algebraically constant reversed expression still has its original nonzero-input requirement. -/
private theorem reversed_guard : ¬guarded.reverse.DefinedAt 0 := by
  intro defined
  have member : (⟨0, .negative 0⟩ : LaurentTerm) ∈ guarded.reverse.terms := .head _
  have nonzero := defined ⟨0, .negative 0⟩ member (Nat.succ_ne_zero 0)
  exact nonzero rfl

/-- All three actual operators retain the complete raw expression after two applications. -/
private theorem involutions : source.reverse.reverse = source ∧ source.conjugate.conjugate = source ∧
    source.adjoint.adjoint = source :=
  ⟨source.reverse_reverse, source.conjugate_conjugate, source.adjoint_adjoint⟩

/-- A positive monomial retains its original three zero-root startup coordinates. -/
private def positive : LaurentPolynomial := ⟨[⟨1, .nonnegative 3⟩]⟩

/-- Prepare the same positive monomial with the original total constructor. -/
private def positiveResult : Normalized positive :=
  match positive.prepare with
  | .normalized result => result
  | .zero obstruction => False.elim (by
      exact (by decide +kernel : positive.eval 1 ≠ 0) obstruction.boundary_contact)

/-- Reversal exchanges the positive monomial's zero jets with the actual negative pole powers. -/
private theorem positive_zero_pole : positiveResult.zeroMultiplicity = 3 ∧
    positiveResult.reverse.poleOrder = 3 ∧ positiveResult.reverse.zeroMultiplicity = 0 := by decide +kernel

/-- A negative monomial has no original zero root and two actual pole powers. -/
private def negative : LaurentPolynomial := ⟨[⟨1, .negative 1⟩]⟩

/-- Prepare the same negative monomial with the original total constructor. -/
private def negativeResult : Normalized negative :=
  match negative.prepare with
  | .normalized result => result
  | .zero obstruction => False.elim (by
      exact (by decide +kernel : negative.eval 1 ≠ 0) obstruction.boundary_contact)

/-- Reversal of a negative monomial introduces the actual positive zero-root transient block. -/
private theorem negative_zero_pole : negativeResult.poleOrder = 2 ∧
    negativeResult.reverse.zeroMultiplicity = 2 ∧ negativeResult.reverse.poleOrder = 0 := by decide +kernel

end TestPurelib.Polynomial.Laurent.Transport
