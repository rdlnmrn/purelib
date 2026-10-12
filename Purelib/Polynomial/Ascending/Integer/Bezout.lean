module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Ascending.Integer.Basic
public import Purelib.Polynomial.Ascending.Integer.Products

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

/-!
# Finite integer-polynomial certificates

Integer coefficient lists are stored in ascending degree order.  The
primitive-recursive operations below let a literal finite Bezout identity be
checked by kernel reduction over `Int`, then evaluated in any constructive
explicit field.  This is useful for prime-field exclusions without listing
or searching an ambient carrier.
-/

public section

namespace Purelib.Polynomial.Ascending.Integer.Bezout

set_option genInjectivity false in
/-- A kernel-checkable finite Bezout identity
`left*cubic + right*(X^p-X) = 1 + p*correction`. -/
structure BezoutCertificate (modulus : Nat) (polynomial : List Int)
  where
  /-- The retained multiplier of the input polynomial in the Bézout identity. -/ left : List Int
  /-- The retained multiplier of `X^modulus - X` in the Bézout identity. -/ right : List Int
  /-- The retained correction table multiplied by the modulus on the right side. -/ correction : List Int
  /-- Exact list equality certifying the Bézout combination as one plus the modulus-scaled correction. -/ identity :
    Ascending.Integer.Basic.Certificate.add (Ascending.Integer.Basic.Certificate.mul left polynomial)
      (Ascending.Integer.Basic.Certificate.mul right (Ascending.Integer.Products.frobenius modulus)) =
      Ascending.Integer.Basic.Certificate.add [1] (Ascending.Integer.Basic.Certificate.scale (Int.ofNat modulus)
        correction)

constructive_injectivity BezoutCertificate

/-- A checked certificate rules out a common root of the displayed integer
polynomial and the pointwise Frobenius equation in characteristic `p`. -/
theorem no_common_root {K : Type*} [ExplicitField K] [Nontrivial K]
    {modulus : Nat} {polynomial : List Int}
    (certificate : BezoutCertificate modulus polynomial)
    (modulusZero : (modulus : K) = 0)
    (value : K) (polynomialZero : Ascending.Integer.Basic.eval polynomial value = 0)
    (frobeniusValue : value ^ modulus = value) : False := by
  have evaluated := congrArg (fun coefficients => Ascending.Integer.Basic.eval coefficients value)
    certificate.identity
  rw [Ascending.Integer.Basic.eval_add, Ascending.Integer.Basic.eval_mul, Ascending.Integer.Basic.eval_mul,
    Ascending.Integer.Products.eval_frobenius,
    Ascending.Integer.Basic.eval_add, Ascending.Integer.Basic.eval_scale] at evaluated
  have frobeniusZero : value ^ modulus - value = 0 := by
    rw [frobeniusValue]
    ring1
  have modulusCast : ((Int.ofNat modulus : Int) : K) = (modulus : K) := by
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]
  rw [polynomialZero, frobeniusZero, modulusCast, modulusZero] at evaluated
  have zeroOne : (0 : K) = 1 := by
    calc
      (0 : K) =
          Ascending.Integer.Basic.eval certificate.left value * 0 +
            Ascending.Integer.Basic.eval certificate.right value * 0 := by ring1
      _ = Ascending.Integer.Basic.eval [1] value + 0 * Ascending.Integer.Basic.eval certificate.correction value :=
        evaluated
      _ = 1 := by
        simp only [Ascending.Integer.Basic.eval_cons, Ascending.Integer.Basic.eval_nil, Int.cast_one]
        ring1
  exact (one_ne_zero : (1 : K) ≠ 0) zeroOne.symm

end Purelib.Polynomial.Ascending.Integer.Bezout

end
