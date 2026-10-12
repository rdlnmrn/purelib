module

public import Purelib.Data.Rat.Interval.Basic
public import Purelib.Data.Rat.Sign.CauchyIndex.Endpoint
import Purelib.Data.Rat.Sign.Typed
import Purelib.Data.Rat.Sign.Typed.Compatibility
import Purelib.Data.Sign.Basic
public import Purelib.Data.Sign.CauchyIndex.Event
import Purelib.Data.Sign.Stability
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

/-!
# Formal signs for a retained Cauchy event

The retained polynomial inputs and interval bounds determine the certificate
indices. Each certificate retains its actual samples, signed chains and branch evidence.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs

open Purelib
open Purelib.Polynomial
open _root_.Purelib.Data renaming Sign -> FiniteSign

@[expose] public section

set_option genInjectivity false in
/-- Formal finite center signs for one actual Cauchy pair, together with the exact event index represented between the
two displayed rational endpoints.

The retained numerator and denominator signs are jointly nonzero and stable
against both actual endpoint pairs. The index field identifies their finite
event reading with the doubled Cauchy index of the original polynomial pair. -/
structure CauchyEventSigns
    (R S : CoordinatePolynomial) (interval : Data.Rat.Interval.Bounds) where
  /-- The retained formal center sign of the numerator. -/ numerator : FiniteSign
  /-- The retained formal center sign of the denominator. -/ denominator : FiniteSign
  /-- At least one of the two formal center signs is nonzero. -/ nonzero : numerator ≠ .zero ∨ denominator ≠ .zero
  /-- The numerator center sign is stable against its actual lower endpoint sign. -/ numeratorLowerStable :
    FiniteSign.Stable numerator
    (FiniteSign.ofCoordinate (R.eval interval.lower))
  /-- The denominator center sign is stable against its actual lower endpoint sign. -/ denominatorLowerStable :
    FiniteSign.Stable denominator
    (FiniteSign.ofCoordinate (S.eval interval.lower))
  /-- The numerator center sign is stable against its actual upper endpoint sign. -/ numeratorUpperStable :
    FiniteSign.Stable numerator
    (FiniteSign.ofCoordinate (R.eval interval.upper))
  /-- The denominator center sign is stable against its actual upper endpoint sign. -/ denominatorUpperStable :
    FiniteSign.Stable denominator
    (FiniteSign.ofCoordinate (S.eval interval.upper))
  /-- The actual doubled Cauchy index equals the finite event index of the retained signs. -/ index :
    Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 R S interval.lower interval.upper =
    FiniteSign.eventIndex2 numerator denominator
      (FiniteSign.ofCoordinate (R.eval interval.lower))
      (FiniteSign.ofCoordinate (S.eval interval.lower))
      (FiniteSign.ofCoordinate (R.eval interval.upper))
      (FiniteSign.ofCoordinate (S.eval interval.upper))

constructive_injectivity CauchyEventSigns

end

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns

open Purelib
open Purelib.Polynomial
open _root_.Purelib.Data renaming Sign -> FiniteSign

/-- Replace the formal center by any other nonzero finite pair stable against the same two endpoint pairs.

Both center pairs retain stability against the same endpoint observations.
The resulting certificate changes only the supplied center signs and their
evidence, preserving the original polynomial pair, interval and index. -/
@[expose] public def recenter
    {R S : CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (data : CauchyEventSigns R S interval)
    (numerator denominator : FiniteSign)
    (nonzero : numerator ≠ .zero ∨ denominator ≠ .zero)
    (numeratorLowerStable : FiniteSign.Stable numerator
      (FiniteSign.ofCoordinate (R.eval interval.lower)))
    (denominatorLowerStable : FiniteSign.Stable denominator
      (FiniteSign.ofCoordinate (S.eval interval.lower)))
    (numeratorUpperStable : FiniteSign.Stable numerator
      (FiniteSign.ofCoordinate (R.eval interval.upper)))
    (denominatorUpperStable : FiniteSign.Stable denominator
      (FiniteSign.ofCoordinate (S.eval interval.upper))) :
    CauchyEventSigns R S interval where
  numerator := numerator
  denominator := denominator
  nonzero := nonzero
  numeratorLowerStable := numeratorLowerStable
  denominatorLowerStable := denominatorLowerStable
  numeratorUpperStable := numeratorUpperStable
  denominatorUpperStable := denominatorUpperStable
  index := by
    rw [data.index]
    exact FiniteSign.eventIndex2_eq_of_stable
      data.numerator data.denominator numerator denominator
      (FiniteSign.ofCoordinate (R.eval interval.lower))
      (FiniteSign.ofCoordinate (S.eval interval.lower))
      (FiniteSign.ofCoordinate (R.eval interval.upper))
      (FiniteSign.ofCoordinate (S.eval interval.upper))
      ⟨data.nonzero, data.numeratorLowerStable,
        data.denominatorLowerStable, data.numeratorUpperStable,
        data.denominatorUpperStable⟩
      ⟨nonzero, numeratorLowerStable, denominatorLowerStable,
        numeratorUpperStable, denominatorUpperStable⟩

/-- Re-center at the exact left endpoint and recover the one-sided endpoint index used by the constructive product
table.

The supplied endpoint nonzero and stability evidence makes its actual sign
pair a valid center. Recentring preserves the retained doubled Cauchy index. -/
public theorem index_eq_leftEndpointIndex2
    {R S : CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (data : CauchyEventSigns R S interval)
    (pairNonzero : R.eval interval.lower ≠ 0 ∨
      S.eval interval.lower ≠ 0)
    (numeratorStable : R.eval interval.lower = 0 ∨
      0 < R.eval interval.lower * R.eval interval.upper)
    (denominatorStable : S.eval interval.lower = 0 ∨
      0 < S.eval interval.lower * S.eval interval.upper) :
    Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 R S interval.lower interval.upper =
      Data.Rat.Sign.CauchyIndex.Endpoint.leftEndpointIndex2
        (R.eval interval.lower) (S.eval interval.lower)
        (R.eval interval.upper) (S.eval interval.upper) := by
  let centered := data.recenter
    (FiniteSign.ofCoordinate (R.eval interval.lower))
    (FiniteSign.ofCoordinate (S.eval interval.lower))
    (pairNonzero.elim
      (fun nonzero => Or.inl (FiniteSign.ofCoordinate_ne_zero_iff.mpr nonzero))
      (fun nonzero => Or.inr (FiniteSign.ofCoordinate_ne_zero_iff.mpr nonzero)))
    (Or.inr rfl) (Or.inr rfl)
    (Data.Rat.Sign.Typed.Compatibility.sign_stable_of_eq_zero_or_mul_pos numeratorStable)
    (Data.Rat.Sign.Typed.Compatibility.sign_stable_of_eq_zero_or_mul_pos denominatorStable)
  have centeredIndex := centered.index
  dsimp only [centered, recenter] at centeredIndex
  rw [centeredIndex, FiniteSign.eventIndex2_self_left,
    Data.Rat.Sign.CauchyIndex.Endpoint.sign_leftEndpointIndex2_ofCoordinate]

/-- Re-center at the exact right endpoint.

The supplied right-endpoint pair is jointly nonzero and stable against the
left endpoint. Orientation reversal negates the same retained event reading. -/
public theorem reverseIndex_eq_leftEndpointIndex2
    {R S : CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (data : CauchyEventSigns R S interval)
    (pairNonzero : R.eval interval.upper ≠ 0 ∨
      S.eval interval.upper ≠ 0)
    (numeratorStable : R.eval interval.upper = 0 ∨
      0 < R.eval interval.upper * R.eval interval.lower)
    (denominatorStable : S.eval interval.upper = 0 ∨
      0 < S.eval interval.upper * S.eval interval.lower) :
    Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 R S interval.upper interval.lower =
      Data.Rat.Sign.CauchyIndex.Endpoint.leftEndpointIndex2
        (R.eval interval.upper) (S.eval interval.upper)
        (R.eval interval.lower) (S.eval interval.lower) := by
  let centered := data.recenter
    (FiniteSign.ofCoordinate (R.eval interval.upper))
    (FiniteSign.ofCoordinate (S.eval interval.upper))
    (pairNonzero.elim
      (fun nonzero => Or.inl (FiniteSign.ofCoordinate_ne_zero_iff.mpr nonzero))
      (fun nonzero => Or.inr (FiniteSign.ofCoordinate_ne_zero_iff.mpr nonzero)))
    (Data.Rat.Sign.Typed.Compatibility.sign_stable_of_eq_zero_or_mul_pos numeratorStable)
    (Data.Rat.Sign.Typed.Compatibility.sign_stable_of_eq_zero_or_mul_pos denominatorStable)
    (Or.inr rfl) (Or.inr rfl)
  have centeredIndex := centered.index
  dsimp only [centered, recenter] at centeredIndex
  rw [Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse, centeredIndex,
    FiniteSign.neg_eventIndex2_self_right,
    Data.Rat.Sign.CauchyIndex.Endpoint.sign_leftEndpointIndex2_ofCoordinate]

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns
