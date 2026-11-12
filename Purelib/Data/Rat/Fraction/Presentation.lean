module

public import Purelib.Data.Presentation
public import Purelib.Data.Rat.Fraction

namespace Purelib.Data.Rat.Fraction.Presentation

/-- A fraction display is a signed numerator and a natural denominator. -/
public abbrev Code := Int × Nat

/-- A display is admissible exactly when its denominator is positive. -/
@[expose] public def Valid (code : Code) : Prop := 0 < code.2

set_option genInjectivity false in
/-- The result of checking a fraction display.

A valid result retains denominator positivity. A zero denominator is rejected
with an equality identifying the precise invalidity. -/
public inductive Check (code : Code) where
  /-- The denominator is positive. -/ | valid (positive : Valid code)
  /-- The denominator is zero. -/ | zeroDenominator (zero : code.2 = 0)

/-- Check a display's denominator and retain either positivity or zero. -/
@[expose] public def check (code : Code) : Check code :=
  if positive : 0 < code.2 then .valid positive
  else .zeroDenominator (Nat.eq_zero_of_not_pos positive)

/-- Decide admissibility using the same evidence as `check`. -/
@[expose] public def recognize (code : Code) : Decidable (Valid code) :=
  match check code with
  | .valid positive => .isTrue positive
  | .zeroDenominator zero => .isFalse (fun positive => Nat.ne_of_gt positive zero)

/-- Decide admissibility using the typed fraction-display checker. -/
public instance (code : Code) : Decidable (Valid code) := recognize code

/-- A display together with its positive-denominator certificate. -/
public abbrev Display := {code : Code // Valid code}

/-- View an admissible display as the original positive-denominator fraction. -/
@[expose] public def toRaw (display : Display) : RawFraction :=
  ⟨display.val.1, display.val.2, display.property⟩

/-- Two displays are equal when their original fraction cross-products agree. -/
@[expose] public def Same (left right : Display) : Prop :=
  Equivalent (toRaw left) (toRaw right)

/-- Decide display equivalence with the original cross-product decision. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (Equivalent (toRaw left) (toRaw right)))

/-- Decide displayed rational equality by the original cross-products. -/
public instance (left right : Display) : Decidable (Same left right) := compare left right

/-- Read an admissible display as its canonical rational via gcd normalization. -/
@[expose] public def read (display : Display) : Rational := normalize (toRaw display)

/-- Quote a canonical rational by its retained numerator and denominator. -/
@[expose] public def quote (value : Rational) : Display :=
  ⟨(value.num, value.den), value.den_pos⟩

/-- Display equivalence is exactly equality of canonical readbacks. -/
public theorem same_iff_read_eq (left right : Display) :
    Same left right ↔ read left = read right :=
  equivalent_iff_normalize_eq (toRaw left) (toRaw right)

/-- Quoting and reading an original canonical rational returns that rational. -/
public theorem read_quote (value : Rational) : read (quote value) = value :=
  normalize_idempotent value

/-- Normalize an admissible display to the quotation of its canonical readback. -/
@[expose] public def normalized (display : Display) : Display := quote (read display)

/-- Normalization preserves the presented rational. -/
public theorem normalized_same (display : Display) : Same (normalized display) display :=
  (same_iff_read_eq _ _).mpr (read_quote (read display))

/-- Normalization respects equality of the represented rational. -/
public theorem normalized_respects {left right : Display} (same : Same left right) :
    Same (normalized left) (normalized right) :=
  (same_iff_read_eq _ _).mpr ((read_quote (read left)).trans
    (((same_iff_read_eq _ _).mp same).trans (read_quote (read right)).symm))

/-!
## Rational fraction displays

* **Object and expressions:** `Code` is the typed finite pair `Int × Nat`,
  displayed as numerator/denominator; this interface does not parse text.
* **Recognition:** `check` accepts precisely `Valid`, positive denominator,
  and returns `Check.zeroDenominator` with proof otherwise. `recognize` derives
  the shared decision from that result; reduced form is not required.
* **Equality:** `compare` decides `Same`, the original `Equivalent` integer
  cross-product relation, rather than literal display equality. Its equivalence
  laws are in `fraction`; `same_iff_read_eq` identifies it with equality of
  canonical rational readbacks.
* **Constructions and operations:** `toRaw` retains the input coordinates;
  `read` uses `Fraction.normalize`, and `quote` retains a `Rational`'s
  coordinates. `read_quote`, `normalized_same` and `normalized_respects`
  establish the round trip and normalization guarantees.
* **Termination and dependencies:** denominator and cross-product checks use
  finite natural and integer decisions. `Fraction.normalize` uses the original
  finite gcd and its quotient certificates. The original fraction owner and
  the repository's constructive proof and runtime assumptions remain in force;
  this presentation does not certify those dependencies itself.
* **Examples and non-examples:** `Purelib.Examples.Data.Rat.Fraction.Presentation`
  defines `half` and `twoQuarters` and proves `sameReadback`.
  `TestPurelib.Data.Rat.Fraction.Regression` compares 1/2 with 2/3, admits
  negative and zero numerators, and checks the `zeroDenominator` rejection.
-/
/-- The explicit presentation of rationals by positive-denominator displays. -/
@[expose] public def fraction : Data.Presentation Code where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun value => equivalent_refl (toRaw value),
    fun proof => equivalent_symm proof,
    fun first second => equivalent_trans first second⟩

end Purelib.Data.Rat.Fraction.Presentation
