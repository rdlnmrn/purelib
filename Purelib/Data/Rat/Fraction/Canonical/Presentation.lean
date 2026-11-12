module

public import Purelib.Data.Rat.Fraction.Presentation
public import Purelib.Data.Nat.Coprime.Presentation

namespace Purelib.Data.Rat.Fraction.Canonical.Presentation

open Purelib.Data.Nat

/-- Canonical coordinates accompanied by proposed Bézout coefficients. -/
public abbrev Code := Fraction.Presentation.Code × Coprime.Presentation.Code

/-- The denominator is positive and the coefficients certify reducedness. -/
@[expose] public def Valid (code : Code) : Prop :=
  Fraction.Presentation.Valid code.1 ∧ Coprime.Presentation.Valid code.1.1.natAbs code.1.2 code.2

set_option genInjectivity false in
/-- The result of checking canonical coordinates and supplied coefficients. -/
public inductive Check (code : Code) where
  /-- The denominator and coefficient equation are valid. -/
  | valid (positive : Fraction.Presentation.Valid code.1)
      (identity : Coprime.Presentation.Valid code.1.1.natAbs code.1.2 code.2)
  /-- The denominator is zero. -/
  | zeroDenominator (zero : code.1.2 = 0)
  /-- The supplied coefficients fail their input-bound equation. -/
  | invalidCoefficients (positive : Fraction.Presentation.Valid code.1)
      (different : ¬ Coprime.Presentation.Valid code.1.1.natAbs code.1.2 code.2)

/-- Check the denominator first and then the supplied Bézout coefficients. -/
@[expose] public def check (code : Code) : Check code :=
  match Fraction.Presentation.check code.1 with
  | .zeroDenominator zero => .zeroDenominator zero
  | .valid positive =>
    match Coprime.Presentation.check code.1.1.natAbs code.1.2 code.2 with
    | .invalid different => .invalidCoefficients positive different
    | .valid identity => .valid positive identity

/-- Decide validity using the same typed checks. -/
@[expose] public def recognize (code : Code) : Decidable (Valid code) :=
  match check code with
  | .valid positive identity => .isTrue ⟨positive, identity⟩
  | .zeroDenominator zero => .isFalse (fun valid => Nat.ne_of_gt valid.1 zero)
  | .invalidCoefficients _ different => .isFalse (fun valid => different valid.2)

/-- Checked coordinates and their supplied finite certificate. -/
public abbrev Display := {code : Code // Valid code}

/-- Construct the original rational with exactly the checked coordinates. -/
@[expose] public def read (display : Display) : Rational :=
  ⟨display.val.1.1, display.val.1.2, display.property.1,
    ⟨Coprime.Presentation.read ⟨display.val.2, display.property.2⟩⟩⟩

/-- Quote a rational using a separately supplied certificate for its coordinates. -/
@[expose] public def quote (value : Rational)
    (certificate : Coprime.Basic.CoprimeCertificate value.num.natAbs value.den) : Display :=
  ⟨((value.num, value.den), (certificate.left, certificate.right)), value.den_pos, certificate.identity⟩

/-- Reading quoted coordinates recovers the original rational. -/
public theorem read_quote (value : Rational)
    (certificate : Coprime.Basic.CoprimeCertificate value.num.natAbs value.den) :
    read (quote value certificate) = value := Rational.ext rfl rfl

/-- Displays are the same rational when their coordinates agree, independently of coefficients. -/
@[expose] public def Same (left right : Display) : Prop := left.val.1 = right.val.1

/-- Decide coordinate equality using integer and natural equality. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val.1 = right.val.1))

/-- Coordinate equality is exactly equality of the original rational records. -/
public theorem same_iff_read_eq (left right : Display) : Same left right ↔ read left = read right := by
  constructor
  · intro same
    exact Rational.ext (congrArg Prod.fst same) (congrArg Prod.snd same)
  · intro same
    exact Prod.ext (congrArg Rational.num same) (congrArg Rational.den same)

/-- Canonical coordinate equality is exactly the original fraction cross-product relation. -/
public theorem same_iff_equivalent (left right : Display) :
    Same left right ↔ Equivalent (read left).toRaw (read right).toRaw := by
  constructor
  · intro same
    apply (equivalent_iff_normalize_eq _ _).mpr
    exact (normalize_idempotent (read left)).trans
      (((same_iff_read_eq left right).mp same).trans (normalize_idempotent (read right)).symm)
  · intro equivalent
    have normalized := (equivalent_iff_normalize_eq _ _).mp equivalent
    exact (same_iff_read_eq left right).mpr ((normalize_idempotent (read left)).symm.trans
      (normalized.trans (normalize_idempotent (read right))))

/-- The explicit canonical-coordinate presentation with supplied coefficients. -/
@[expose] public def canonical : Data.Presentation Code where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-!
The finite input contains signed numerator, natural denominator and two supplied
integer coefficients. `check` reuses the positive-denominator and Bézout checks;
it does not normalize raw displays or search for coefficients. `read` constructs
the original `Rational`, and `same_iff_read_eq` shows that different accepted
coefficient witnesses do not change its identity. `quote` requires a separately
supplied original certificate. `same_iff_equivalent` connects canonical
coordinate comparison with the original fraction cross-products. The
proposition-valued `Reduced` field is not
eliminated into executable coefficients. Dependencies and runtime admission
remain subject to the repository's separate scoped workflows.
-/

end Purelib.Data.Rat.Fraction.Canonical.Presentation
