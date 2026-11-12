module

public import Purelib.Data.Presentation
public import Purelib.Data.Nat.Coprime.Basic

namespace Purelib.Data.Nat.Coprime.Presentation

open Purelib.Data.Nat.Coprime.Basic

/-- The retained integer coefficients of a proposed Bézout certificate. -/
public abbrev Code := Int × Int

/-- The coefficients give one for the specified original natural inputs. -/
@[expose] public def Valid (leftInput rightInput : Nat) (code : Code) : Prop :=
  code.1 * (leftInput : Int) + code.2 * (rightInput : Int) = 1

set_option genInjectivity false in
/-- The result of checking the Bézout equation for the specified inputs. -/
public inductive Check (leftInput rightInput : Nat) (code : Code) where
  /-- The proposed coefficients satisfy the equation. -/
  | valid (identity : Valid leftInput rightInput code)
  /-- The proposed coefficients fail the equation. -/
  | invalid (different : ¬ Valid leftInput rightInput code)

/-- Check the integer equation, retaining evidence for either outcome. -/
@[expose] public def check (leftInput rightInput : Nat) (code : Code) :
    Check leftInput rightInput code :=
  if identity : code.1 * (leftInput : Int) + code.2 * (rightInput : Int) = 1 then
    .valid identity
  else
    .invalid identity

/-- Decide admissibility using the same equation checker. -/
@[expose] public def recognize (leftInput rightInput : Nat) (code : Code) :
    Decidable (Valid leftInput rightInput code) :=
  match check leftInput rightInput code with
  | .valid identity => .isTrue identity
  | .invalid different => .isFalse different

/-- A coefficient pair certified for its original natural inputs. -/
public abbrev Display (leftInput rightInput : Nat) :=
  {code : Code // Valid leftInput rightInput code}

/-- Construct the original certificate from its checked coefficients. -/
@[expose] public def read {leftInput rightInput : Nat}
    (display : Display leftInput rightInput) : CoprimeCertificate leftInput rightInput :=
  ⟨display.val.1, display.val.2, display.property⟩

/-- Quote the original certificate's retained coefficients and equation. -/
@[expose] public def quote {leftInput rightInput : Nat}
    (certificate : CoprimeCertificate leftInput rightInput) : Display leftInput rightInput :=
  ⟨(certificate.left, certificate.right), certificate.identity⟩

/-- Two displays are the same when their ordered coefficients agree. -/
@[expose] public def Same {leftInput rightInput : Nat}
    (left right : Display leftInput rightInput) : Prop := left.val = right.val

/-- Compare both retained integer coefficients. -/
@[expose] public def compare {leftInput rightInput : Nat}
    (left right : Display leftInput rightInput) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val = right.val))

/-- Reading quoted coefficients recovers the original certificate. -/
public theorem read_quote {leftInput rightInput : Nat}
    (certificate : CoprimeCertificate leftInput rightInput) : read (quote certificate) = certificate := by
  cases certificate
  rfl

/-- Quoting a read display recovers the coefficients and ignores proof identity. -/
public theorem quote_read {leftInput rightInput : Nat}
    (display : Display leftInput rightInput) : quote (read display) = display := by
  cases display with
  | mk code identity =>
    cases code
    rfl

/-- Coefficient equality agrees with equality of the original certificates. -/
public theorem same_iff_read_eq {leftInput rightInput : Nat}
    (left right : Display leftInput rightInput) : Same left right ↔ read left = read right := by
  constructor
  · intro equal
    cases left with
    | mk left _ =>
      cases right with
      | mk right _ =>
        cases equal
        rfl
  · intro equal
    exact congrArg (fun value : CoprimeCertificate leftInput rightInput => (value.left, value.right)) equal

/-- The finite coefficient presentation for one fixed pair of natural inputs. -/
@[expose] public def coefficients (leftInput rightInput : Nat) : Purelib.Data.Presentation Code where
  Valid := Valid leftInput rightInput
  recognize := recognize leftInput rightInput
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-!
The input is a pair of integers bound to the indicated natural inputs. `check`
decides their Bézout equation, returning its proof or a proof of failure; it
does not search for coefficients. `read` and `quote` connect that display to the
original `CoprimeCertificate`, and `same_iff_read_eq` identifies ordered
coefficient equality with original certificate equality. Proof irrelevance
does not identify different coefficient pairs. Integer arithmetic and equality
use their existing finite procedures; proof-system and runtime admission remain
separate obligations.
-/

end Purelib.Data.Nat.Coprime.Presentation
