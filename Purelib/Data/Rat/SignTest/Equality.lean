module
public import Purelib.Data.Rat.SignTest
public import Mathlib.Order.RelClasses
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Finite equality ownership for CCL formula atoms

The parser's weak/strict convention decides every atom exactly at a zero of
its Hermitian form.  This module records that decision as finite data and
lets formula inspection reuse boundaries already proved identically zero.
Consequently a universal boundary is discharged once, and structural
reinspection either proves the complete formula stable or returns a
different unresolved atom.
-/

namespace Purelib.Data.Rat.SignTest

open Purelib.Data.Rat in
/-- Retain either a proof that a sign test owns zero or a proof that it excludes zero.

Both outcomes retain the original sign-test index. The owned outcome proves satisfaction at zero; the excluded outcome
proves its negation, so callers receive evidence rather than a bare Boolean. -/
inductive EqualityDecision (test : Data.Rat.SignTest) where
  /-- Retain the proof that the selected sign test holds at zero. -/ | owned (holds : test.Holds 0)
  /-- Retain the proof that the selected sign test fails at zero. -/ | excluded (fails : ¬test.Holds 0)

open Purelib.Data.Rat in
open Purelib.Data.Rat.Fraction.Order in
/-- Decide whether zero satisfies a sign test and return the corresponding exact proof certificate.

Inspect the six finite sign-test constructors and construct the corresponding ownership or exclusion witness for zero.
No rational search or external enumeration is required. -/
def decideEquality (test : Data.Rat.SignTest) : EqualityDecision test := by
  cases test with
  | negative => exact .excluded (fun holds => holds.2 (Basic.le_refl _))
  | nonpositive => exact .owned (Basic.le_refl _)
  | zero => exact .owned rfl
  | nonzero => exact .excluded (fun unequal => unequal rfl)
  | nonnegative => exact .owned (Basic.le_refl _)
  | positive => exact .excluded (fun holds => holds.2 (Basic.le_refl _))
end Purelib.Data.Rat.SignTest

end
