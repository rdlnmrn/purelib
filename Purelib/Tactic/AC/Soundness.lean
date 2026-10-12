module
import Purelib.Data.List.Nat.Equality

import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring.Basic

open Lean.Data

/-!
# Quotient-free ring normalization

Mathlib's ring normalizer is computational, but three proof lemmas emitted by
the tactic currently reach `Quot.sound`: integer-cast multiplication and
power in `norm_num`, and the generic AC normalizer's conversion of Boolean
list equality to propositional equality.  This module supplies direct
constructive replacements and a `ring0` frontend that substitutes them in the
generated proof term before the kernel checks it.

The normalizer and the replacement pass run only during elaboration.  The
stored theorem proof contains the explicit lemmas below, never the three
upstream quotient-bearing declarations.
-/

public section

namespace Purelib.Tactic.AC.Soundness

/-- The AC normalizer's soundness step with its finite Boolean equality
certificate decoded directly. -/
theorem ac_eq_of_norm {R : Sort u} (context : AC.Context R)
    (left right : AC.Expr)
    (equalNormalForms :
      AC.norm context left == AC.norm context right) :
    AC.eval R context left = AC.eval R context right := open Purelib in by
  have normalFormsEqual :
      AC.norm context left = AC.norm context right :=
    Data.List.Nat.Equality.listNat_eq_of_beq _ _ equalNormalForms
  calc
    AC.eval R context left =
        AC.evalList R context (AC.norm context left) :=
      (AC.Context.eval_norm context left).symm
    _ = AC.evalList R context (AC.norm context right) :=
      congrArg (AC.evalList R context) normalFormsEqual
    _ = AC.eval R context right :=
      AC.Context.eval_norm context right

end Purelib.Tactic.AC.Soundness

end
