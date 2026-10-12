module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Sequence.CCL.Output
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.Name
import Purelib.Approximation.Gaussian.Exponential.Horner.Sequence
import Purelib.Data.CCL.Transducer.Machine.Advance

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Exponential.Horner

open Purelib.Data.CCL.Transducer.Machine

section
@[expose] public section

/-!
# Finite exponential Horner approximation

This is a finite operational exponential on Gaussian rationals in the closed
unit disk.  `sample x n` evaluates exactly one finite Horner program.  The
pairwise theorem compares any two displayed truncations and supplies an
explicit rational squared-error sidecar.  Nothing in this module defines a
completed exponential value or invokes an infinite series or a limit.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Horner.CCL.Output

/-- Every natural request returns exactly that many CCL bits. Its sidecar semantics ranges only over explicitly
witnessed later finite Horner samples. -/
theorem productive (x :
  Data.Gaussian.Basic.Canonical) (unitInput : Data.Gaussian.Norm.Basic.normSq x ≤ 1) (count : Nat) :
    (Name.named x unitInput).machine.emitted.IsPrefix
        (Advance.advance
          (Name.named x unitInput).machine count).emitted ∧
      (Advance.advance
          (Name.named x unitInput).machine count).emitted.length = count :=
  (Sequence.approximation x unitInput).output_productive count

end Purelib.Approximation.Gaussian.Exponential.Horner.CCL.Output

end
