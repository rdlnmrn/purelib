module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Sequence.Name
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sequence

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Exponential.Horner

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

namespace Purelib.Approximation.Gaussian.Exponential.Horner.Name

/-- Turn the finite exponential Horner approximation of a displayed unit-disk Gaussian input into a productive process
name. -/
def named (x : Data.Gaussian.Basic.Canonical) (unitInput :
  Data.Gaussian.Norm.Basic.normSq x ≤ 1) : Gaussian.Name.Basic.Named :=
  (Sequence.approximation x unitInput).toNamed
end Purelib.Approximation.Gaussian.Exponential.Horner.Name

end
