module

public import Purelib.Data.Gaussian.Basic
import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

section
@[expose] public section

/-!
# A finite expression front end for certificate acquisition

Syntactic sharing supplies cancellation and squaring evidence even for opaque
atoms. This is not equality testing for arbitrary processes, nor a reifier
for arbitrary Lean functions. The compiler preserves the numerical channel
exactly; only its optional, proved provenance is inferred.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

set_option genInjectivity false in
/-- The total or checked evaluation discipline of finite acquisition syntax. -/
inductive Mode where
  /-- The original everywhere-defined arithmetic and displayed root language. -/
  | total
  /-- Arithmetic retaining total base regions and checked reciprocal nodes. -/
  | checked
  deriving @[expose] DecidableEq

constructive_injectivity Mode

set_option genInjectivity false in
/-- Finite arithmetic syntax retaining original atom indices, root sheets and total base regions.

The default index is the original total grammar. The checked index retains total
base regions and adds natural powers, conjugation and partial reciprocals;
negation, addition, subtraction and multiplication use the same constructors. -/
inductive Expr (arity : Nat) : (mode : optParam Mode .total) → Type where
  /-- Refer to one of the original finitely indexed input atoms. -/
  | atom (index : Fin arity) : Expr arity .total
  /-- Retain an exact Gaussian rational constant. -/
  | rational (value : Canonical) : Expr arity .total
  /-- Retain a displayed square-root parameter and one of its two sheets. -/
  | root (parameter : Canonical) (sheet : Fin 2) : Expr arity .total
  /-- Negate a retained expression in its original discipline. -/
  | neg {mode : Mode} (input : Expr arity mode) : Expr arity mode
  /-- Add two retained expressions in their original discipline. -/
  | add {mode : Mode} (left right : Expr arity mode) : Expr arity mode
  /-- Subtract two retained expressions in their original discipline. -/
  | sub {mode : Mode} (left right : Expr arity mode) : Expr arity mode
  /-- Multiply two retained expressions in their original discipline. -/
  | mul {mode : Mode} (left right : Expr arity mode) : Expr arity mode
  /-- Retain an entire original total region for its unchanged cached compiler. -/
  | base (expression : Expr arity .total) : Expr arity .checked
  /-- Raise a checked child to its displayed finite natural power. -/
  | pow (input : Expr arity .checked) (exponent : Nat) : Expr arity .checked
  /-- Conjugate a retained checked child. -/
  | conj (input : Expr arity .checked) : Expr arity .checked
  /-- Prepare a checked child before constructing its partial reciprocal. -/
  | inverse (input : Expr arity .checked) : Expr arity .checked
  deriving @[expose] DecidableEq

constructive_injectivity Expr

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

end
