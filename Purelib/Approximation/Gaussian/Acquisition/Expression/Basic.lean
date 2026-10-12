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
/-- Finite arithmetic syntax retaining atom indices and displayed square-root sheets.

Expressions use Gaussian rational constants, indexed opaque atoms and explicit negation, addition, subtraction and
multiplication; syntactic identity is decidable. -/
inductive Expr (arity : Nat) where
  /-- Refer to one of the original finitely indexed input atoms. -/ | atom (index : Fin arity)
  /-- Retain an exact Gaussian rational constant. -/ | rational (value : Data.Gaussian.Basic.Canonical)
  /-- Retain a displayed square-root parameter and one of its two sheets. -/ | root (parameter :
    Data.Gaussian.Basic.Canonical) (sheet : Fin 2)
  /-- Negate a retained expression. -/ | neg (input : Expr
    arity)
  /-- Add two retained expressions. -/ | add (left right :
    Expr arity)
  /-- Subtract two retained expressions. -/ | sub (left right :
    Expr arity)
  /-- Multiply two retained expressions. -/ | mul (left right :
    Expr arity)
  deriving DecidableEq

constructive_injectivity Expr

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

end
