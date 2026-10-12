module
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic

import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
import Purelib.Approximation.Gaussian.Acquisition.Provenance
public import Purelib.RootIsolation.SquareRoot.Observation.Annotated
import Init.Prelude
import Purelib.Approximation.Gaussian.Provenance.Rational.Arithmetic
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.RootContinuation.SquareRootSidecar

open Purelib.Approximation.Gaussian.Acquisition (Annotated)

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

section
@[expose] public section

/-!
# A finite expression front end for certificate acquisition

Syntactic sharing supplies cancellation and squaring evidence even for opaque
atoms. This is not equality testing for arbitrary processes, nor a reifier
for arbitrary Lean functions. The compiler preserves the numerical channel
exactly; only its optional, proved provenance is inferred.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic.Expr

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

/-- Evaluate finite acquisition syntax as its original coherent numerical channel. -/
def denote {arity : Nat} (environment : Fin
  arity → Annotated) : Expression.Basic.Expr arity → Coherent.CoherentNamed
  | .atom index => (environment index).channel
  | .rational value => (Annotated.rational value).channel
  | .root parameter sheet => (Annotated.root parameter sheet).channel
  | .neg input => CoherentNamed.neg (input.denote environment)
  | .add left right => CoherentNamed.add
      (left.denote environment) (right.denote environment)
  | .sub left right => CoherentNamed.add
      (left.denote environment) (CoherentNamed.neg (right.denote environment))
  | .mul left right => CoherentNamed.mul
      (left.denote environment) (right.denote environment)

/-- Compile finite acquisition syntax while inferring supported provenance from its exact syntactic sharing.

Cancellation and repeated-factor cases reuse the same compiled child; unsupported combinations keep their numerical
channel without inventing provenance. -/
def compile {arity : Nat} (environment : Fin
  arity → Annotated) : Expression.Basic.Expr arity →
      Annotated
  | .atom index => environment index
  | .rational value => Annotated.rational value
  | .root parameter sheet => Annotated.root parameter sheet
  | .neg input => (input.compile environment).neg
  | .add left right =>
      if right = .neg left then (left.compile environment).cancel
      else (left.compile environment).add (right.compile environment)
  | .sub left right =>
      if left = right then (left.compile environment).cancel
      else (left.compile environment).add (right.compile environment).neg
  | .mul left right =>
      if left = right then (left.compile environment).square
      else (left.compile environment).mul (right.compile environment)

/-- Evidence inference changes neither process state, emitted prefix, nor refinement program. Equality here is stronger
than operational equivalence. -/
theorem compile_channel {arity : Nat}
  (environment : Fin arity → Annotated) (expression : Expression.Basic.Expr arity) :
    (expression.compile environment).channel = expression.denote environment := by
  induction expression with
  | atom index => rfl
  | rational value => rfl
  | root parameter sheet => rfl
  | neg input ih => exact congrArg CoherentNamed.neg ih
  | add left right ihLeft ihRight =>
      simp only [compile, -eq_self, -iff_self]
      split
      · rename_i equal
        subst right
        change CoherentNamed.add _ _ = _
        simp only [denote, ← ihLeft, -eq_self, -iff_self]
        rfl
      · change CoherentNamed.add _ _ = _
        simp only [denote, ihLeft, ihRight, -eq_self,
          -iff_self]
        rfl
  | sub left right ihLeft ihRight =>
      simp only [compile, -eq_self, -iff_self]
      split
      · rename_i equal
        subst right
        change CoherentNamed.add _ _ = _
        simp only [denote, ihLeft, -eq_self, -iff_self]
        rfl
      · change CoherentNamed.add _ _ = _
        simp only [denote,
            Annotated.neg, ihLeft, ihRight,
          -eq_self, -iff_self]
        rfl
  | mul left right ihLeft ihRight =>
      simp only [compile, -eq_self, -iff_self]
      split
      · rename_i equal
        subst right
        change CoherentNamed.mul _ _ = _
        simp only [denote, ihLeft, -eq_self, -iff_self]
        rfl
      · change CoherentNamed.mul _ _ = _
        simp only [denote, ihLeft, ihRight, -eq_self,
          -iff_self]
        rfl

/-- Compiling subtraction of the same expression retains rational provenance with exact value zero. -/
theorem compile_cancel {arity : Nat}
  (environment : Fin arity → Annotated) (expression : Expression.Basic.Expr arity) :
    ((Expr.sub expression expression).compile environment).rationalValue = some 0 := by
  rewrite [compile, if_pos rfl]
  rfl

/-- Compiling an expression plus its syntactic negation retains rational provenance with exact value zero. -/
theorem compile_add_neg {arity : Nat}
  (environment : Fin arity → Annotated) (expression : Expression.Basic.Expr arity) :
    ((Expr.add expression (.neg expression)).compile environment).rationalValue = some 0 := by
  rewrite [compile, if_pos rfl]
  rfl
end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic.Expr

end
