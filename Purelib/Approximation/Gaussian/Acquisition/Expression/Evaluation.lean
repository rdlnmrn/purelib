module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Basic
public import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic
public import Purelib.RootIsolation.SquareRoot.Observation.Annotated
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic

/-!
# The original acquisition expression evaluator

Finite expression syntax evaluates to the original coherent numerical channel.
Annotation and normalization may retain additional evidence without replacing
these arithmetic constructors, atom owners or selected root sheets.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

/-- Evaluate finite acquisition syntax as its original coherent numerical channel. -/
@[expose] def Expr.denote {arity : Nat} (environment : Fin arity → Annotated)
    (expression : Expr arity) : CoherentNamed :=
  let Result : Mode → Type 1 := fun mode => match mode with
    | .total => CoherentNamed
    | .checked => PUnit
  let rec interpret {mode : Mode} (expression : Expr arity mode) : Result mode :=
    match expression with
    | .atom index => (environment index).channel
    | .rational value => (Annotated.rational value).channel
    | .root parameter sheet => (Annotated.root parameter sheet).channel
    | .neg input =>
      match mode with
      | .total => CoherentNamed.neg (interpret input)
      | .checked => PUnit.unit
    | .add left right =>
      match mode with
      | .total => CoherentNamed.add (interpret left) (interpret right)
      | .checked => PUnit.unit
    | .sub left right =>
      match mode with
      | .total => CoherentNamed.add (interpret left) (CoherentNamed.neg (interpret right))
      | .checked => PUnit.unit
    | .mul left right =>
      match mode with
      | .total => CoherentNamed.mul (interpret left) (interpret right)
      | .checked => PUnit.unit
    | .base _ | .pow _ _ | .conj _ | .inverse _ => PUnit.unit
  termination_by structural expression
  interpret expression

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic

end
