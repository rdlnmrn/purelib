import CCL.Acquisition.Annotated

/-!
# A finite expression front end for certificate acquisition

Syntactic sharing supplies cancellation and squaring evidence even for opaque
atoms. This is not equality testing for arbitrary processes, nor a reifier
for arbitrary Lean functions. The compiler preserves the numerical channel
exactly; only its optional, proved provenance is inferred.
-/

namespace CCL.AcquisitionAutomation

open CCL.FiniteAcquisition (Gaussian CoherentNamed)

inductive Expr (arity : Nat) where
  | atom (index : Fin arity)
  | rational (value : Gaussian)
  | root (parameter : Gaussian) (sheet : Fin 2)
  | neg (input : Expr arity)
  | add (left right : Expr arity)
  | sub (left right : Expr arity)
  | mul (left right : Expr arity)
  deriving DecidableEq

def Expr.denote {arity : Nat} (environment : Fin arity → Annotated) : Expr arity → CoherentNamed
  | .atom index => (environment index).channel
  | .rational value => (Annotated.rational value).channel
  | .root parameter sheet => (Annotated.root parameter sheet).channel
  | .neg input => CCL.ProgressiveCoherence.CoherentNamed.neg (input.denote environment)
  | .add left right => CCL.ProgressiveCoherence.CoherentNamed.add
      (left.denote environment) (right.denote environment)
  | .sub left right => CCL.ProgressiveCoherence.CoherentNamed.add
      (left.denote environment) (CCL.ProgressiveCoherence.CoherentNamed.neg (right.denote environment))
  | .mul left right => CCL.ProgressiveCoherence.CoherentNamed.mul
      (left.denote environment) (right.denote environment)

def Expr.compile {arity : Nat} (environment : Fin arity → Annotated) : Expr arity → Annotated
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

/-- Evidence inference changes neither process state, emitted prefix, nor
refinement program. Equality here is stronger than operational equivalence. -/
theorem Expr.compile_channel {arity : Nat} (environment : Fin arity → Annotated) (expression : Expr arity) :
    (expression.compile environment).channel = expression.denote environment := by
  induction expression with
  | atom index => rfl
  | rational value => rfl
  | root parameter sheet => rfl
  | neg input ih => exact congrArg CCL.ProgressiveCoherence.CoherentNamed.neg ih
  | add left right ihLeft ihRight =>
      simp only [Expr.compile]
      split
      · rename_i equal
        subst right
        change CCL.ProgressiveCoherence.CoherentNamed.add _ _ = _
        simp only [Expr.denote, ← ihLeft]
      · change CCL.ProgressiveCoherence.CoherentNamed.add _ _ = _
        simp only [Expr.denote, ihLeft, ihRight]
  | sub left right ihLeft ihRight =>
      simp only [Expr.compile]
      split
      · rename_i equal
        subst right
        change CCL.ProgressiveCoherence.CoherentNamed.add _ _ = _
        simp only [Expr.denote, ihLeft]
      · change CCL.ProgressiveCoherence.CoherentNamed.add _ _ = _
        simp only [Expr.denote, Annotated.neg, ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
      simp only [Expr.compile]
      split
      · rename_i equal
        subst right
        change CCL.ProgressiveCoherence.CoherentNamed.mul _ _ = _
        simp only [Expr.denote, ihLeft]
      · change CCL.ProgressiveCoherence.CoherentNamed.mul _ _ = _
        simp only [Expr.denote, ihLeft, ihRight]

theorem Expr.compile_cancel {arity : Nat} (environment : Fin arity → Annotated) (expression : Expr arity) :
    ((Expr.sub expression expression).compile environment).rationalValue = some 0 := by
  simp only [Expr.compile]
  rfl

theorem Expr.compile_add_neg {arity : Nat} (environment : Fin arity → Annotated) (expression : Expr arity) :
    ((Expr.add expression (.neg expression)).compile environment).rationalValue = some 0 := by
  simp only [Expr.compile]
  rfl

theorem Annotated.root_square_value (parameter : Gaussian) (sheet : Fin 2) :
    (Annotated.root parameter sheet).square.rationalValue = some parameter :=
  congrArg some (CCL.Riemann.SquareRootProvenance.isolated_parameter parameter sheet)

end CCL.AcquisitionAutomation
