module

public import Purelib.Polynomial.Multivariate.Evaluation
import Mathlib.Algebra.Group.Defs

/-!
# Renaming finite polynomial variables

A bounded map of original variable indices transports retained monomials and
coefficients. Canonicalization combines variables mapped to the same target
index; scalar evaluation reads the corresponding original pullback environment.
-/

public section

namespace Purelib.Polynomial.Multivariate

namespace Monomial

/-- Multiply every retained exponent by a natural power through finite exponent addition. -/
@[expose] def power {arity : Nat} (monomial : Monomial arity) : Nat → Monomial arity
  | 0 => zero arity
  | exponent + 1 => add (power monomial exponent) monomial

/-- Rename original bounded variables, adding the exponents of variables with the same target index. -/
@[expose] def rename {target : Nat} : {source : Nat} → Monomial source → (Fin source → Fin target) → Monomial target
  | 0, .nil, _ => zero target
  | _ + 1, .cons exponent tail, mapping =>
      add (power (atom target (mapping 0)) exponent) (rename tail (fun index => mapping index.succ))

/-- Finite exponent multiplication evaluates to the corresponding scalar power. -/
theorem eval_power {R : Type} [CommRing R] {arity : Nat}
    (monomial : Monomial arity) (environment : Fin arity → R) (exponent : Nat) :
    (power monomial exponent).eval environment = monomial.eval environment ^ exponent := by
  induction exponent with
  | zero => rewrite [power, eval_zero, pow_zero]; rfl
  | succ exponent ih =>
      rewrite [power, eval_add, ih, pow_succ]
      rfl

/-- Renamed monomials evaluate at the original bounded pullback of the target environment. -/
theorem eval_rename {R : Type} [CommRing R] {source target : Nat}
    (monomial : Monomial source) (mapping : Fin source → Fin target) (environment : Fin target → R) :
    (rename monomial mapping).eval environment = monomial.eval (fun index => environment (mapping index)) := by
  induction monomial with
  | nil => exact eval_zero target environment
  | cons exponent tail ih =>
      change (add (power (atom target (mapping 0)) exponent)
        (rename tail (fun index => mapping index.succ))).eval environment = _
      rewrite [eval_add, eval_power, eval_atom, ih]
      rfl

end Monomial

namespace Term

/-- Retain a coefficient while renaming the bounded variables of its monomial. -/
@[expose] def rename {R : Type} {source target : Nat} (term : Term R source)
    (mapping : Fin source → Fin target) : Term R target := ⟨term.monomial.rename mapping, term.coefficient⟩

/-- Renaming a term preserves its scalar reading in the bounded pullback environment. -/
theorem eval_rename {R : Type} [CommRing R] {source target : Nat} (term : Term R source)
    (mapping : Fin source → Fin target) (environment : Fin target → R) :
    (term.rename mapping).eval environment = term.eval (fun index => environment (mapping index)) := by
  change term.coefficient * (term.monomial.rename mapping).eval environment = _
  rewrite [Monomial.eval_rename]
  rfl

end Term

namespace Terms

/-- Rename the monomials of an actual retained coefficient list without computing their coefficients again. -/
@[expose] def renamed {R : Type} {source target : Nat} (terms : List (Term R source))
    (mapping : Fin source → Fin target) : List (Term R target) := terms.map (fun term => term.rename mapping)

/-- Renaming an entire retained term list preserves its scalar reading in the bounded pullback environment. -/
theorem eval_renamed {R : Type} [CommRing R] {source target : Nat} (terms : List (Term R source))
    (mapping : Fin source → Fin target) (environment : Fin target → R) :
    eval environment (renamed terms mapping) = eval (fun index => environment (mapping index)) terms := by
  induction terms with
  | nil => rfl
  | cons first remaining ih =>
      change (first.rename mapping).eval environment + eval environment (renamed remaining mapping) = _
      rewrite [Term.eval_rename, ih]
      rfl

end Terms

namespace Sparse

/-- Rename cached coefficients and canonically combine target monomials, retaining exact target arity. -/
@[expose] def rename {R : Type} [Zero R] [Add R] [DecidableEq R] {source target : Nat}
    (polynomial : Sparse R source) (mapping : Fin source → Fin target) : Sparse R target :=
  ofTerms (Terms.renamed polynomial.terms mapping)

/-- Canonical variable renaming preserves scalar evaluation through the original bounded index map. -/
theorem eval_rename {R : Type} [CommRing R] [DecidableEq R] {source target : Nat}
    (polynomial : Sparse R source) (mapping : Fin source → Fin target) (environment : Fin target → R) :
    (polynomial.rename mapping).eval environment = polynomial.eval (fun index => environment (mapping index)) := by
  rewrite [rename, eval_ofTerms]
  exact Terms.eval_renamed polynomial.terms mapping environment

end Sparse

end Purelib.Polynomial.Multivariate

end
