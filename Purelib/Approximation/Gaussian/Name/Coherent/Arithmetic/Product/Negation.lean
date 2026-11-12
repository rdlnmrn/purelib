module

public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Data.Fin

/-!
# Operational negation of retained coherent products

The shared polynomial normalizer compares the actual product and negation
processes over the same original two coherent bindings. The finite coefficient
identities preserve both input channels without identifying their samples.
-/

public section

namespace Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Negation

open Purelib
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Multivariate.Gaussian (Normalized)

/-- Multiplying the actual negated right channel agrees operationally with negating the actual original product. -/
def neg_right (left right : CoherentNamed) :
    NamedEquivalent (left.mul right.neg).name (left.mul right).neg.name := by
  let bindings : Fin 2 → CoherentNamed := Data.Fin.cases left (fun _ => right)
  let first := Normalized.atom bindings 0
  let second := Normalized.atom bindings 1
  let source := first.mul second.neg
  let target := (first.mul second).neg
  have forms : source.form.terms = target.form.terms := by
    dsimp only [source, target, first, second]
    simp only [Normalized.mul_form, Normalized.neg_form, Normalized.atom_form, -eq_self, -iff_self]
    decide +kernel
  exact source.compare target forms

end Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Negation
