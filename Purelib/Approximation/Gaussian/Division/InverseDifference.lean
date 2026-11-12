module

public import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Polynomial.Multivariate.Gaussian.Normalization
import Purelib.Data.Fin
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Coherent.Additive

/-! # Cleared inverse differences of retained coherent channels

The original two denominator guards justify only their actual quotients.
Finite polynomial normalization checks the rearrangement and the difference
of squares without preparing a third denominator.
-/

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence (coherentAdd_respects)
open Purelib.Approximation.Gaussian.Coherent.Additive (coherentNeg_respects)

namespace Purelib.Approximation.Gaussian.Division.Cancellation

open Purelib
open Purelib.Polynomial.Multivariate.Gaussian (Normalized)

/-- Reassociate the retained two quotient channels before their original denominator cancellations. -/
private def inverse_difference_cross_rearrange (first second inverse quotient : CoherentNamed) :
    NamedEquivalent ((inverse.add quotient.neg).mul (second.mul first)).name
      ((second.mul (inverse.mul first)).add (first.mul (quotient.mul second)).neg).name := by
  let bindings : Fin 4 → CoherentNamed :=
    Data.Fin.cases first (Data.Fin.cases second (Data.Fin.cases inverse (fun _ => quotient)))
  let a := Normalized.atom bindings 0
  let b := Normalized.atom bindings 1
  let u := Normalized.atom bindings 2
  let q := Normalized.atom bindings 3
  let source := (u.add q.neg).mul (b.mul a)
  let target := (b.mul (u.mul a)).add (a.mul (q.mul b)).neg
  have same : source.form.terms = target.form.terms := by
    dsimp only [source, target, a, b, u, q]
    simp only [Normalized.mul_form, Normalized.add_form, Normalized.neg_form, Normalized.atom_form,
      -eq_self, -iff_self]
    decide +kernel
  exact source.compare target same

/-- The difference and sum of two retained original channels multiply to their original square difference. -/
private def difference_squares (first second : CoherentNamed) :
    NamedEquivalent ((first.add second.neg).mul (first.add second)).name
      ((first.mul first).add (second.mul second).neg).name := by
  let bindings : Fin 2 → CoherentNamed := Data.Fin.cases first (fun _ => second)
  let a := Normalized.atom bindings 0
  let b := Normalized.atom bindings 1
  let source := (a.add b.neg).mul (a.add b)
  let target := (a.mul a).add (b.mul b).neg
  have same : source.form.terms = target.form.terms := by
    dsimp only [source, target, a, b]
    simp only [Normalized.mul_form, Normalized.add_form, Normalized.neg_form, Normalized.atom_form,
      -eq_self, -iff_self]
    decide +kernel
  exact source.compare target same

/-- Rationalize an actual inverse difference using only its two original denominator guards.

The cleared identity is `(1/a-h/b)ba(b+ah)=b²-a²h²`. The factor `b+ah`
is multiplied, never divided, so the identity asserts no extra denominator
admission or local regularity. Both quotients use the supplied original
channels and their actual apartness certificates.
-/
public def inverse_difference_cleared (first second coefficient : CoherentNamed)
    (firstApart : Named.Apart first.name) (secondApart : Named.Apart second.name) :
    let inverse := CoherentNamed.div (Coherence.exact 1) first firstApart
    let quotient := CoherentNamed.div coefficient second secondApart
    NamedEquivalent
      (((inverse.add quotient.neg).mul (second.mul first)).mul (second.add (first.mul coefficient))).name
      ((second.mul second).add ((first.mul first).mul (coefficient.mul coefficient)).neg).name := by
  let inverse := CoherentNamed.div (Coherence.exact 1) first firstApart
  let quotient := CoherentNamed.div coefficient second secondApart
  let bindings : Fin 3 → CoherentNamed :=
    Data.Fin.cases first (Data.Fin.cases second (fun _ => coefficient))
  let a := Normalized.atom bindings 0
  let b := Normalized.atom bindings 1
  let h := Normalized.atom bindings 2
  let firstCancellation := Normalized.ofRational bindings
    (⟨1, coherentDiv_mul_cancel (Coherence.exact 1) first firstApart⟩ :
      Provenance.Rational.Basic.RationalSidecar (inverse.mul first))
  let secondCancellation := Normalized.ofAtomComparison bindings 2
    (coherentDiv_mul_cancel coefficient second secondApart)
  let cleared := (b.mul firstCancellation).add (a.mul secondCancellation).neg
  let cross := b.add (a.mul h).neg
  have same : cleared.form.terms = cross.form.terms := by
    dsimp only [cleared, cross, firstCancellation, secondCancellation, a, b, h]
    simp only [Normalized.mul_form, Normalized.add_form, Normalized.neg_form, Normalized.ofRational_form,
      Normalized.ofAtomComparison_form, Normalized.atom_form, -eq_self, -iff_self]
    decide +kernel
  have crossIdentity := (inverse_difference_cross_rearrange first second inverse quotient).trans
    (cleared.compare cross same)
  dsimp only [bindings, Data.Fin.cases] at crossIdentity
  exact (Congruence.coherentMul_respects
    ((inverse.add quotient.neg).mul (second.mul first)) (second.add (first.mul coefficient).neg)
    (second.add (first.mul coefficient)) (second.add (first.mul coefficient))
    crossIdentity (NamedEquivalent.refl _)).trans
      ((difference_squares second (first.mul coefficient)).trans
        (coherentAdd_respects (second.mul second) (second.mul second)
          ((first.mul coefficient).mul (first.mul coefficient)).neg
          ((first.mul first).mul (coefficient.mul coefficient)).neg
          (NamedEquivalent.refl _)
          (coherentNeg_respects _ _
            (Laws.coherentMul_squares_interchange first coefficient).symm)))

end Purelib.Approximation.Gaussian.Division.Cancellation
