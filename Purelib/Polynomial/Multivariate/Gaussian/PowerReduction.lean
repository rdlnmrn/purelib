module

public import Purelib.Polynomial.Multivariate.PowerReduction
public import Purelib.Polynomial.Multivariate.Gaussian.Normalization
public import Purelib.Approximation.Gaussian.Provenance.Power.Reduction
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic

/-!
# Operational reduction of retained polynomial powers

The relation is supplied at one actual bounded original generator channel.
Reduction changes coefficient data and the selected exponent, while the
original numerical evaluator remains the source of its cached comparison.
-/

public section

namespace Purelib.Polynomial.Multivariate

open Purelib.Data.Gaussian.Basic renaming Canonical -> Coefficient
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)

namespace Monomial

/-- Reduce the original monomial channel using the retained equation at its actual bounded generator index. -/
def denote_reduceAt : {arity : Nat} → (monomial : Monomial arity) → (index : Fin arity) →
    (degree : Nat) → (parameter : Coefficient) → (environment : Fin arity → CoherentNamed) →
    PowerIdentity (environment index) degree parameter →
    NamedEquivalent (monomial.denote environment).name
      (CoherentNamed.mul (Coherence.exact (reduceAt degree parameter monomial index).1)
        ((reduceAt degree parameter monomial index).2.denote environment)).name
  | 0, .nil, index, _, _, _, _ => Fin.elim0 index
  | _ + 1, .cons exponent tail, index, degree, parameter, environment, relation => by
      revert relation
      refine Fin.cases ?_ ?_ index
      · intro relation
        let coefficient := Coherence.exact (parameter ^ (exponent / degree))
        let remainder := Power.namedPower (environment 0) (exponent % degree)
        let tailChannel := tail.denote (fun next => environment next.succ)
        exact NamedEquivalent.trans
          (Product.Congruence.coherentMul_respects (Power.namedPower (environment 0) exponent)
            (CoherentNamed.mul coefficient remainder) tailChannel tailChannel (relation.reduce exponent)
            (NamedEquivalent.refl _))
          (Product.Laws.coherentMul_assoc coefficient remainder tailChannel)
      · intro tailIndex relation
        let tailEnvironment := fun next : Fin _ => environment next.succ
        let reduced := reduceAt degree parameter tail tailIndex
        let coefficient := Coherence.exact reduced.1
        let head := Power.namedPower (environment 0) exponent
        let tailChannel := reduced.2.denote tailEnvironment
        exact NamedEquivalent.trans
          (Product.Congruence.coherentMul_respects head head (tail.denote tailEnvironment)
            (CoherentNamed.mul coefficient tailChannel) (NamedEquivalent.refl _)
            (denote_reduceAt tail tailIndex degree parameter tailEnvironment relation))
          (NamedEquivalent.trans (NamedEquivalent.symm (Product.Laws.coherentMul_assoc head coefficient tailChannel))
            (NamedEquivalent.trans
              (Product.Congruence.coherentMul_respects (CoherentNamed.mul head coefficient)
                (CoherentNamed.mul coefficient head) tailChannel tailChannel
                (Product.Laws.coherentMul_comm head coefficient) (NamedEquivalent.refl _))
              (Product.Laws.coherentMul_assoc coefficient head tailChannel)))

end Monomial

namespace Term

/-- Move a retained monomial's whole generator powers into its exact coefficient without changing its source channel. -/
def denote_reduceAt {arity : Nat} (term : Term Coefficient arity) (index : Fin arity)
    (degree : Nat) (parameter : Coefficient) (environment : Fin arity → CoherentNamed)
    (relation : PowerIdentity (environment index) degree parameter) :
    NamedEquivalent (term.denote environment).name ((term.reduceAt index degree parameter).denote environment).name :=
  let reduced := term.monomial.reduceAt degree parameter index
  let coefficient := Coherence.exact term.coefficient
  let factor := Coherence.exact reduced.1
  let remainder := reduced.2.denote environment
  NamedEquivalent.trans
    (Product.Congruence.coherentMul_respects coefficient coefficient (term.monomial.denote environment)
      (CoherentNamed.mul factor remainder) (NamedEquivalent.refl _)
      (Monomial.denote_reduceAt term.monomial index degree parameter environment relation))
    (NamedEquivalent.trans (NamedEquivalent.symm (Product.Laws.coherentMul_assoc coefficient factor remainder))
      (Product.Congruence.coherentMul_respects (CoherentNamed.mul coefficient factor)
        (Coherence.exact (term.coefficient * reduced.1)) remainder remainder
        (Exact.Arithmetic.exact_mul term.coefficient reduced.1) (NamedEquivalent.refl _)))

end Term

namespace Terms

/-- Reduction transports an actual retained finite coefficient sum through its original generator equation. -/
def denote_reducedAt {arity : Nat} (index : Fin arity) (degree : Nat) (parameter : Coefficient)
    (environment : Fin arity → CoherentNamed) (relation : PowerIdentity (environment index) degree parameter) :
    (terms : List (Term Coefficient arity)) →
    NamedEquivalent (denote environment terms).name (denote environment (reducedAt terms index degree parameter)).name
  | [] => NamedEquivalent.refl _
  | first :: remaining =>
      Sum.Congruence.coherentAdd_respects (first.denote environment)
        ((first.reduceAt index degree parameter).denote environment) (denote environment remaining)
        (denote environment (reducedAt remaining index degree parameter))
        (first.denote_reduceAt index degree parameter environment relation)
        (denote_reducedAt index degree parameter environment relation remaining)

end Terms

namespace Sparse

/-- Canonical reduction preserves the original polynomial channel at the supplied original generator relation. -/
def denote_reduceAt {arity : Nat} (polynomial : Sparse Coefficient arity) (index : Fin arity)
    (degree : Nat) (parameter : Coefficient) (environment : Fin arity → CoherentNamed)
    (relation : PowerIdentity (environment index) degree parameter) :
    NamedEquivalent (polynomial.denote environment).name
      ((polynomial.reduceAt index degree parameter).denote environment).name :=
  NamedEquivalent.trans (Terms.denote_reducedAt index degree parameter environment relation polynomial.terms)
    (NamedEquivalent.symm (denote_ofTerms environment (Terms.reducedAt polynomial.terms index degree parameter)))

end Sparse

namespace Gaussian.Normalized

/-- Reduce the actual cached form using a relation at its retained bounded generator channel. -/
@[expose] def reduceAt {arity : Nat} {original : CoherentNamed} {bindings : Fin arity → CoherentNamed}
    (normalized : Gaussian.Normalized bindings original) (index : Fin arity) (degree : Nat) (parameter : Coefficient)
    (relation : PowerIdentity (bindings index) degree parameter) : Gaussian.Normalized bindings original := by
  let form := normalized.form.reduceAt index degree parameter
  have reduced := Sparse.denote_reduceAt normalized.form index degree parameter bindings relation
  rewrite [← normalized.channel_eq] at reduced
  exact ofForm bindings form (NamedEquivalent.trans normalized.equivalent reduced) normalized.denotation.findMonomial

/-- Generator reduction computes its form from the actual retained input coefficients. -/
theorem reduceAt_form {arity : Nat} {original : CoherentNamed} {bindings : Fin arity → CoherentNamed}
    (normalized : Gaussian.Normalized bindings original) (index : Fin arity) (degree : Nat) (parameter : Coefficient)
    (relation : PowerIdentity (bindings index) degree parameter) :
    (normalized.reduceAt index degree parameter relation).form = normalized.form.reduceAt index degree parameter := rfl

end Gaussian.Normalized

end Purelib.Polynomial.Multivariate

end
