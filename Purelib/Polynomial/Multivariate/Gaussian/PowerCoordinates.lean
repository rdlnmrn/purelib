module

public import Purelib.Polynomial.Multivariate.PowerCoordinates
import Purelib.Polynomial.Multivariate.PowerReduction
public import Purelib.Polynomial.Multivariate.Gaussian.Denotation
import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Sequence.Equivalence

/-!
# Operational interpretation of cached bounded power coordinates

The coordinate cache retains the original polynomial and its actual selected
variable index. Its interpretation uses that original coherent generator and
the same cached coefficients, with a comparison to the original polynomial
channel valid for every starting index and positive tolerance.
-/

public section

namespace Purelib.Polynomial.Multivariate

open Purelib.Data.Gaussian.Basic renaming Canonical -> Coefficient
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Approximation
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)

namespace Monomial

/-- A single-variable monomial compares to the supplied finite power of its original selected channel. -/
def denote_single : (arity : Nat) → (index : Fin arity) → (exponent : Nat) →
    (environment : Fin arity → CoherentNamed) →
    NamedEquivalent ((single arity index exponent).denote environment).name
      (Power.namedPower (environment index) exponent).name
  | 0, index, _, _ => Fin.elim0 index
  | arity + 1, index, exponent, environment => by
      refine Fin.cases ?_ ?_ index
      · exact NamedEquivalent.trans
          (Product.Congruence.coherentMul_respects (Power.namedPower (environment 0) exponent)
            (Power.namedPower (environment 0) exponent)
            ((zero arity).denote (fun next => environment next.succ)) (Coherence.exact 1)
            (NamedEquivalent.refl _) (denote_zero arity _))
          (Mul.coherentMul_one_right (Power.namedPower (environment 0) exponent))
      · intro tail
        exact NamedEquivalent.trans
          (Mul.coherentMul_one_left ((single arity tail exponent).denote (fun next => environment next.succ)))
          (denote_single arity tail exponent (fun next => environment next.succ))

end Monomial

namespace Term

/-- The original coefficient and a supported monomial compare to that coefficient times its generator power. -/
def denote_single {arity : Nat} (index : Fin arity) (exponent : Nat) (coefficient : Coefficient)
    (environment : Fin arity → CoherentNamed) :
    NamedEquivalent
      ((⟨Monomial.single arity index exponent, coefficient⟩ : Term Coefficient arity).denote environment).name
      (CoherentNamed.mul (Coherence.exact coefficient) (Power.namedPower (environment index) exponent)).name :=
  Product.Congruence.coherentMul_respects (Coherence.exact coefficient) (Coherence.exact coefficient)
    ((Monomial.single arity index exponent).denote environment) (Power.namedPower (environment index) exponent)
    (NamedEquivalent.refl _) (Monomial.denote_single arity index exponent environment)

end Term

namespace Terms

/-- Reconstruct cached power entries at their actual original variable index. -/
@[expose] def singlePowers {arity degree : Nat} (index : Fin arity) (entries : List (Fin degree × Coefficient)) :
    List (Term Coefficient arity) :=
  entries.map (fun entry => ⟨Monomial.single arity index entry.1.val, entry.2⟩)

/-- Interpret the cached bounded powers at the same original coherent generator in their retained order. -/
@[expose] def denotePowers {degree : Nat} (generator : CoherentNamed) : List (Fin degree × Coefficient) → CoherentNamed
  | [] => Coherence.exact 0
  | first :: remaining =>
      CoherentNamed.add (CoherentNamed.mul (Coherence.exact first.2) (Power.namedPower generator first.1.val))
        (denotePowers generator remaining)

/-- Reconstruction of cached powers preserves their original multivariate term interpretation. -/
def denote_singlePowers {arity degree : Nat} (index : Fin arity) (environment : Fin arity → CoherentNamed) :
    (entries : List (Fin degree × Coefficient)) →
    NamedEquivalent
      (denote environment (singlePowers index entries)).name
      (denotePowers (environment index) entries).name
  | [] => NamedEquivalent.refl _
  | first :: remaining => by
      let originalHead :=
        (⟨Monomial.single arity index first.1.val, first.2⟩ : Term Coefficient arity).denote environment
      let powerHead := CoherentNamed.mul (Coherence.exact first.2) (Power.namedPower (environment index) first.1.val)
      let originalTail := denote environment (singlePowers index remaining)
      let powerTail := denotePowers (environment index) remaining
      have headComparison : NamedEquivalent originalHead.name powerHead.name :=
        Term.denote_single index first.1.val first.2 environment
      have tailComparison : NamedEquivalent originalTail.name powerTail.name :=
        denote_singlePowers index environment remaining
      exact Sum.Congruence.coherentAdd_respects originalHead powerHead originalTail powerTail
        headComparison tailComparison

/-- Build dense coefficient data from the same bounded power entries in their retained order. -/
@[expose] def densePowers {degree : Nat} : List (Fin degree × Coefficient) → CoefficientPolynomial
  | [] => DensePolynomial.constant 0
  | first :: remaining =>
      (DensePolynomial.shift first.1.val (DensePolynomial.constant first.2)).add (densePowers remaining)

/-- Read the same ordered cached entries at a supplied exact Gaussian point. -/
@[expose] def evalPowers {degree : Nat} (point : Coefficient) : List (Fin degree × Coefficient) → Coefficient
  | [] => 0
  | first :: remaining => first.2 * point ^ first.1.val + evalPowers point remaining

/-- Dense power readback keeps every actual coefficient and exponent at the same scalar point. -/
theorem densePowers_eval {degree : Nat} (point : Coefficient) :
    (entries : List (Fin degree × Coefficient)) → (densePowers entries).eval point = evalPowers point entries
  | [] => DensePolynomial.eval_constant 0 point
  | first :: remaining => by
      change ((DensePolynomial.shift first.1.val (DensePolynomial.constant first.2)).add
        (densePowers remaining)).eval point = _
      calc
        _ = (DensePolynomial.shift first.1.val (DensePolynomial.constant first.2)).eval point +
            (densePowers remaining).eval point := DensePolynomial.eval_add _ _ point
        _ = _ := by
          rewrite [DensePolynomial.eval_shift, DensePolynomial.eval_constant, densePowers_eval point remaining]
          rfl

end Terms

namespace Monomial

/-- The retained zero-monomial products compare to the exact unit through their actual powers and suffixes. -/
private def Products.zero_equivalent : (arity : Nat) →
    {environment : Fin arity → CoherentNamed} → {channel : CoherentNamed} →
    Products (zero arity) environment channel → NamedEquivalent channel.name (Coherence.exact 1).name
  | 0, _, _, .nil _ _ same => by
      rewrite [same]
      exact NamedEquivalent.refl _
  | arity + 1, _, _, .cons _ _ _ power power_eq tailChannel tail _ same => by
      have powers : NamedEquivalent power.name (Coherence.exact 1).name := by
        rewrite [power_eq]
        exact NamedEquivalent.refl _
      have agreement := (Product.Congruence.coherentMul_respects power (Coherence.exact 1)
        tailChannel (Coherence.exact 1) powers (Products.zero_equivalent arity tail)).trans
          (Mul.coherentMul_one_left (Coherence.exact 1))
      change NamedEquivalent (CoherentNamed.mul power tailChannel).name (Coherence.exact 1).name at agreement
      rewrite [← same] at agreement
      exact agreement

/-- A supported original monomial compares to its actual selected stored power, retaining every suffix channel. -/
private def Products.single_equivalentAux : (arity : Nat) → (index : Fin arity) → (exponent : Nat) →
    {environment : Fin arity → CoherentNamed} → {channel : CoherentNamed} →
    (products : Products (single arity index exponent) environment channel) →
    NamedEquivalent channel.name (products.powerAt index).val.name
  | 0, index, _, _, _, _ => Fin.elim0 index
  | arity + 1, index, exponent, _, _, products => by
      revert products
      refine Fin.cases ?_ ?_ index
      · intro products
        cases products with
        | cons _ _ _ power power_eq tailChannel tail channel same =>
            have agreement := (Product.Congruence.coherentMul_respects power power
              tailChannel (Coherence.exact 1) (NamedEquivalent.refl _) (Products.zero_equivalent arity tail)).trans
                (Mul.coherentMul_one_right power)
            change NamedEquivalent (CoherentNamed.mul power tailChannel).name power.name at agreement
            rewrite [← same] at agreement
            exact agreement
      · intro tailIndex products
        cases products with
        | cons _ _ _ power power_eq tailChannel tail channel same =>
            have powers : NamedEquivalent power.name (Coherence.exact 1).name := by
              rewrite [power_eq]
              exact NamedEquivalent.refl _
            have agreement := (Product.Congruence.coherentMul_respects power (Coherence.exact 1)
              tailChannel tailChannel powers (NamedEquivalent.refl _)).trans
                ((Mul.coherentMul_one_left tailChannel).trans
                  (Products.single_equivalentAux arity tailIndex exponent tail))
            change NamedEquivalent (CoherentNamed.mul power tailChannel).name
              (tail.powerAt tailIndex).val.name at agreement
            rewrite [← same] at agreement
            exact agreement

/-- Compare one actual original product cache to its retained selected power under exact single-variable support. -/
def Products.single_equivalent {arity : Nat} {monomial : Monomial arity}
    {environment : Fin arity → CoherentNamed} {channel : CoherentNamed}
    (products : Products monomial environment channel) (index : Fin arity) (exponent : Nat)
    (same : monomial = single arity index exponent) :
    NamedEquivalent channel.name (products.powerAt index).val.name := by
  cases same
  exact Products.single_equivalentAux arity index exponent products

end Monomial

namespace Term

/-- Compare the actual original coefficient and monomial caches to their same scalar source power.

The retained term product is the endpoint, and both operands of its operational
comparison are the original stored coefficient and monomial channel.
-/
def Denotation.singleSource_agrees {arity degree : Nat} {environment : Fin arity → CoherentNamed}
    {term : Term Coefficient arity} (retained : Denotation environment term)
    (index : Fin arity) (exponent : Fin degree) (same : term.monomial = Monomial.single arity index exponent.val)
    (source : GeometricApproximation)
    (sourceEq : NamedEquivalent (environment index).name source.toApproximation.toNamed)
    (powers : Monomial.PowerPrefix (environment index) degree) :
    NamedEquivalent retained.channel.name
      ((GeometricApproximation.exact term.coefficient).mul
        (CoherentEvaluation.powerSource source exponent.val)).toApproximation.toNamed := by
  let actual := retained.monomial.products.powerAt index
  have exponent_eq : term.monomial.exponentAt index = exponent.val :=
    (congrArg (fun monomial => monomial.exponentAt index) same).trans
      (Monomial.exponentAt_single arity index exponent.val)
  let selected : {channel : CoherentNamed // channel = Power.namedPower (environment index) exponent.val} :=
    ⟨actual.val, actual.property.trans (congrArg (Power.namedPower (environment index)) exponent_eq)⟩
  have monomial := (retained.monomial.products.single_equivalent index exponent.val same).trans
    (Monomial.powerFrom_agrees (environment index) source sourceEq powers exponent selected)
  have coefficient := CoherentEvaluation.exact_agrees term.coefficient
  rewrite [← retained.coefficient_eq] at coefficient
  have agreement := CoherentEvaluation.mul_agrees retained.coefficient retained.monomial.channel
    (GeometricApproximation.exact term.coefficient) (CoherentEvaluation.powerSource source exponent.val)
    coefficient monomial
  rewrite [← retained.product_eq] at agreement
  exact agreement

end Term

namespace Terms

/-- Sample the same ordered coordinate entries at the original selected geometric source. -/
@[expose] def sourcePowers {degree : Nat} (source : GeometricApproximation) :
    List (Fin degree × Coefficient) → GeometricApproximation
  | [] => GeometricApproximation.exact 0
  | first :: remaining =>
      ((GeometricApproximation.exact first.2).mul (CoherentEvaluation.powerSource source first.1.val)).add
        (sourcePowers source remaining)

/-- The ordered coordinate source reads exactly the same finite scalar power sum at each original sample. -/
theorem sourcePowers_sample {degree : Nat} (source : GeometricApproximation) (index : Nat) :
    (entries : List (Fin degree × Coefficient)) →
    (sourcePowers source entries).sample index = evalPowers (source.sample index) entries
  | [] => rfl
  | first :: remaining => by
      change (((GeometricApproximation.exact first.2).mul
        (CoherentEvaluation.powerSource source first.1.val)).add (sourcePowers source remaining)).sample index = _
      rewrite [GeometricApproximation.add_sample, GeometricApproximation.mul_sample,
        GeometricApproximation.exact_sample, CoherentEvaluation.powerSource_sample, sourcePowers_sample]
      rfl

/-- Compare each original cached term and suffix sum directly to the same ordered coordinate source. -/
private def Sums.singlePowers_agrees {arity degree : Nat} {environment : Fin arity → CoherentNamed}
    (index : Fin arity) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent (environment index).name source.toApproximation.toNamed)
    (powers : Monomial.PowerPrefix (environment index) degree) :
    (entries : List (Fin degree × Coefficient)) → {channel : CoherentNamed} →
    Sums environment (singlePowers index entries) channel →
    NamedEquivalent channel.name (sourcePowers source entries).toApproximation.toNamed
  | [], _, .nil _ same => by
      have agreement := CoherentEvaluation.exact_agrees (0 : Coefficient)
      rewrite [← same] at agreement
      exact agreement
  | first :: remaining, _, .cons _ _ head tailChannel tail _ same => by
      have firstAgreement := head.singleSource_agrees index first.1 rfl source sourceEq powers
      have tailAgreement := Sums.singlePowers_agrees index source sourceEq powers remaining tail
      have agreement := CoherentEvaluation.add_agrees head.channel tailChannel
        ((GeometricApproximation.exact first.2).mul (CoherentEvaluation.powerSource source first.1.val))
        (sourcePowers source remaining) firstAgreement tailAgreement
      rewrite [← same] at agreement
      exact agreement

/-- Compare the original retained sum directly to the source evaluation of its unchanged dense coordinate cache.

The exact term-list equation transports only the retained sum index. No
monomial evaluator, coherent finite power or dense basis evaluator is invoked
to produce a substitute numerical channel.
-/
def Denotation.densePowers_agrees {arity degree : Nat} {environment : Fin arity → CoherentNamed}
    {terms : List (Term Coefficient arity)} (retained : Denotation environment terms)
    (index : Fin arity) (entries : List (Fin degree × Coefficient))
    (same : terms = singlePowers index entries) (source : GeometricApproximation)
    (sourceEq : NamedEquivalent (environment index).name source.toApproximation.toNamed)
    (powers : Monomial.PowerPrefix (environment index) degree) :
    NamedEquivalent retained.channel.name
      (Evaluation.evaluate (densePowers entries) source).toApproximation.toNamed := by
  cases same
  have agreement := Sums.singlePowers_agrees index source sourceEq powers entries retained.sums
  have samples := Sequence.Equivalence.approximationEquivalentOfSamplesEq
    (sourcePowers source entries).toApproximation (Evaluation.evaluate (densePowers entries) source).toApproximation
    (fun sample => by
      rewrite [GeometricApproximation.toApproximation_sample, GeometricApproximation.toApproximation_sample,
        sourcePowers_sample, Evaluation.evaluate_sample, densePowers_eval]
      rfl)
  exact agreement.trans samples.toNamed

end Terms

namespace Sparse.PowerCoordinates

/-- Interpret the actual cached coordinates using the same selected original coherent variable. -/
@[expose] def denote {arity degree : Nat} {polynomial : Sparse Coefficient arity} {index : Fin arity}
    (coordinates : PowerCoordinates polynomial index degree) (environment : Fin arity → CoherentNamed) :
    CoherentNamed := Terms.denotePowers (environment index) coordinates.entries

/-- Cached coordinates compare to the entire original polynomial channel through their exact reconstruction law. -/
def equivalent {arity degree : Nat} {polynomial : Sparse Coefficient arity} {index : Fin arity}
    (coordinates : PowerCoordinates polynomial index degree) (environment : Fin arity → CoherentNamed) :
    NamedEquivalent (polynomial.denote environment).name (coordinates.denote environment).name := by
  change NamedEquivalent (Terms.denote environment polynomial.terms).name _
  rewrite [coordinates.terms_eq]
  exact Terms.denote_singlePowers index environment coordinates.entries

/-- Read the exact dense polynomial determined by this original coordinate cache. -/
@[expose] def dense {arity degree : Nat} {polynomial : Sparse Coefficient arity} {index : Fin arity}
    (coordinates : PowerCoordinates polynomial index degree) : CoefficientPolynomial :=
  Terms.densePowers coordinates.entries

/-- The actual retained polynomial interpretation compares to its unchanged dense coordinate evaluation.

The complete original denotation supplies every coefficient, selected power,
product and suffix sum. The supplied predecessor bank shares existing powers
and provides only the missing powers needed by this finite comparison.
-/
def dense_equivalent {arity degree : Nat} {polynomial : Sparse Coefficient arity} {index : Fin arity}
    (coordinates : PowerCoordinates polynomial index degree) (environment : Fin arity → CoherentNamed)
    (source : GeometricApproximation)
    (sourceEq : NamedEquivalent (environment index).name source.toApproximation.toNamed)
    (retained : Terms.Denotation environment polynomial.terms)
    (powers : Monomial.PowerPrefix (environment index) degree) :
    NamedEquivalent retained.channel.name
      (Horner.polynomialEval coordinates.dense (environment index)).name :=
  (retained.densePowers_agrees index coordinates.entries coordinates.terms_eq source sourceEq powers).trans
    (CoherentEvaluation.evaluate_agrees coordinates.dense (environment index) source sourceEq).symm

end Sparse.PowerCoordinates

end Purelib.Polynomial.Multivariate

end
