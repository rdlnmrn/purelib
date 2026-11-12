module

public import Purelib.Approximation.Gaussian.Division.Prepared.Basic
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
public import Purelib.Approximation.Gaussian.Process.Apart.Possible
public import Purelib.Approximation.Gaussian.Name.Coherent.Power
public import Purelib.Approximation.Gaussian.Name.Coherent.Conjugation
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
public import Purelib.Approximation.Gaussian.Division.Prepared.Rational
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Process.Conjugation
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Name.Coherent.Apart
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Preparing the original product of two apart coherent names

The original operand processes and their paired candidate states give a
positive product-candidate floor. Existing apartification refines the exact
retained product, keeping its operational comparison and original state tree.
The construction does not require its coarse product balls to be apart.
-/

public section

namespace Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- All actual product candidates inherit the product of the two original whole-ball norm floors. -/
def productPossibleApart (left right : CoherentNamed)
    (leftApart : Named.Apart left.name) (rightApart : Named.Apart right.name) :
    Process.Apart.Possible.PossibleApart (left.mul right).name.process where
  lowerSq := leftApart.certificate.lowerSq * rightApart.certificate.lowerSq
  positive := Fraction.Order.Arithmetic.mul_pos_direct leftApart.certificate.positive rightApart.certificate.positive
  lower := by
    intro state value possible
    rcases possible with ⟨first, last, firstPossible, lastPossible, rfl⟩
    rewrite [Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      (leftApart.certificate.lower state.1 (left.name.process.possible_inside firstPossible))
      (rightApart.certificate.lower state.2 (right.name.process.possible_inside lastPossible))
      rightApart.certificate.positive.le (Norm.Basic.normSq_nonneg _)

/-- The product-candidate certificate retains the exact original two floors. -/
theorem productPossibleApart_lowerSq (left right : CoherentNamed)
    (leftApart : Named.Apart left.name) (rightApart : Named.Apart right.name) :
    (productPossibleApart left right leftApart rightApart).lowerSq =
      leftApart.certificate.lowerSq * rightApart.certificate.lowerSq := by
  unfold productPossibleApart
  rfl

/-- Transport the candidate certificate to the identical retained original product input. -/
def retainedProductApart (product left right : CoherentNamed) (retained : product = left.mul right)
    (leftApart : Named.Apart left.name) (rightApart : Named.Apart right.name) :
    Process.Apart.Possible.PossibleApart product.name.process :=
  Eq.mp (congrArg (fun value : CoherentNamed => Process.Apart.Possible.PossibleApart value.name.process) retained.symm)
    (productPossibleApart left right leftApart rightApart)

/-- Prepare the actual retained product by refining its own paired operand-state tree.

The original product and both complete operands remain inputs. Only the
candidate-apartness certificate is reindexed along their exact construction
equation. The retained product itself supplies the executable preparation and
the operational comparison to its division-ready presentation.
-/
def ofProduct (product left right : CoherentNamed) (retained : product = left.mul right)
    (leftApart : Named.Apart left.name) (rightApart : Named.Apart right.name) : Division.Prepared product :=
  let lower := retainedProductApart product left right retained leftApart rightApart
  { denominator := product.apartify lower
    apart := ⟨Process.Apart.Preparation.apartifyApart lower⟩
    equivalent := product.apartifyEquivalent lower }

/-- The actual product preparation retains the original product's apartified process and state. -/
theorem ofProduct_denominator (product left right : CoherentNamed) (retained : product = left.mul right)
    (leftApart : Named.Apart left.name) (rightApart : Named.Apart right.name) :
    (ofProduct product left right retained leftApart rightApart).denominator =
      product.apartify (retainedProductApart product left right retained leftApart rightApart) := by
  unfold ofProduct
  rfl

/-- Prepare the original product from both actual retained apart presentations.

Both original channels remain the numerical input. The shared product builder
consumes the supplied prepared operands and their positive floors, and only
its operational comparison is transported back to the original product.
-/
def mul {first second : CoherentNamed} (left : Division.Prepared first) (right : Division.Prepared second) :
    Division.Prepared (first.mul second) :=
  let product := left.denominator.mul right.denominator
  let prepared := ofProduct product left.denominator right.denominator rfl left.apart right.apart
  let equivalent := Product.Congruence.coherentMul_respects first left.denominator
    second right.denominator left.equivalent right.equivalent
  prepared.transport equivalent.symm

/-- Product preparation stores the actual apartified product of both supplied prepared presentations. -/
theorem mul_denominator {first second : CoherentNamed}
    (left : Division.Prepared first) (right : Division.Prepared second) :
    (left.mul right).denominator =
      (ofProduct (left.denominator.mul right.denominator) left.denominator right.denominator rfl
        left.apart right.apart).denominator := by
  unfold mul
  rfl

/-- The prepared product retains the original two floors with the shared apartification factor. -/
theorem mul_lowerSq {first second : CoherentNamed}
    (left : Division.Prepared first) (right : Division.Prepared second) :
    (left.mul right).apart.certificate.lowerSq =
      (left.apart.certificate.lowerSq * right.apart.certificate.lowerSq) / 8 := by
  unfold mul ofProduct retainedProductApart productPossibleApart
  rfl

/-- Prepare each actual finite power using the same retained input and shared prepared-product operation. -/
def pow {channel : CoherentNamed} (prepared : Division.Prepared channel) :
    (exponent : Nat) → Division.Prepared (Power.namedPower channel exponent)
  | 0 => Provenance.Rational.Basic.RationalSidecar.prepare
      (Provenance.Rational.Basic.RationalSidecar.exact 1) BoundaryCanonical.one_ne_zero
  | exponent + 1 => (prepared.pow exponent).mul prepared

/-- The zero power retains the actual exact-unit preparation. -/
theorem pow_zero {channel : CoherentNamed} (prepared : Division.Prepared channel) :
    prepared.pow 0 = Provenance.Rational.Basic.RationalSidecar.prepare
      (Provenance.Rational.Basic.RationalSidecar.exact 1) BoundaryCanonical.one_ne_zero := by
  unfold pow
  rfl

/-- A power successor consumes the exact preceding prepared power and same original input preparation. -/
theorem pow_succ {channel : CoherentNamed} (prepared : Division.Prepared channel) (exponent : Nat) :
    prepared.pow (exponent + 1) = (prepared.pow exponent).mul prepared := by
  conv =>
    lhs
    unfold pow

/-- Conjugate a retained preparation at the actual conjugated channel without another observation. -/
def conj {channel : CoherentNamed} (prepared : Division.Prepared channel) :
    Division.Prepared (CoherentNamed.conj channel) where
  denominator := CoherentNamed.conj prepared.denominator
  apart := ⟨prepared.apart.certificate.conj⟩
  equivalent := CoherentNamed.conj_respects prepared.equivalent

/-- The actual conjugated presentation retains the same uniform lower quadrance. -/
theorem conj_lowerSq {channel : CoherentNamed} (prepared : Division.Prepared channel) :
    prepared.conj.apart.certificate.lowerSq = prepared.apart.certificate.lowerSq := by
  unfold conj
  exact Process.Apart.conj_lowerSq prepared.apart.certificate

end Purelib.Approximation.Gaussian.Division.Prepared
