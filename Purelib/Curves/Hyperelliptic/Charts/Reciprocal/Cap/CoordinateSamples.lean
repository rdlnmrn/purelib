module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Sampling
public import Purelib.Approximation.Gaussian.Quotient.Geometric
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Field
import Init.Prelude
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Quotient

open Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

section
@[expose] public section

/-!
# Finite inverse-product readings of the retained cap coordinate

The comparison polynomial uses q A B. Its operational counterpart reads the
same two retained root owners and forms (q/root(q)) (1/root(R)). The square
and reconstruction certificates identify that stream with the actual cap
coordinate, without treating its rational readings as exact square roots.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples

open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames (Gaussian)
open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (RootCoordinate)
open _root_.Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open _root_.Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open _root_.Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul div ofApproximation)
open _root_.Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent)
open _root_.Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence (coherentMul_respects)
open _root_.Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws (coherentMul_comm coherentMul_assoc)
open _root_.Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open _root_.Purelib.Riemann.RootContinuation.CertifiedSquareRoot (Certificate)

/-- Multiply the synchronized quotient streams for the original numerator and denominator root certificates. -/
def inverseProduct {first second :
  ReciprocalRootNames.Gaussian} (numerator : Certificate first) (denominator : Certificate second) :
    GeometricApproximation :=
  (Geometric.quotientStream (exact first) numerator.value numerator.apart).mul
    (Geometric.quotientStream (exact 1) denominator.value denominator.apart)

/-- The retained product stream sample is exactly the numerator times the inverses of both original root samples. -/
theorem inverseProduct_sample {first second
  : ReciprocalRootNames.Gaussian} (numerator : Certificate first) (denominator : Certificate second)
    (index : Nat) : (inverseProduct numerator
      denominator).sample index =
    first * Data.Gaussian.Field.inv ((Sampling.approximation numerator.value.name).sample index) *
      Data.Gaussian.Field.inv ((Sampling.approximation denominator.value.name).sample index) := by
  change (first / _ ) * ((1 : ReciprocalRootNames.Gaussian) / _) = _
  rw [Algebra.Field.ExplicitField.div_eq_mul_inv, Algebra.Field.ExplicitField.div_eq_mul_inv, _root_.one_mul]
  rw [Data.Gaussian.Field.inv_eq, Data.Gaussian.Field.inv_eq]

/-- The product of the original coherent quotient channels is equivalent to the synchronized retained product stream. -/
public def inverseProduct_raw {first second
  : ReciprocalRootNames.Gaussian} (numerator : Certificate first) (denominator : Certificate second) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul (CoherentNamed.div (exact first) numerator.value numerator.apart) (CoherentNamed.div (exact 1)
        denominator.value denominator.apart)).name
      (inverseProduct numerator
        denominator).toApproximation.toNamed := by
  let left := Geometric.quotientStream (exact first) numerator.value numerator.apart
  let right := Geometric.quotientStream (exact 1) denominator.value denominator.apart
  have replace := Congruence.coherentMul_respects _ (CoherentNamed.ofApproximation left.toApproximation) _
    (CoherentNamed.ofApproximation right.toApproximation)
    (Geometric.quotientStream_agrees (exact first) numerator.value numerator.apart)
    (Geometric.quotientStream_agrees (exact 1) denominator.value denominator.apart)
  exact replace.trans (Bridge.mulToNamed_equivalent_pointwise
    left.toApproximation right.toApproximation
      (inverseProduct numerator
      denominator).toApproximation (fun _ => rfl))

/-- Dividing the exact radicand by its retained nonzero square-root channel is equivalent to that same root channel. -/
public def parameter_div_root {parameter :
  ReciprocalRootNames.Gaussian} (root : Certificate parameter) :
    Gaussian.Equivalence.NamedEquivalent (CoherentNamed.div (exact parameter) root.value root.apart).name
      root.value.name := by
  let quotient := CoherentNamed.div (exact parameter) root.value root.apart
  have cancel : Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul root.value quotient).name (exact parameter).name
    :=
    (Laws.coherentMul_comm root.value quotient).trans
      (Cancellation.coherentDiv_mul_cancel (exact parameter) root.value root.apart)
  exact Cancellation.coherentMul_cancel_left root.value quotient root.value root.apart
    (cancel.trans root.square.symm)

/-- Read any certified numerator program on the retained sheet. The supplied operational comparison transports its
square law to the original coordinate; the coordinate's prepared denominator and regular-root cache are reused. -/
def inverseProduct_equivalent {first second
  target : ReciprocalRootNames.Gaussian} {numerator : Certificate first} {denominator : Certificate second}
    (coordinate : RootCoordinates.RootCoordinate numerator denominator target) (source : Certificate first)
    (roots : Gaussian.Equivalence.NamedEquivalent source.value.name numerator.value.name) :
    Gaussian.Equivalence.Equivalent (inverseProduct source
      denominator).toApproximation
      (Sampling.approximation coordinate.prepared.denominator.name) := by
  let left := CoherentNamed.div (exact first) source.value source.apart
  let right := CoherentNamed.div (exact 1) denominator.value denominator.apart
  let product := CoherentNamed.mul left right
  have cancel : Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul product denominator.value).name
    source.value.name :=
    (Laws.coherentMul_assoc left right denominator.value).trans
      ((Congruence.coherentMul_respects left left (CoherentNamed.mul right denominator.value) (exact 1)
        (NamedEquivalent.refl _) (Cancellation.reciprocal_mul_cancel denominator.value denominator.apart)).trans
        ((Mul.coherentMul_one_right left).trans
          (parameter_div_root source)))
  have identified : Gaussian.Equivalence.NamedEquivalent product.name coordinate.prepared.denominator.name :=
    Cancellation.coherentMul_cancel_left denominator.value product coordinate.prepared.denominator denominator.apart
      ((((Laws.coherentMul_comm denominator.value product).trans cancel).trans roots).trans
        (((Laws.coherentMul_comm denominator.value coordinate.prepared.denominator).trans coordinate.reconstruct).symm))
  exact (Equivalent.toNamed_sampling (inverseProduct source
    denominator).toApproximation).symm.trans
    ((inverseProduct_raw source
      denominator).symm.trans identified)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples

end
