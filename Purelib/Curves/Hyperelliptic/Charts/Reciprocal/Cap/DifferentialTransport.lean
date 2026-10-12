module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootProvenance
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Arithmetic

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Riemann.RootContinuation

@[expose] public section

/-!
# Differential transport through the actual reciprocal cap coordinate

Odd degree uses the retained quotient coordinate t with t²=w and tangent
2t. Even degree retains the actual sheet sign whose square is one. These
operational identities compare the original collar channel with the regular
cap expression, including the reciprocal orientation sign. Rational readings
are not treated as exact roots or as exact points on the ramified boundary.
-/

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Approximation.Gaussian.Name.Coherent.Power (namedPower)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames (Gaussian)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul div)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence (coherentMul_respects)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws (coherentMul_comm coherentMul_assoc)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.RootContinuation.CertifiedSquareRoot (Certificate)
open Purelib.Riemann.RootContinuation.SquareRootProvenance (SquareIdentity)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (RootCoordinate Overlap)

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.RootCoordinate

/-- Cancel the retained coordinate against the original reciprocal root. The numerator may itself be an operational
polynomial expression. -/
def cancel_quotient {first second target : ReciprocalRootNames.Gaussian} {numerator : CertifiedSquareRoot.Certificate
  first} {denominator : CertifiedSquareRoot.Certificate second}
    (coordinate : RootCoordinates.RootCoordinate numerator denominator target) (value : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul coordinate.prepared.denominator (CoherentNamed.div value
      numerator.value numerator.apart)).name
      (CoherentNamed.div value denominator.value denominator.apart).name := by
  let factor := coordinate.prepared.denominator
  let quotient := CoherentNamed.div value numerator.value numerator.apart
  let regular := CoherentNamed.div value denominator.value denominator.apart
  have left : Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul denominator.value (CoherentNamed.mul factor
    quotient)).name value.name :=
    (Laws.coherentMul_assoc denominator.value factor quotient).symm.trans
      ((Congruence.coherentMul_respects (CoherentNamed.mul denominator.value factor) numerator.value quotient quotient
        ((Laws.coherentMul_comm denominator.value factor).trans coordinate.reconstruct) (NamedEquivalent.refl _)).trans
        ((Laws.coherentMul_comm numerator.value quotient).trans
          (Cancellation.coherentDiv_mul_cancel value numerator.value numerator.apart)))
  have right : Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul denominator.value regular).name value.name :=
    (Laws.coherentMul_comm denominator.value regular).trans
      (Cancellation.coherentDiv_mul_cancel value denominator.value denominator.apart)
  exact Cancellation.coherentMul_cancel_left denominator.value (CoherentNamed.mul factor quotient) regular
    denominator.apart (left.trans right.symm)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.RootCoordinate

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {point :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames.Gaussian}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)}

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap

/-- Minus the reversed differential coefficient, before multiplying by the cap-coordinate tangent. The denominator is
the actual collar root. -/
def collarCoefficient (overlap : RootCoordinates.Overlap cap point owner) (differential :
  Differentials.Basic.Differential genus) : CoherentNamed :=
  CoherentNamed.mul (Coherence.exact (-1)) (CoherentNamed.div (Coherence.exact (point ^
    (HyperellipticReciprocal.reversedDifferential differential).exponent)) overlap.reciprocal.value
      overlap.reciprocal.apart)

/-- A polynomial numerator in t, regular at t=0, over the retained model's regular-factor root. This is the operational
odd-chart cap expression. -/
def oddCoefficient (overlap : RootCoordinates.Overlap cap point owner) (differential : Differentials.Basic.Differential
  genus) : CoherentNamed :=
  CoherentNamed.mul (Coherence.exact (-(Primitives.degree curve : ReciprocalRootNames.Gaussian)))
    (CoherentNamed.div (Power.namedPower overlap.coordinate.prepared.denominator
    (Primitives.degree curve * (HyperellipticReciprocal.reversedDifferential differential).exponent))
      overlap.regularRoot.value overlap.regularRoot.apart)

/-- Move an exact Gaussian scalar outside a product of the original coherent channels. -/
public def move_constant (constant : ReciprocalRootNames.Gaussian) (factor value : Coherent.CoherentNamed) :
    Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul factor (CoherentNamed.mul (Coherence.exact constant)
      value)).name
      (CoherentNamed.mul (Coherence.exact constant) (CoherentNamed.mul factor value)).name :=
  (Laws.coherentMul_comm factor (CoherentNamed.mul (Coherence.exact constant) value)).trans
    ((Laws.coherentMul_assoc (Coherence.exact constant) value factor).trans
      (Congruence.coherentMul_respects (Coherence.exact constant) (Coherence.exact constant) (CoherentNamed.mul value
        factor) (CoherentNamed.mul factor value)
        (NamedEquivalent.refl _) (Laws.coherentMul_comm value factor)))

/-- The tangent 2t cancels the coordinate factor in the retained reciprocal root. The square law then turns w^m into the
finite polynomial t^(2m). -/
def odd_transport (overlap : RootCoordinates.Overlap cap point owner) (differential : Differentials.Basic.Differential
  genus)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul (CoherentNamed.mul (Coherence.exact 2) overlap.coordinate.prepared.denominator)
        (overlap.collarCoefficient differential)).name
      (overlap.oddCoefficient differential).name := by
  let factor := overlap.coordinate.prepared.denominator
  let numerator := Coherence.exact (point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent)
  let quotient := CoherentNamed.div numerator overlap.reciprocal.value overlap.reciprocal.apart
  let regular := CoherentNamed.div numerator overlap.regularRoot.value overlap.regularRoot.apart
  let polynomial := CoherentNamed.div (Power.namedPower factor (2 * (HyperellipticReciprocal.reversedDifferential
    differential).exponent))
    overlap.regularRoot.value overlap.regularRoot.apart
  have square : SquareRootProvenance.SquareIdentity factor point := by
    simpa only [branch, pow_one] using overlap.coordinate.square
  have powers := Purelib.Riemann.RootContinuation.SquareRootProvenance.SquareIdentity.even_power square
    (HyperellipticReciprocal.reversedDifferential differential).exponent
  have regularPolynomial :=
    Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence.coherentDiv_respects numerator
    (Power.namedPower factor (2 * (HyperellipticReciprocal.reversedDifferential differential).exponent))
    overlap.regularRoot.value overlap.regularRoot.value overlap.regularRoot.apart overlap.regularRoot.apart
    powers.symm (NamedEquivalent.refl _)
  have normalized := (Laws.coherentMul_assoc (Coherence.exact 2) factor (CoherentNamed.mul (Coherence.exact (-1))
    quotient)).trans
    ((Congruence.coherentMul_respects (Coherence.exact 2) (Coherence.exact 2) (CoherentNamed.mul factor
      (CoherentNamed.mul (Coherence.exact (-1)) quotient))
      (CoherentNamed.mul (Coherence.exact (-1)) (CoherentNamed.mul factor quotient)) (NamedEquivalent.refl _)
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.move_constant (-1) factor
        quotient)).trans
      ((Laws.coherentMul_assoc (Coherence.exact 2) (Coherence.exact (-1)) (CoherentNamed.mul factor
        quotient)).symm.trans
        (Congruence.coherentMul_respects (CoherentNamed.mul (Coherence.exact 2) (Coherence.exact (-1))) (Coherence.exact
          (-2)) (CoherentNamed.mul factor quotient) regular
          (by simpa only [show (2 : ReciprocalRootNames.Gaussian) * (-1) = -2 by ring1] using
            Exact.Arithmetic.exact_mul (2 : ReciprocalRootNames.Gaussian) (-1))
          (overlap.coordinate.cancel_quotient numerator))))
  have degree_eq : Primitives.degree curve = 2 := by
    rw [Primitives.degree, branch]
  simpa only [Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.oddCoefficient, degree_eq, show ((2 :
    Nat) : ReciprocalRootNames.Gaussian) = 2 by rfl,
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.collarCoefficient, factor, numerator, quotient,
      regular, polynomial,
    CoherentNamed.mul] using
    normalized.trans (Congruence.coherentMul_respects (Coherence.exact (-2)) (Coherence.exact (-2)) regular polynomial
      (NamedEquivalent.refl _) regularPolynomial)

/-- In even degree the quotient coordinate is a sheet sign. Its square law supplies the inverse sign, with no equality
test on opaque channels. -/
def even_transport (overlap : RootCoordinates.Overlap cap point owner) (differential : Differentials.Basic.Differential
  genus)
    (regularChart : HyperellipticReciprocal.originOrder curve = 0) :
    Gaussian.Equivalence.NamedEquivalent (overlap.collarCoefficient differential).name
      (CoherentNamed.mul overlap.coordinate.prepared.denominator
        (CoherentNamed.mul (Coherence.exact (-1)) (CoherentNamed.div (Coherence.exact (point ^
          (HyperellipticReciprocal.reversedDifferential differential).exponent))
            overlap.regularRoot.value overlap.regularRoot.apart))).name := by
  let factor := overlap.coordinate.prepared.denominator
  let numerator := Coherence.exact (point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent)
  let quotient := CoherentNamed.div numerator overlap.reciprocal.value overlap.reciprocal.apart
  let regular := CoherentNamed.div numerator overlap.regularRoot.value overlap.regularRoot.apart
  have square : SquareRootProvenance.SquareIdentity factor 1 := by
    simpa only [regularChart, pow_zero] using overlap.coordinate.square
  have inverse : Gaussian.Equivalence.NamedEquivalent quotient.name (CoherentNamed.mul factor regular).name :=
    (Mul.coherentMul_one_left quotient).symm.trans
      ((Congruence.coherentMul_respects (Coherence.exact 1) (CoherentNamed.mul factor factor) quotient quotient
        square.symm (NamedEquivalent.refl _)).trans
        ((Laws.coherentMul_assoc factor factor quotient).trans
          (Congruence.coherentMul_respects factor factor (CoherentNamed.mul factor quotient) regular
            (NamedEquivalent.refl _)
            (overlap.coordinate.cancel_quotient numerator))))
  exact (Congruence.coherentMul_respects (Coherence.exact (-1)) (Coherence.exact (-1)) quotient (CoherentNamed.mul
    factor regular)
    (NamedEquivalent.refl _) inverse).trans
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.move_constant (-1) factor regular).symm

set_option genInjectivity false in
/-- The intrinsic degree shape chooses the proved transport law. Both outcomes retain the actual coefficient comparison,
not a parity flag alone. -/
inductive Transport (overlap : RootCoordinates.Overlap cap point owner) (differential : Differentials.Basic.Differential
  genus) where
  /-- Retain the zero origin order and actual coefficient equivalence through the original sheet-sign coordinate. -/ |
    even (order : HyperellipticReciprocal.originOrder curve = 0)
      (equivalent : Gaussian.Equivalence.NamedEquivalent (overlap.collarCoefficient differential).name
        (CoherentNamed.mul overlap.coordinate.prepared.denominator
          (CoherentNamed.mul (Coherence.exact (-1)) (CoherentNamed.div (Coherence.exact (point ^
            (HyperellipticReciprocal.reversedDifferential differential).exponent))
              overlap.regularRoot.value overlap.regularRoot.apart))).name)
  /-- Retain the unit origin order and actual tangent-weighted coefficient equivalence through the original ramified
    coordinate. -/ | odd (order : HyperellipticReciprocal.originOrder curve = 1)
      (equivalent : Gaussian.Equivalence.NamedEquivalent
        (CoherentNamed.mul (CoherentNamed.mul (Coherence.exact 2) overlap.coordinate.prepared.denominator)
          (overlap.collarCoefficient differential)).name
        (overlap.oddCoefficient differential).name)

constructive_injectivity Transport

/-- Select the certified differential transport law from the original reciprocal origin order.

Both degree branches retain the actual operational coefficient comparison on the original cap coordinate and root
channels. -/
def transport (overlap : RootCoordinates.Overlap cap point owner) (differential : Differentials.Basic.Differential
  genus) : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Transport overlap differential :=
  if regular : HyperellipticReciprocal.originOrder curve = 0 then
    .even regular (overlap.even_transport differential regular)
  else
    let branch := (HyperellipticReciprocal.origin_factor curve).2.resolve_left regular
    .odd branch (overlap.odd_transport differential branch)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap
