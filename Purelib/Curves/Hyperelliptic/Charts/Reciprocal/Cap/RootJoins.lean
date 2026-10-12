module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Endpoints
public import Purelib.Riemann.Normalization.InverseModelRootAgreement
import Init.ByCases
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Normalization.InverseRootPolynomial

public section

/-!
# Cap coordinate and primitive agreement at shared owned points

The regular root channels come from one retained polynomial model. Their
cached Newton readings agree at a common point, so agreement of the actual
reciprocal roots also identifies the quotient coordinates and cap primitives.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.RootCoordinate

open Purelib
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
open Purelib.Geometry
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames (Gaussian CoherentNamed NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (RootCoordinate Overlap)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul)

/-- Quotient coordinates preserve the supplied numerator and denominator root agreements, including their independently
prepared presentations. -/
@[expose] public def equivalent {firstParameter lastParameter firstRegular lastRegular firstTarget lastTarget :
  ReciprocalRootNames.Gaussian}
    {firstNumerator : CertifiedSquareRoot.Certificate firstParameter}
    {lastNumerator : CertifiedSquareRoot.Certificate lastParameter}
    {firstDenominator : CertifiedSquareRoot.Certificate firstRegular}
    {lastDenominator : CertifiedSquareRoot.Certificate lastRegular}
    (first : RootCoordinates.RootCoordinate firstNumerator firstDenominator firstTarget)
    (last : RootCoordinates.RootCoordinate lastNumerator lastDenominator lastTarget)
    (numerators : ReciprocalRootNames.NamedEquivalent firstNumerator.value.name lastNumerator.value.name)
    (denominators : ReciprocalRootNames.NamedEquivalent firstDenominator.value.name lastDenominator.value.name) :
    ReciprocalRootNames.NamedEquivalent first.prepared.denominator.name last.prepared.denominator.name := by
  have quotients : ReciprocalRootNames.NamedEquivalent first.quotient.name last.quotient.name := by
    rw [first.quotient_eq, last.quotient_eq]
    exact Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence.coherentDiv_respects
      firstNumerator.value lastNumerator.value
      firstDenominator.value lastDenominator.value firstDenominator.apart lastDenominator.apart numerators denominators
  exact first.prepared.equivalent.symm.trans (quotients.trans last.prepared.equivalent)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.RootCoordinate

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap

open Purelib
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
open Purelib.Geometry
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames (Gaussian CoherentNamed NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (RootCoordinate Overlap)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {firstPoint lastPoint
    : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames.Gaussian}
  {firstOwner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval firstPoint)}
  {lastOwner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval lastPoint)}

set_option genInjectivity false in
/-- A join records actual point equality and operational coordinate agreement. It does not assert equality of finite
readings chosen at different indices. -/
structure Join (first : RootCoordinates.Overlap cap firstPoint firstOwner) (last : RootCoordinates.Overlap cap lastPoint
  lastOwner) where
  /-- The two retained original cap-coordinate occurrences have the same exact geometric point. -/ point_eq : firstPoint
    = lastPoint
  /-- The original retained quotient-coordinate channels are operationally equivalent. -/ equivalent :
    ReciprocalRootNames.NamedEquivalent first.coordinate.prepared.denominator.name
    last.coordinate.prepared.denominator.name

constructive_injectivity Join

/-- Reverse the retained point identity and original coordinate equivalence. -/
@[expose] public def Join.symm {first : RootCoordinates.Overlap cap firstPoint firstOwner} {last :
  RootCoordinates.Overlap cap lastPoint lastOwner}
    (join : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Join first last) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Join last first :=
  ⟨join.point_eq.symm, join.equivalent.symm⟩

/-- Compose retained original cap-coordinate joins through their shared middle occurrence. -/
@[expose] public def Join.trans {middlePoint : ReciprocalRootNames.Gaussian}
    {middleOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval middlePoint)}
    {first : RootCoordinates.Overlap cap firstPoint firstOwner} {middle : RootCoordinates.Overlap cap middlePoint
      middleOwner}
    {last : RootCoordinates.Overlap cap lastPoint lastOwner} (firstJoin :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Join first middle) (lastJoin :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Join middle last) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Join first last :=
  ⟨firstJoin.point_eq.trans lastJoin.point_eq, firstJoin.equivalent.trans lastJoin.equivalent⟩

/-- Construct an original cap-coordinate join from point equality and actual reciprocal-root equivalence, reusing the
shared regular model channel. -/
@[expose] public def Join.build (first : RootCoordinates.Overlap cap firstPoint firstOwner) (last :
  RootCoordinates.Overlap cap lastPoint lastOwner)
    (pointEq : firstPoint = lastPoint)
    (roots : ReciprocalRootNames.NamedEquivalent first.reciprocal.value.name last.reciprocal.value.name) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Join first last := by
  cases pointEq
  have regular : ReciprocalRootNames.NamedEquivalent first.regularRoot.value.name last.regularRoot.value.name := by
    rw [first.regularRoot_eq, last.regularRoot_eq]
    exact InverseModelRootAgreement.equivalent_of_value first.regular.channel last.regular.channel rfl
  exact ⟨rfl, first.coordinate.equivalent last.coordinate roots regular⟩

/-- The same global cap polynomial has one operational value at a joined endpoint, in either the even sheet chart or the
odd ramified chart. -/
@[expose] public def Join.primitive {first : RootCoordinates.Overlap cap firstPoint firstOwner} {last :
  RootCoordinates.Overlap cap lastPoint lastOwner}
    (join : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Join first last) {differential :
      Differentials.Basic.Differential genus} {index : Nat} {box : Rational.Box}
    (sample : Primitives.Sample cap differential index box) :
    ReciprocalRootNames.NamedEquivalent (first.chartPrimitive sample).name (last.chartPrimitive sample).name := by
  rcases join with ⟨pointEq, coordinates⟩
  cases pointEq
  by_cases regular : HyperellipticReciprocal.originOrder curve = 0
  · simp only [Overlap.chartPrimitive, if_pos regular]
    exact Congruence.coherentMul_respects _ _ _ _ coordinates
      (NamedEquivalent.refl _)
  · simp only [Overlap.chartPrimitive, if_neg regular]
    exact Horner.horner_respects _ _ (Coherence.exact 0) (Coherence.exact 0) coordinates
      (NamedEquivalent.refl _) sample.primitive.value.coeffs

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap
