module

public import Purelib.Curves.Hyperelliptic.Differentials.Basis
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Normalization.Program
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Normalization.Transport
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Bounds
import Purelib.Tactic.Ring

/-!
# Basis combinations on the original fixed-model normalized cap

The original scaled basis differential and the same infinity jet determine the
coefficient channel. Its finite kernel condition is transported through the
actual radius-paid four-quarter programme and prepared logarithmic integral.
These operational identities concern the supplied fixed model; arbitrary
external charts, the opposite sheet and a global meromorphic quotient retain
their separate geometric obligations.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs.Normalization.Basis

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

variable {genus : Nat} {curve : HyperellipticCurve genus} {jet : InfinityCoefficients.Jet curve}
    {coordinates : Data.Vector Canonical (2 * genus)} {scale : Canonical}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {data : Polynomials (Differentials.Basis.differential curve jet coordinates scale)}
    {principal : jet.Principal data.1.val (Differentials.Basis.differential curve jet coordinates scale).scale}

/-- The original coefficient channel of every basis combination is operationally zero in either degree shape.

The even case reads the same normalized numerator vector through its actual
infinity functional and retained jet. The origin reciprocal is unchanged;
only multiplication by its proved zero scalar is cancelled.
-/
def coefficient_zero (origin : Owners.Point cap 0)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial principal }) :
    Equivalence.NamedEquivalent (coefficientChannel (origin := origin) table).name (Coherence.exact 0).name := by
  cases shape : curve.degreeShape with
  | odd degree =>
      have ramified : HyperellipticReciprocal.originOrder curve = 1 := by
        rewrite [HyperellipticReciprocal.originOrder, shape]
        rfl
      exact coefficientChannel_odd table ramified
  | even degree =>
      have unramified : HyperellipticReciprocal.originOrder curve = 0 := by
        rewrite [HyperellipticReciprocal.originOrder, shape]
        rfl
      have original := Differentials.Basis.infinityCoefficient_combination curve jet coordinates
      rewrite [Differentials.Basis.infinityCoefficient, shape] at original
      have zero : InfinityCoefficients.evenFunctional curve jet
          (Dense.Evaluation.toVector (2 * genus + 1)
            (Dense.Evaluation.fromDense
              (Differentials.Basis.differential curve jet coordinates scale).numerator.normalize)) = 0 := by
        rewrite [(Differentials.Basis.differential_data curve jet coordinates scale).1]
        exact original
      let reciprocal := div (Coherence.exact 1) origin.certificate.value origin.certificate.apart
      have scalar := (congrArg (fun value : Canonical =>
        -(Differentials.Basis.differential curve jet coordinates scale).scale * value) zero).trans (mul_zero _)
      have names := congrArg (fun value : Canonical => (reciprocal.mul (Coherence.exact value)).name) scalar
      have compared := coefficientChannel_even (origin := origin)
        (degreeBound := Differentials.Basis.differential_numerator_degree_le curve jet coordinates scale)
        table unramified
      have atZero : Equivalence.NamedEquivalent (coefficientChannel (origin := origin) table).name
          (reciprocal.mul (Coherence.exact 0)).name :=
        Eq.mp (congrArg (fun target => Equivalence.NamedEquivalent
          (coefficientChannel (origin := origin) table).name target) names) compared
      exact atZero.trans (Arithmetic.Mul.coherentMul_zero_right reciprocal)

variable {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    {remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val}
    {primitive : Antiderivative.ReciprocalPrimitive principal.val genus}

/-- The actual normalized four-quarter cap channel of every basis combination is operationally zero.

The same original programme retains its intrinsic radius requests, total-form
sources, coefficients, logarithmic preparation and error bounds. Its proved
comparison with the coefficient channel composes with that channel's zero
certificate, without replacing programme samples by a finite functional.
-/
def channel_zero (origin : Owners.Point cap 0)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial principal })
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish)
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
    (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor)
    (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1) :
    Equivalence.NamedEquivalent
      (channel (primitive := primitive) origin table
        (Differentials.Basis.differential_data curve jet coordinates scale).2.1
        (Differentials.Basis.differential_numerator_degree_le curve jet coordinates scale)
        bounds edges jetBounds anchor setup errorBounds).name
      (Coherence.exact 0).name :=
  (channel_equivalent (primitive := primitive) origin table
    (Differentials.Basis.differential_data curve jet coordinates scale).2.1
    (Differentials.Basis.differential_numerator_degree_le curve jet coordinates scale)
    bounds edges jetBounds anchor setup errorBounds).trans (coefficient_zero origin table)

/-- The actual normalized negative-sheet loop of every scaled basis numerator is operationally zero.

The reference and signed differential have opposite scalars and the same
original numerator. All four signed programmes and their saved logarithmic
normalizer belong to the actual shrinking-loop construction; its coefficient
comparison consumes the same original finite-kernel proof.
-/
def evenNegative_zero (origin : Owners.Point cap 0)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial principal })
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish)
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
    (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor)
    (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1) :
    Equivalence.NamedEquivalent
      (evenNegativeChannel (differential := Differentials.Basis.differential curve jet coordinates (-scale))
        (primitive := primitive) origin table
        (Differentials.Basis.differential_data curve jet coordinates (-scale)).2.1
        (Differentials.Basis.differential_data curve jet coordinates scale).2.1
        (Differentials.Basis.differential_numerator_degree_le curve jet coordinates scale)
        ((Differentials.Basis.differential_data curve jet coordinates scale).1.trans
          (Differentials.Basis.differential_data curve jet coordinates (-scale)).1.symm)
        (by
          rewrite [(Differentials.Basis.differential_data curve jet coordinates scale).2.2,
            (Differentials.Basis.differential_data curve jet coordinates (-scale)).2.2]
          ring1)
        parity bounds edges jetBounds anchor setup errorBounds).name
      (Coherence.exact 0).name :=
  (evenNegativeChannel_equivalent
    (differential := Differentials.Basis.differential curve jet coordinates (-scale))
    (primitive := primitive) origin table
    (Differentials.Basis.differential_data curve jet coordinates (-scale)).2.1
    (Differentials.Basis.differential_data curve jet coordinates scale).2.1
    (Differentials.Basis.differential_numerator_degree_le curve jet coordinates scale)
    ((Differentials.Basis.differential_data curve jet coordinates scale).1.trans
      (Differentials.Basis.differential_data curve jet coordinates (-scale)).1.symm)
    (by
      rewrite [(Differentials.Basis.differential_data curve jet coordinates scale).2.2,
        (Differentials.Basis.differential_data curve jet coordinates (-scale)).2.2]
      ring1)
    parity bounds edges jetBounds anchor setup errorBounds).trans (coefficient_zero origin table)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs.Normalization.Basis

end
