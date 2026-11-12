module

import Purelib.Polynomial.Approximation.Gaussian.Localization.Selection
import Purelib.Riemann.RootContinuation.CoherentRoot.Arithmetic.Localization
import Purelib.Polynomial.Approximation.Gaussian.Arithmetic

/-! # All-input original multiplicity root selection and arithmetic-channel comparison -/

namespace TestPurelib.Riemann.MultiplicitySelection

open Purelib
open Purelib.Polynomial.Approximation.Gaussian renaming Arithmetic -> PolynomialArithmetic
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Companion (Operation)
open Purelib.Riemann.RootContinuation

example {polynomial : CoefficientPolynomial} {original : GeometricApproximation}
    (preparation : Polynomial.Approximation.Gaussian.Localization.Preparation polynomial original) :
    Equivalence.Equivalent original.toApproximation preparation.select.approximation :=
  preparation.select.equivalent

example {polynomial : CoefficientPolynomial} {original : GeometricApproximation}
    (preparation : Polynomial.Approximation.Gaussian.Localization.Preparation polynomial original) :
    Equivalence.NamedEquivalent original.toApproximation.toNamed preparation.select.channel.name :=
  preparation.select.namedEquivalent

example {firstPolynomial secondPolynomial : CoherentRoot.GaussianPolynomial}
    {firstAmbient secondAmbient : CoherentRoot.Box}
    {firstTrack : CoherentRoot.WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : CoherentRoot.WindingOneTrack secondPolynomial secondAmbient}
    {operation : Operation} {first : CoherentRoot.CertifiedName firstTrack}
    {second : CoherentRoot.CertifiedName secondTrack}
    (arithmetic : CoherentRoot.Arithmetic operation first second) :
    Equivalence.NamedEquivalent (PolynomialArithmetic.channel operation first.value second.value).name
      arithmetic.select.channel.name := arithmetic.select.equivalent

example {firstPolynomial secondPolynomial : CoherentRoot.GaussianPolynomial}
    {firstAmbient secondAmbient : CoherentRoot.Box}
    {firstTrack : CoherentRoot.WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : CoherentRoot.WindingOneTrack secondPolynomial secondAmbient}
    {operation : Operation} {first : CoherentRoot.CertifiedName firstTrack}
    {second : CoherentRoot.CertifiedName secondTrack}
    (arithmetic : CoherentRoot.Arithmetic operation first second) :
    Division.Prepared.Decision (PolynomialArithmetic.channel operation first.value second.value) :=
  arithmetic.select.decide

end TestPurelib.Riemann.MultiplicitySelection
