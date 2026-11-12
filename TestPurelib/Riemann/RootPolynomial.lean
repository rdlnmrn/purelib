module

import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent

/-!
# Polynomial equations for arbitrary original root certificates

The tests retain the original coherent channel and cache through the geometric
view. The Horner equation consumes that actual channel for every polynomial
degree supported by its original winding-one track.
-/

namespace TestPurelib.Riemann.RootPolynomial

open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Polynomial.Approximation.Gaussian.Evaluation

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient}
    (certificate : CoherentRoot.CertifiedName track) (index : Nat) :
    certificate.geometric.sample index = certificate.approximation.sample index := rfl

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient}
    (certificate : CoherentRoot.CertifiedName track) :
    NamedEquivalent (Horner.polynomialEval polynomial certificate.value).name (Coherence.exact 0).name :=
  certificate.polynomial_zero

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient}
    (certificate : CoherentRoot.CertifiedName track) :
    certificate.value = Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.ofApproximation
      certificate.approximation :=
  certificate.value_approximation

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    {track : CoherentRoot.WindingOneTrack polynomial ambient}
    (certificate : CoherentRoot.CertifiedName track) (index : Nat) :
    certificate.approximation.sample index = (certificate.stateAt index).box.anchor := certificate.sample_stateAt index

example {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
    (track : CoherentRoot.WindingOneTrack polynomial ambient) (positive : 0 < polynomial.natDegree) :
    (CoherentRoot.certifiedName track positive).stateCache =
      CoherentRoot.StateCache.buildPrefix 64 (CoherentRoot.StateCache.first track) := rfl

end TestPurelib.Riemann.RootPolynomial
