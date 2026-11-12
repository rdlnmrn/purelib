module

import Purelib.Riemann.RootContinuation.CoherentRoot.Localization

/-! # Original squarefree residual programs select fixed cached roots -/

namespace TestPurelib.Riemann.RootLocalization

open Purelib
open Purelib.Riemann.RootContinuation
open Purelib.Approximation.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

variable {polynomial : CoherentRoot.GaussianPolynomial} {ambient : CoherentRoot.Box}
variable {track : CoherentRoot.WindingOneTrack polynomial ambient}

example (input : RootIsolation.FTA.Squarefree.Input polynomial) (root : CoherentRoot.CertifiedName track) :
    Equivalence.NamedEquivalent root.value.name
      ((CoherentRoot.Localization.Preparation.ofCertifiedName input root).select.root.value.name) :=
  (CoherentRoot.Localization.Preparation.ofCertifiedName input root).select.original_equivalent root

example {input : RootIsolation.FTA.Squarefree.Input polynomial} {source : Geometric.GeometricApproximation}
    (preparation : CoherentRoot.Localization.Preparation input source) (leftStart rightStart : Nat)
    (target : Rational) (positive : 0 < target) :
    Equivalence.Comparison source.toApproximation preparation.select.root.approximation leftStart rightStart target :=
  preparation.select.equivalent.compare leftStart rightStart target positive

example {input : RootIsolation.FTA.Squarefree.Input polynomial} {source : Geometric.GeometricApproximation}
    (preparation : CoherentRoot.Localization.Preparation input source)
    (selection : preparation.Selection) {later : Nat} (order : selection.anchor.index ≤ later)
    {target : Rational} (small : target ≤ preparation.separated.gap / 16)
    (nearby : Sequence.Selection.Nearby preparation.candidates (preparation.source.sample later) target) :
    nearby.owner = selection.anchor.nearby.owner := selection.anchor.sameOwner order small nearby

end TestPurelib.Riemann.RootLocalization
