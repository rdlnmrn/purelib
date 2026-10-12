module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Multiplicity.Site.Winding
public import Purelib.RootIsolation.Multiplicity.Observation.Track
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
public import Purelib.RationalFunctions.Winding.Box.Basic
import Purelib.RootIsolation.FTA.Squarefree.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.RationalFunctions.Winding.Box.Multiplicity

section
@[expose] public section

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
namespace PositiveSideInput

open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- A higher-degree weighted zero site has ordinary quotient winding equal to its retained multiplicity.

The indexed squarefree-factor track is protected from the opposite polynomial, and the exact represented source retains
the factorization weights. -/
theorem higherZeroBoxWinding
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries)
    (boxes : FTA.Squarefree.BoxResult
      context.focus.part.polynomial)
    (index : Fin context.focus.part.polynomial.natDegree) :
    let site := input.higherTrackInput context boxes index
    Winding.Box.Basic.rationalBoxWinding
        site.representedSource opposite site.state.box =
      context.focus.multiplicity :=
  (input.higherTrackInput context boxes index).representedBoxWinding

/-- A higher-degree weighted pole site has ordinary quotient winding equal to its negative multiplicity.

Use the same protected squarefree-factor track with the opposite polynomial as numerator. -/
theorem higherPoleBoxWinding
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries)
    (boxes : FTA.Squarefree.BoxResult
      context.focus.part.polynomial)
    (index : Fin context.focus.part.polynomial.natDegree) :
    let site := input.higherTrackInput context boxes index
    Winding.Box.Basic.rationalBoxWinding
        opposite site.representedSource site.state.box =
      -(context.focus.multiplicity : Int) :=
  (input.higherTrackInput context boxes index).representedPoleBoxWinding
end PositiveSideInput
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side

end
