module
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RationalFunctions.Winding.Box.Basic
import Purelib.RationalFunctions.Winding.Box.Quotient
import Purelib.RootIsolation.Multiplicity.Site.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.RootIsolation.Multiplicity.Site.Winding
import Purelib.RootIsolation.Multiplicity.Site.Protection
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

section
@[expose] public section

/-!
# Constructive signed multiplicity sites

A squarefree factor track represents one geometric zero location.  This
module attaches the factor's complete finite multiplicity while protecting
the same box from both the remaining same-side factors and the opposite
rational-function cofactor.  One minimum of two positive rational requests
provides both protections simultaneously.
-/

namespace Purelib.RootIsolation.Multiplicity.Site.Basic
namespace TrackSiteInput

section
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.RationalFunctions
/-- The protected weighted source quotient has quadrupled winding four times the retained multiplicity.

The exact source factorization supplies its weighted winding, while the protected opposite polynomial has winding zero.
-/
theorem representedRationalWinding
    {source opposite : CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    Winding.Box.Basic.rationalQuadrupledWinding
        input.representedSource opposite input.state.box =
      (4 : Int) * input.context.focus.multiplicity := by
  have quotient :=
    Winding.Box.Quotient.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      input.representedSource opposite input.state.box input.state.proper
      input.representedSourceClearance input.oppositeClearance
  rw [quotient, input.representedSourceWinding, input.oppositeWinding_zero]
  ring1

/-- The protected weighted source quotient has ordinary box winding equal to its retained multiplicity. -/
theorem representedBoxWinding
    {source opposite : CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    Winding.Box.Basic.rationalBoxWinding
        input.representedSource opposite input.state.box =
      input.context.focus.multiplicity :=
  Winding.Box.Basic.rationalBoxWinding_eq_of_quadrupled_eq_four_mul
    input.representedRationalWinding

/-- Reversing the protected weighted quotient gives quadrupled winding minus four times the multiplicity.

The same retained site and boundary clearances are used with numerator and denominator exchanged. -/
theorem representedPoleRationalWinding
    {source opposite : CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    Winding.Box.Basic.rationalQuadrupledWinding
        opposite input.representedSource input.state.box =
      -(4 : Int) * input.context.focus.multiplicity := by
  have quotient :=
    Winding.Box.Quotient.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      opposite input.representedSource input.state.box input.state.proper
      input.oppositeClearance input.representedSourceClearance
  rw [quotient, input.oppositeWinding_zero, input.representedSourceWinding]
  ring1

/-- The reciprocal protected quotient has ordinary box winding equal to the negative retained multiplicity. -/
theorem representedPoleBoxWinding
    {source opposite : CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    Winding.Box.Basic.rationalBoxWinding
        opposite input.representedSource input.state.box =
      -(input.context.focus.multiplicity : Int) := by
  apply Winding.Box.Basic.rationalBoxWinding_eq_of_quadrupled_eq_four_mul
  rw [input.representedPoleRationalWinding]
  ring1

end

end TrackSiteInput

end Purelib.RootIsolation.Multiplicity.Site.Basic

end
