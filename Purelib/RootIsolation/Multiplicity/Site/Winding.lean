module
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Operations
public import Purelib.Polynomial.Clearance.Box.Boundary.Power
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.Power
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Power
import Purelib.Polynomial.Winding.Box.Product
import Purelib.RootIsolation.Multiplicity.Site.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.RootIsolation.Multiplicity.Site.Protection
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Cofactor
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.Polynomial.Dense.Multiplication
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Polynomial

open Purelib.RootIsolation

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

/-- The factored same-side numerator used for the local quotient winding.
Its evaluation is certified equal to `source` by
`representedFactorization`. -/
def representedSource
    {source opposite : CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
      CoefficientPolynomial :=
  Dense.Gaussian.Power.polynomialPower
      input.context.focus.part.polynomial input.context.focus.multiplicity *
    input.context.otherPolynomial input.decomposition

/-- The represented source is exactly the focused factor to its retained multiplicity times the original other factor.
-/
theorem representedFactorization
    {source opposite : CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    Dense.Gaussian.Factorization.Identity.ProductIdentity source
      (Dense.Gaussian.Power.polynomialPower
        input.context.focus.part.polynomial input.context.focus.multiplicity)
      (input.context.otherPolynomial input.decomposition) :=
  input.context.multiplicityFactorization input.decomposition rfl

/-- Combine the original focused-factor power clearance with the other-factor clearance on the same protected site box.
-/
def representedSourceClearance
    {source opposite : CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    Clearance.Box.Boundary.Basic.BoundaryClearance input.representedSource input.state.box :=
  Clearance.Box.Boundary.Basic.BoundaryClearance.mul
    (Clearance.Box.Boundary.Power.polynomialPower_boundaryClearance
      input.state.clearance input.context.focus.multiplicity)
    input.otherClearance

/-- The represented source has raw winding four times the original focused multiplicity on its protected site box.

The focused factor contributes its retained unit winding; the original other factor has zero winding there. -/
theorem representedSourceWinding
    {source opposite : CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    Winding.Box.Basic.quadrupledBoxWinding input.representedSource input.state.box =
      (4 : Int) * input.context.focus.multiplicity := by
  have powerWinding :=
    Winding.Box.Power.quadrupledBoxWinding_polynomialPower
      input.state.proper input.state.clearance input.context.focus.multiplicity
  have productWinding :=
    Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
      (Dense.Gaussian.Power.polynomialPower
        input.context.focus.part.polynomial input.context.focus.multiplicity)
      (input.context.otherPolynomial input.decomposition) input.state.box
      input.state.proper
      (Clearance.Box.Boundary.Power.polynomialPower_boundaryClearance
        input.state.clearance input.context.focus.multiplicity)
      input.otherClearance
  change Winding.Box.Basic.quadrupledBoxWinding
      (Dense.Gaussian.Power.polynomialPower
          input.context.focus.part.polynomial input.context.focus.multiplicity *
        input.context.otherPolynomial input.decomposition) input.state.box = _
  rw [productWinding, powerWinding, input.state.rawWindingFour,
    input.otherWinding_zero]
  ring1
end TrackSiteInput

end Purelib.RootIsolation.Multiplicity.Site.Basic

end
