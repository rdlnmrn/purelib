module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Multiplicity.Observation.Separation
public import Purelib.RootIsolation.Multiplicity.Side.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.RootIsolation.Multiplicity.Family.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.RootIsolation.Multiplicity.Side.Separation

/-- Joint numerator/denominator separation.  Constant sides contribute no
sites; positive sides retain a finite separation witness for every pair of
factor groups across the displayed reduced Bézout identity. -/
@[expose] def SidesSeparated
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (numeratorSites : Multiplicity.Side.Basic.SideResult numerator denominator)
    (denominatorSites : Multiplicity.Side.Basic.SideResult denominator numerator) : Type :=
  match numeratorSites, denominatorSites with
  | .positive numeratorInput numeratorFamily,
      .positive denominatorInput denominatorFamily =>
      ∀ (numeratorIndex : Fin numeratorInput.contexts.length)
        (denominatorIndex : Fin denominatorInput.contexts.length),
        Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.ObservationsSeparated
          (numeratorFamily.observationAt numeratorIndex)
          (denominatorFamily.observationAt denominatorIndex)
  | .constant _ _ _, _ => PUnit
  | .positive _ _, .constant _ _ _ => PUnit

/-- Construct separation between the retained numerator and denominator site observations.

Constant sides need no site comparisons; positive sides use the original context-to-context coprimality witnesses and
retain the actual observation separation at both indices. -/
@[expose] def separateSides
    {numerator denominator : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (numeratorSites : Multiplicity.Side.Basic.SideResult numerator denominator)
    (denominatorSites : Multiplicity.Side.Basic.SideResult denominator numerator) :
    Multiplicity.Side.Separation.SidesSeparated numeratorSites denominatorSites := by
  cases numeratorSites with
  | constant => exact PUnit.unit
  | positive numeratorInput numeratorFamily =>
      cases denominatorSites with
      | constant => exact PUnit.unit
      | positive denominatorInput denominatorFamily =>
          intro numeratorIndex denominatorIndex
          exact Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.separateObservations
            (numeratorFamily.observationAt numeratorIndex)
            (denominatorFamily.observationAt denominatorIndex)
            (numeratorInput.focusFocusCoprime
              (numeratorInput.contexts.get numeratorIndex)
              denominatorInput
              (denominatorInput.contexts.get denominatorIndex))
end Purelib.RootIsolation.Multiplicity.Side.Separation

end
