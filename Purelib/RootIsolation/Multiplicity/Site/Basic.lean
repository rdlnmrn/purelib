module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Cofactor
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
public import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Constructive signed multiplicity sites

A squarefree factor track represents one geometric zero location.  This
module attaches the factor's complete finite multiplicity while protecting
the same box from both the remaining same-side factors and the opposite
rational-function cofactor.  One minimum of two positive rational requests
provides both protections simultaneously.
-/

namespace Purelib.RootIsolation.Multiplicity.Site.Basic

set_option genInjectivity false in
/-- Input for one higher-degree multiplicity site.  `source` is the
normalized same-side cofactor represented by the complete multiplicity
decomposition; `opposite` is the other reduced cofactor. -/
structure TrackSiteInput
    (source opposite : CoefficientPolynomial) where
  /-- The complete squarefree multiplicity decomposition of the original same-side source polynomial. -/ decomposition :
    Polynomial.Dense.Gaussian.Squarefree.Decomposition source
  /-- Distinct retained positive-multiplicity factors have displayed pairwise coprimality certificates. -/ pairwise :
    decomposition.positiveMultiplicityEntries.Pairwise
    fun left right => Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
      left.part right.part
  /-- The original focused positive-factor occurrence within the complete decomposition. -/ context :
    Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext
    decomposition.positiveMultiplicityEntries
  /-- The original opposite cofactor is nonzero. -/ oppositeNonzero : opposite.isZero = false
  /-- A displayed Bézout certificate separates the focused factor from the original opposite cofactor. -/
    focusOppositeCoprime :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate context.focus.part.polynomial
      opposite
  /-- The retained winding-one track for the focused factor in its coefficient-computed large square. -/ track :
    Track.Basic.WindingOneTrack context.focus.part.polynomial
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
      context.focus.part.polynomial)
  /-- The actual current winding-one state of the same focused factor and ambient square. -/ current :
    State.WindingOne.Basic.WindingOneState context.focus.part.polynomial
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
      context.focus.part.polynomial)

constructive_injectivity TrackSiteInput

namespace TrackSiteInput

/-- The original coefficient-computed large-square box of the focused factor. -/
abbrev ambient
    {source opposite : CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) : Box :=
  Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox
    input.context.focus.part.polynomial

/-- Derive the focused factor's Bézout certificate against the complete remaining same-side cofactor. -/
@[expose] def otherCoprime
    {source opposite : CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate
      input.context.focus.part.polynomial
      (input.context.otherPolynomial input.decomposition) :=
  input.context.otherCoprime input.decomposition input.pairwise

/-- The complete remaining same-side cofactor is nonzero. -/
theorem otherNonzero
    {source opposite : CoefficientPolynomial}
    (input : Multiplicity.Site.Basic.TrackSiteInput source opposite) :
    (input.context.otherPolynomial input.decomposition).isZero = false :=
  input.context.otherPolynomial_nonzero input.decomposition
end TrackSiteInput

end Purelib.RootIsolation.Multiplicity.Site.Basic

end
