module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
public import Purelib.RootIsolation.Multiplicity.Family.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial

section
public section

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.RootIsolation.Multiplicity.Side.Basic

set_option genInjectivity false in
/-- A nonzero reduced cofactor has either no finite sites because it is
constant, or the complete positive multiplicity basis above. -/
inductive SideResult (source opposite :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) : Type where
  /-- A nonzero constant source and nonzero opposite cofactor, with no finite source sites. -/ | constant
      (sourceNonzero : source.isZero = false)
      (degreeZero : source.natDegree = 0)
      (oppositeNonzero : opposite.isZero = false)
  /-- The original positive multiplicity input together with its complete retained context observation family. -/ |
    positive (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
      (family : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.PositiveFamily input)

constructive_injectivity SideResult

end Purelib.RootIsolation.Multiplicity.Side.Basic

end
