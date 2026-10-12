module
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product
public import Purelib.RootIsolation.Multiplicity.Side.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.RootIsolation.Multiplicity.Family.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.RootIsolation.Multiplicity.Side.Basic
namespace SideResult

/-- Total signed-multiplicity mass on one side before choosing its sign. -/
def multiplicityDegree
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} :
    Multiplicity.Side.Basic.SideResult source opposite → Nat
  | .constant _ _ _ => 0
  | .positive input _ =>
      Dense.Gaussian.Multiplicity.Basis.Product.positiveDegree input.entries

/-- The original side's retained multiplicity mass equals its source polynomial degree. -/
theorem multiplicityDegree_eq_natDegree
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (result : Multiplicity.Side.Basic.SideResult source opposite) :
    result.multiplicityDegree = source.natDegree := by
  cases result with
  | constant _ degreeZero _ => exact degreeZero.symm
  | positive _ family => exact family.weightedDegree

end SideResult
end Purelib.RootIsolation.Multiplicity.Side.Basic

end
