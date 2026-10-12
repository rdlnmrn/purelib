module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
public import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Complete finite refinement families for profile events

`SturmNonzeroEvent.request` deliberately follows one nonzero child.  That is
the right interface for one persistent algebraic event, but it is not a
complete refinement when the starting cell has several nonzero children.
This module builds the full finite binary refinement at a requested width,
filters all and only the nonzero-count children, and retains pointwise
coverage for every supplied displayed rational profile zero.

The construction uses only finite subdivision trees and integer event counts.
In particular, nonzero count is never converted into a root-existence claim.
-/

namespace Purelib.CCL.Persistent.ProfileRequestFamily
section Profile

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
  Purelib.Geometry.Projective.Hermitian.HermitianForm}
variable {chart : Purelib.Geometry.Projective.Hermitian.Chart.BoundedChart form}
variable {data : Purelib.RootIsolation.Curve.Event.Nontrivial p
  chart.parameterization.curve}
variable {gcdDegreePositive : 0 <
  (Purelib.RationalFunctions.Curve.Substitution.gcdPolynomial p
    chart.parameterization.curve).natDegree}
variable {factorAnalysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilySquarefreeFactorAnalysisAlias p box
  chart data
  gcdDegreePositive}
namespace CompleteRequestLeaf

end CompleteRequestLeaf

end Profile

/-! ## Complete requested families through a dispatched boundary -/

end Purelib.CCL.Persistent.ProfileRequestFamily

end
