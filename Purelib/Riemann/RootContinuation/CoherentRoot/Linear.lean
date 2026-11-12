module

public import Purelib.Riemann.RootContinuation.CoherentRoot
public import Purelib.Polynomial.Dense.Gaussian.Roots.Linear.Evaluation
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic

/-! # Exact linear readback of original coherent root tracks -/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.CertifiedName

open Purelib.Polynomial
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat

/-- A degree-one track's original numerical channel agrees with its retained exact linear root.

The inverse leading coefficient scales the original polynomial residual into
a geometric displacement bound. The comparison computes its own finite
indices from that bound and preserves both original starting states; no new
root track or copied sample channel is constructed.
-/
def linear_equivalent {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track)
    (data : Dense.Gaussian.Roots.Linear.RootData polynomial) :
    Equivalence.NamedEquivalent root.value.name (Name.Coherent.CoherentNamed.Coherence.exact data.point).name := by
  let factor := normSq data.leading⁻¹
  let scale := factor * residualScale polynomial ambient track
  have factorNonnegative : 0 ≤ factor := Purelib.Data.Gaussian.Norm.Basic.normSq_nonneg _
  have scaleNonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct
    factorNonnegative (residualScale_nonneg polynomial ambient track)
  have samples : ∀ index, normSq (root.approximation.sample index - data.point) ≤
      Geometric.Basic.quarterRadius scale index := by
    intro index
    rewrite [data.displacement_eq, Purelib.Data.Gaussian.Norm.Basic.normSq_mul]
    have residual := root.residual index
    rewrite [← root.approximation_eq] at residual
    have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct residual factorNonnegative
    rewrite [Geometric.Basic.quarterRadius_eq_mul_pow] at bounded
    rewrite [Geometric.Basic.quarterRadius_eq_mul_pow]
    exact bounded.trans_eq (Fraction.Field.mul_assoc _ _ _).symm
  rewrite [root.value_approximation]
  exact (Sequence.Equivalence.equivalent_constant root.approximation
    data.point scale scaleNonnegative samples).toNamed.trans
    (Sequence.Name.Exact.exact_toConstantNamed data.point).symm

end Purelib.Riemann.RootContinuation.CoherentRoot.CertifiedName

end
