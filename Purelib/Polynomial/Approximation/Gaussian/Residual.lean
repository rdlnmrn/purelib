module

public import Purelib.Polynomial.Approximation.CoherentEvaluation
public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Approximation.Gaussian.Sequence.Constant
public import Purelib.Polynomial.Dense.Gaussian.LinearFactor
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Algebra.Ring.Normalization
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Quantitative polynomial residual certificates on original numerical channels

The original coherent channel is compared to one retained geometric sample
program. Its exact displayed polynomial has positive degree, and every actual
sample has a polynomial residual bounded by the retained geometric scale.
These certificates compose without replacing mathematical root owners.
-/

public section

namespace Purelib.Polynomial.Approximation.Gaussian

open Purelib
open Purelib.Algebra.Ring
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)

set_option genInjectivity false in
/-- One retained quantitative polynomial residual program linked to its unchanged original coherent channel.

The certificate keeps the actual sample program and scale rather than only an
operational zero equation. Positive degree permits finite coefficient-derived
root preparation; no finite sample is asserted to be an exact root.
-/
structure Residual (polynomial : CoefficientPolynomial) (channel : CoherentNamed) where
  /-- The original displayed polynomial has positive degree. -/
  degreePositive : 0 < polynomial.natDegree
  /-- The actual retained geometric sample program. -/
  source : GeometricApproximation
  /-- The unchanged original channel agrees with this same retained sample program. -/
  equivalent : NamedEquivalent channel.name source.toApproximation.toNamed
  /-- The retained quantitative geometric polynomial-residual scale. -/
  scale : Rational
  /-- The retained scale is nonnegative. -/
  scale_nonnegative : 0 ≤ scale
  /-- Every sample of the same retained program obeys the displayed polynomial's geometric residual bound. -/
  bound : ∀ index, normSq (polynomial.eval (source.sample index)) ≤
    Purelib.Approximation.Rational.Geometric.Basic.quarterRadius scale index

constructive_injectivity Residual

namespace Residual

/-- Retain an original channel, actual sample program and its all-index polynomial residual bound. -/
@[expose] def ofGeometric {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (degreePositive : 0 < polynomial.natDegree) (source : GeometricApproximation)
    (equivalent : NamedEquivalent channel.name source.toApproximation.toNamed)
    (scale : Rational) (scaleNonnegative : 0 ≤ scale)
    (bound : ∀ index, normSq (polynomial.eval (source.sample index)) ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius scale index) : Residual polynomial channel :=
  ⟨degreePositive, source, equivalent, scale, scaleNonnegative, bound⟩

/-- Transport the same actual residual program and bound to an explicitly compared original coherent channel. -/
def transport {polynomial : CoefficientPolynomial} {first second : CoherentNamed}
    (residual : Residual polynomial first) (equivalent : NamedEquivalent second.name first.name) :
    Residual polynomial second :=
  ⟨residual.degreePositive, residual.source, equivalent.trans residual.equivalent,
    residual.scale, residual.scale_nonnegative, residual.bound⟩

/-- Channel transport retains the exact original geometric sample program. -/
theorem transport_source {polynomial : CoefficientPolynomial} {first second : CoherentNamed}
    (residual : Residual polynomial first) (equivalent : NamedEquivalent second.name first.name) :
    (residual.transport equivalent).source = residual.source := by
  unfold transport
  rfl

/-- Equal polynomial indices retain the exact same original geometric source program. -/
theorem cast_polynomial_source {first second : CoefficientPolynomial} {channel : CoherentNamed}
    (same : first = second) (residual : Residual first channel) :
    (same ▸ residual).source = residual.source := by
  cases same
  rfl

/-- Quantitative all-index residuals imply operational polynomial zero on the unchanged original coherent channel. -/
def equation {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) :
    NamedEquivalent (Horner.polynomialEval polynomial channel).name (CoherentNamed.Coherence.exact 0).name := by
  let evaluated := Evaluation.evaluate polynomial residual.source
  have bound : ∀ index, normSq (evaluated.toApproximation.sample index - 0) ≤
      Purelib.Approximation.Rational.Geometric.Basic.quarterRadius residual.scale index := by
    intro index
    change normSq (polynomial.eval (residual.source.sample index) - 0) ≤ _
    rewrite [Normalization.sub_zero]
    exact residual.bound index
  let zero := Sequence.Equivalence.equivalent_constant evaluated.toApproximation 0 residual.scale
    residual.scale_nonnegative bound
  let agreement := CoherentEvaluation.evaluate_agrees polynomial channel residual.source residual.equivalent
  exact agreement.trans (zero.toNamed.trans (Sequence.Name.Exact.exact_toConstantNamed 0).symm)

/-- An exact Gaussian channel retains its computed degree-one polynomial and zero residual sample program. -/
@[expose] def exact (point : Canonical) : Residual (Dense.Gaussian.LinearFactor.linearFactor point)
    (CoherentNamed.Coherence.exact point) := by
  let source := GeometricApproximation.exact point
  have degreePositive : 0 < (Dense.Gaussian.LinearFactor.linearFactor point).natDegree := by
    rewrite [Dense.Gaussian.LinearFactor.linearFactor_natDegree]
    exact (show (0 : Nat) < 1 by decide)
  have equivalent : NamedEquivalent (CoherentNamed.Coherence.exact point).name source.toApproximation.toNamed :=
    (Sequence.Name.Exact.exact_toConstantNamed point).trans
      ((Sequence.Equivalence.approximationEquivalentOfSamplesEq (Sequence.Constant.constantApproximation point)
        source.toApproximation (fun _ => rfl)).toNamed)
  refine ⟨degreePositive, source, equivalent, 0, by decide, ?_⟩
  intro index
  change normSq ((Dense.Gaussian.LinearFactor.linearFactor point).eval point) ≤
    Purelib.Approximation.Rational.Geometric.Basic.quarterRadius 0 index
  rewrite [Dense.Gaussian.LinearFactor.linearFactor_eval, Purelib.Data.Gaussian.Basic.sub_self,
    Purelib.Data.Gaussian.Norm.Basic.normSq_zero]
  exact Purelib.Approximation.Rational.Geometric.Basic.quarterRadius_nonneg (by decide) index

/-- The exact residual constructor reads its retained exact point at every original finite index. -/
theorem exact_sample (point : Canonical) (index : Nat) : (exact point).source.sample index = point := rfl

/-- The exact residual constructor retains zero as its actual polynomial residual scale. -/
theorem exact_scale (point : Canonical) : (exact point).scale = 0 := rfl

end Residual

end Purelib.Polynomial.Approximation.Gaussian

end
