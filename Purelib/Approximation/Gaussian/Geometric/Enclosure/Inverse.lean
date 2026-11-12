module
public import Purelib.Approximation.Gaussian.Geometric.Enclosure
public import Purelib.Approximation.Gaussian.Geometric.Inverse
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Division
public import Purelib.Approximation.Gaussian.Division.Prepared.Quotient.Inverse
import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence

/-! # Common enclosures of original formal reciprocals at prepared channels -/

public section

namespace Purelib.Approximation.Gaussian.Geometric.Enclosure

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Polynomial.Approximation
open Purelib.Data.Gaussian

/-- Enclose the formal reciprocal of every original sample on the actual retained prepared quotient.

The original common-ball apartness supplies the all-index lower quadrance.
The supplied division ball is retained with its exact original-formula equality.
The formal inverse program and common division ball are cached before future
samples. Product cancellation compares that same program to the original
prepared quotient without replacing the preparation or identifying its
samples with a reciprocal residual program.
-/
def inverseFromBall {channel : CoherentNamed} (original : Enclosure channel)
    (prepared : Division.Prepared channel) (apart : Ball.Apart original.ball) (ball : Ball)
    (same : ball = (Ball.point 1).div original.ball apart) :
    Enclosure (prepared.quotient (CoherentNamed.Coherence.exact 1)) := by
  let lower := fun index => apart.lower (original.contains index)
  let source := original.source.inverse apart.lowerSq apart.positive lower
  let inverseChannel := CoherentNamed.ofApproximation source.toApproximation
  have nonzero (index : Nat) : original.source.sample index ≠ 0 := by
    intro zero
    have bound := lower index
    rewrite [zero, Norm.Basic.normSq_zero] at bound
    exact (not_le_of_gt apart.positive) bound
  have unitSamples (index : Nat) : (GeometricApproximation.exact 1).toApproximation.sample index =
      original.source.toApproximation.sample index * source.toApproximation.sample index := by
    change 1 = original.source.sample index * source.sample index
    rewrite [GeometricApproximation.inverse_sample]
    exact (Basic.Canonical.mul_inv_cancel _ (nonzero index)).symm
  let pointwise := Sequence.Arithmetic.Multiplication.Bridge.mulToNamed_equivalent_pointwise
    original.source.toApproximation source.toApproximation (GeometricApproximation.exact 1).toApproximation unitSamples
  let product := (Congruence.coherentMul_respects channel
    (CoherentNamed.ofApproximation original.source.toApproximation) inverseChannel inverseChannel
    original.equivalent (NamedEquivalent.refl _)).trans
      (pointwise.trans (CoherentEvaluation.exact_agrees 1).symm)
  let equivalent := prepared.reciprocal_equivalent_of_product inverseChannel product
  have contains (index : Nat) : ball.Contains (source.sample index) := by
    have contained : ((Ball.point 1).div original.ball apart).Contains (source.sample index) := by
      rewrite [GeometricApproximation.inverse_sample_div]
      exact Ball.contains_div apart (Ball.contains_point 1) (original.contains index)
    exact same.symm ▸ contained
  exact ⟨source, equivalent, ball, contains⟩

/-- Enclose the original formal reciprocal with its computed original division ball. -/
def inverse {channel : CoherentNamed} (original : Enclosure channel)
    (prepared : Division.Prepared channel) (apart : Ball.Apart original.ball) :
    Enclosure (prepared.quotient (CoherentNamed.Coherence.exact 1)) :=
  original.inverseFromBall prepared apart ((Ball.point 1).div original.ball apart) rfl

/-- Supplied-ball inversion retains the complete original formal reciprocal enclosure. -/
theorem inverseFromBall_eq {channel : CoherentNamed} (original : Enclosure channel)
    (prepared : Division.Prepared channel) (apart : Ball.Apart original.ball) (ball : Ball)
    (same : ball = (Ball.point 1).div original.ball apart) :
    original.inverseFromBall prepared apart ball same = original.inverse prepared apart := by
  cases same
  rfl

/-- Supplied-ball inversion retains its original ball and all-index containment. -/
private theorem inverseFromBall_readback {channel : CoherentNamed} (original : Enclosure channel)
    (prepared : Division.Prepared channel) (apart : Ball.Apart original.ball) (ball : Ball)
    (same : ball = (Ball.point 1).div original.ball apart) :
    (original.inverseFromBall prepared apart ball same).ball = ball ∧
      ∀ index, ball.Contains ((original.inverseFromBall prepared apart ball same).source.sample index) :=
  ⟨rfl, fun index => (original.inverseFromBall prepared apart ball same).contains index⟩

/-- Supplied-ball inversion consumes exactly the retained original division ball. -/
theorem inverseFromBall_ball {channel : CoherentNamed} (original : Enclosure channel)
    (prepared : Division.Prepared channel) (apart : Ball.Apart original.ball) (ball : Ball)
    (same : ball = (Ball.point 1).div original.ball apart) :
    (original.inverseFromBall prepared apart ball same).ball = ball :=
  (inverseFromBall_readback original prepared apart ball same).1

/-- Every actual original formal reciprocal reading belongs to the same retained supplied ball. -/
theorem inverseFromBall_contains {channel : CoherentNamed} (original : Enclosure channel)
    (prepared : Division.Prepared channel) (apart : Ball.Apart original.ball) (ball : Ball)
    (same : ball = (Ball.point 1).div original.ball apart) (index : Nat) :
    ball.Contains ((original.inverseFromBall prepared apart ball same).source.sample index) :=
  (inverseFromBall_readback original prepared apart ball same).2 index

/-- Formal reciprocal construction retains the exact inverse program and common division ball. -/
private theorem inverse_readback {channel : CoherentNamed} (original : Enclosure channel)
    (prepared : Division.Prepared channel) (apart : Ball.Apart original.ball) :
    (original.inverse prepared apart).source = original.source.inverse apart.lowerSq apart.positive
      (fun index => apart.lower (original.contains index)) ∧
    (original.inverse prepared apart).ball = (Ball.point 1).div original.ball apart := ⟨rfl, rfl⟩

/-- The reciprocal enclosure retains the actual formal inverse of the original geometric program. -/
theorem inverse_source {channel : CoherentNamed} (original : Enclosure channel)
    (prepared : Division.Prepared channel) (apart : Ball.Apart original.ball) :
    (original.inverse prepared apart).source = original.source.inverse apart.lowerSq apart.positive
      (fun index => apart.lower (original.contains index)) := (inverse_readback original prepared apart).1

/-- The reciprocal enclosure retains the original-ball division construction and its actual apartness certificate. -/
theorem inverse_ball {channel : CoherentNamed} (original : Enclosure channel)
    (prepared : Division.Prepared channel) (apart : Ball.Apart original.ball) :
    (original.inverse prepared apart).ball = (Ball.point 1).div original.ball apart :=
  (inverse_readback original prepared apart).2

/-- The formal reciprocal enclosure reads the inverse of the same original sample at its unchanged index. -/
theorem inverse_sample {channel : CoherentNamed} (original : Enclosure channel)
    (prepared : Division.Prepared channel) (apart : Ball.Apart original.ball) (index : Nat) :
    (original.inverse prepared apart).source.sample index = (original.source.sample index)⁻¹ := by
  rewrite [inverse_source]
  exact GeometricApproximation.inverse_sample _ _ _ _ index

/-- Every original formal reciprocal reading remains inside the retained common division ball. -/
theorem inverse_contains {channel : CoherentNamed} (original : Enclosure channel)
    (prepared : Division.Prepared channel) (apart : Ball.Apart original.ball) (index : Nat) :
    (original.inverse prepared apart).ball.Contains ((original.source.sample index)⁻¹) := by
  have inside := (original.inverse prepared apart).contains index
  rewrite [inverse_sample] at inside
  exact inside

/-- Supplied-ball inversion retains the exact original formal inverse program and its actual lower bound. -/
theorem inverseFromBall_source {channel : CoherentNamed} (original : Enclosure channel)
    (prepared : Division.Prepared channel) (apart : Ball.Apart original.ball) (ball : Ball)
    (same : ball = (Ball.point 1).div original.ball apart) :
    (original.inverseFromBall prepared apart ball same).source = original.source.inverse apart.lowerSq apart.positive
      (fun index => apart.lower (original.contains index)) := by
  rewrite [inverseFromBall_eq]
  exact inverse_source original prepared apart

end Purelib.Approximation.Gaussian.Geometric.Enclosure

end
