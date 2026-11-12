module

public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
public import Purelib.Geometry.Rational.Box.Square.Centered.Separation
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Exact roots in one retained signed square

An actual certified root channel and an independently supplied exact root of
its radicand agree when both retain the same original signed square. The
existing square comparison pays the original positive sum floor and keeps
both consumer start indices. No root owner or sampler is reconstructed.
-/

public section

namespace Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Exact

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Geometry.Rational.Box.Square.Centered (Separation)

/-- Compare an original certified root channel with an exact root in the same retained signed square.

Every actual candidate of the original process remains in the supplied
separation square. The independent exact root lies in that identical square
and squares to the unchanged certified radicand. The square comparison
chooses an index after the consumer's left start with its residual target
scaled by four original radius squares; the exact right sampler keeps its
requested start. This constructs operational agreement on the original name.
-/
def agrees {parameter center : Canonical} (source : Certificate parameter)
    (separation : Separation center) (root : Canonical) (square : root ^ 2 = parameter)
    (inside : (Box.Square.Centered.Affine.centeredSquare center separation.radius separation.positive.le).Contains root)
    (candidates : ∀ {state : source.value.name.process.State} {candidate : Canonical},
      source.value.name.process.Possible state candidate →
      (Box.Square.Centered.Affine.centeredSquare center separation.radius separation.positive.le).Contains candidate) :
    NamedEquivalent source.value.name (Named.exact root) where
  compare := by
    intro leftStart rightStart target positive
    let floor := 4 * separation.radius ^ 2
    have floorPositive : 0 < floor := Fraction.Order.Arithmetic.mul_pos_direct (by decide +kernel)
      (Fraction.Order.Arithmetic.pow_pos_direct separation.positive 2)
    let comparison := (Sampling.squareComparison source).compare leftStart 0 (target * floor)
      (Fraction.Order.Arithmetic.mul_pos_direct positive floorPositive)
    refine
      { leftIndex := comparison.leftIndex
        rightIndex := rightStart
        left_ge := comparison.left_ge
        right_ge := Nat.le_refl _
        close := ?_ }
    intro leftLater rightLater leftOrder _rightOrder
    let value := (Name.Sampling.approximation source.value.name).sample leftLater
    have possible := Process.Sampling.witnessAt_possible source.value.name.process source.value.name.state leftLater
    have contained := candidates possible
    have sumLower := separation.sum_normSq_lower contained inside
    have residual := comparison.close leftOrder (Nat.le_refl comparison.rightIndex)
    rewrite [Sequence.Name.Exact.exactNamedSample] at residual
    change Norm.Basic.normSq (value * value - parameter) < target * floor at residual
    rewrite [← square] at residual
    rewrite [Sequence.Name.Exact.exactNamedSample]
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := floor) _ floorPositive
    calc
      _ ≤ Norm.Basic.normSq (value - root) * Norm.Basic.normSq (value + root) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumLower (Norm.Basic.normSq_nonneg _)
      _ = Norm.Basic.normSq (value * value - root ^ 2) := by
        rewrite [← Norm.Basic.normSq_mul,
          show (value - root) * (value + root) = value * value - root ^ 2 by ring1]
        rfl
      _ < _ := residual

end Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Exact
