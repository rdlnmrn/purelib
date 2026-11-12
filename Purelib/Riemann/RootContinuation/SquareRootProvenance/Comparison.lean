module

public import Purelib.Riemann.RootContinuation.SquareRootProvenance
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Gaussian.Norm.SquareResidual
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Operational comparison from a retained square-root sum floor

The two original channels have the same exact square identity. A positive
sum bound on their actual sampled readings turns the two independently paid
square residuals into the requested root comparison, retaining both original
sampling processes and both consumer start indices.
-/

public section

namespace Purelib.Riemann.RootContinuation.SquareRootProvenance

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat

/-- Compare two original square-root channels using a paid sum floor on all actual sampled readings.

The original square comparisons independently choose indices after the two
requested consumer starts. Their residual tolerances are the target times the
same retained positive sum floor divided by four. The scalar difference-of-
squares bound proves the operational comparison on every later pair of the
original samples, without constructing another root channel or owner.
-/
def equivalent_of_sum_lower {left right : CoherentNamed} {parameter : Canonical}
    (leftSquare : SquareIdentity left parameter) (rightSquare : SquareIdentity right parameter)
    (floor : Fraction.Rational) (positive : 0 < floor)
    (sumLower : ∀ leftIndex rightIndex,
      floor ≤ Canonical.normSq ((Name.Sampling.approximation left.name).sample leftIndex +
        (Name.Sampling.approximation right.name).sample rightIndex)) :
    NamedEquivalent left.name right.name where
  compare := by
    intro leftStart rightStart target targetPositive
    let residualTarget := target * floor / 4
    have residualPositive : 0 < residualTarget := Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.mul_pos_direct targetPositive positive) (by decide +kernel)
    let first := (sampled_square leftSquare).compare leftStart 0 residualTarget residualPositive
    let second := (sampled_square rightSquare).compare rightStart 0 residualTarget residualPositive
    refine
      { leftIndex := first.leftIndex
        rightIndex := second.leftIndex
        left_ge := first.left_ge
        right_ge := second.left_ge
        close := ?_ }
    intro leftLater rightLater leftOrder rightOrder
    have leftResidual := first.close leftOrder (Nat.le_refl first.rightIndex)
    have rightResidual := second.close rightOrder (Nat.le_refl second.rightIndex)
    rewrite [Norm.Basic.normSq_eq_canonical] at leftResidual rightResidual
    change Canonical.normSq ((Name.Sampling.approximation left.name).sample leftLater *
      (Name.Sampling.approximation left.name).sample leftLater - parameter) < residualTarget at leftResidual
    change Canonical.normSq ((Name.Sampling.approximation right.name).sample rightLater *
      (Name.Sampling.approximation right.name).sample rightLater - parameter) < residualTarget at rightResidual
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact Norm.SquareResidual.distance_lt_of_sum_lower positive (sumLower leftLater rightLater)
      leftResidual rightResidual

end Purelib.Riemann.RootContinuation.SquareRootProvenance

end
