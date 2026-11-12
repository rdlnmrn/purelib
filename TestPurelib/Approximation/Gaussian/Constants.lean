module

import Purelib.Examples.Approximation.Gaussian.Constants
public meta import Purelib.Examples.Approximation.Gaussian.Constants
import Purelib.Approximation.Gaussian.Equivalence.Presentation
meta import Purelib.Approximation.Gaussian.Equivalence.Presentation
import Purelib.Approximation.Gaussian.Sequence.Presentation
meta import Purelib.Approximation.Gaussian.Sequence.Presentation
import Purelib.Approximation.Gaussian.Name.Sampling
meta import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Pi.Polygon.Presentation
import Purelib.Approximation.Gaussian.SquareRoot.Two
meta import Purelib.Approximation.Gaussian.SquareRoot.Two
import Purelib.Approximation.Rational.SquareRoot.Two
meta import Purelib.Approximation.Rational.SquareRoot.Two

namespace TestPurelib.Approximation.Gaussian.Constants

open Purelib.Examples.Approximation.Gaussian.Constants
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Sequence
open SamplePrefix.Entry
open Purelib.Data.Rat
open Purelib.Approximation.Rational.SquareRoot

/-- info: (true, true, true, true, true, true) -/
#guard_msgs in
#eval (let coarse := Two.bracket 0
  let fine := Two.bracket 3
  (coarse.lower == 1, coarse.upper == 2,
    fine.lower == 11 / 8, fine.upper == 3 / 2,
    fine.upper - fine.lower == 1 / 8,
    decide (coarse.lower ≤ fine.upper)))

example (stage : Nat) :
    0 ≤ (Two.bracket stage).lower ∧ (Two.bracket stage).lower ^ 2 ≤ 2 :=
  Two.lower_spec stage

example (stage : Nat) :
    0 < (Two.bracket stage).upper ∧ 2 < (Two.bracket stage).upper ^ 2 :=
  Two.upper_spec stage

example (stage : Nat) :
    (Two.bracket stage).upper - (Two.bracket stage).lower = 1 / (2 ^ stage : Nat) :=
  Two.width_eq stage

example {earlier later : Nat} (ordered : earlier ≤ later) :
    Fraction.abs ((Two.bracket later).upper - (Two.bracket earlier).upper) ≤
      1 / (2 ^ earlier : Nat) :=
  Two.upper_abs_difference_le ordered

example {earlier later : Nat} (ordered : earlier ≤ later) :
    Purelib.Data.Gaussian.Norm.Basic.normSq
      (SquareRoot.Two.sample later - SquareRoot.Two.sample earlier) ≤
        Purelib.Approximation.Rational.Geometric.Basic.quarterRadius 1 earlier :=
  SquareRoot.Two.later_close ordered

/-- info: (true, true, 7) -/
#guard_msgs in
#eval ((SquareRoot.Two.sample 0).re == 2,
  (SquareRoot.Two.sample 1).re == 3 / 2,
  SquareRoot.Two.approximation.refineIndex 7 1 (by decide))

example (current : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    current ≤ SquareRoot.Two.approximation.refineIndex current target positive ∧
      SquareRoot.Two.approximation.radiusSq
        (SquareRoot.Two.approximation.refineIndex current target positive) < target :=
  ⟨SquareRoot.Two.approximation.refineIndex_ge current target positive,
    SquareRoot.Two.approximation.refineIndex_accurate current target positive⟩

example (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    leftStart ≤ (expressionComparison leftStart rightStart target positive).leftIndex ∧
      rightStart ≤ (expressionComparison leftStart rightStart target positive).rightIndex :=
  ⟨(expressionComparison leftStart rightStart target positive).left_ge,
    (expressionComparison leftStart rightStart target positive).right_ge⟩

example (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target)
    {leftLater rightLater : Nat}
    (left : (expressionComparison leftStart rightStart target positive).leftIndex ≤ leftLater)
    (right : (expressionComparison leftStart rightStart target positive).rightIndex ≤ rightLater) :=
  (expressionComparison leftStart rightStart target positive).close left right

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval (let target : Fraction.Rational := (65536 : Nat)
  let positive : 0 < target := Fraction.Cast.Order.natCast_pos_direct (by decide)
  let first := expressionComparison 1 0 target positive
  let second := expressionComparison 0 1 target positive
  (decide (1 ≤ first.leftIndex), decide (0 ≤ first.rightIndex),
    decide (0 ≤ second.leftIndex), decide (1 ≤ second.rightIndex)))

example (current : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    current ≤ Pi.Polygon.approximation.refineIndex current target positive ∧
      Pi.Polygon.approximation.radiusSq (Pi.Polygon.approximation.refineIndex current target positive) < target :=
  ⟨Pi.Polygon.refine_ge current target positive, Pi.Polygon.refine_accurate current target positive⟩

example : Pi.Polygon.approximation.refineIndex 7 4 (by decide) = 7 := by decide

example : (Pi.Polygon.named.name.process.ball Pi.Polygon.named.name.state).center =
    (⟨2, 0⟩ : Purelib.Data.Gaussian.Basic.Canonical) := by decide

example (stage : Nat) :
    (Pi.Polygon.named.name.process.ball (show Pi.Polygon.named.name.process.State from stage)).center =
      Purelib.Data.Gaussian.RationalEmbedding.realPoint
        (Purelib.Geometry.Gaussian.UnitCircle.Polygon.area
          (Purelib.Approximation.Rational.Pi.Polygon.dyadicExtra stage)) :=
  Pi.Polygon.named_center_area stage

private def checkSampleWitnesses (approximation : ApproximationData) : Bool × Bool × Bool × Bool × Bool :=
  let sample := approximation.sample 1
  let wrong := { sample with re := sample.re + 1 }
  let entry : SamplePrefix.Entry approximation := ⟨1, sample, rfl⟩
  ((match ApproximationData.checkWitness approximation 1 1 sample with
    | .valid _ => true | _ => false),
   (match ApproximationData.checkWitness approximation 2 1 sample with
    | .beforeStart _ => true | _ => false),
   (match ApproximationData.checkWitness approximation 1 1 wrong with
    | .wrongSample _ => true | _ => false),
   (match ApproximationData.checkEntry 1 entry with
    | .valid _ => true | _ => false),
   (match ApproximationData.checkEntry 2 entry with
    | .beforeStart _ => true | _ => false))

/-- info: ((true, true, true, true, true), true, true, true, true, true) -/
#guard_msgs in
#eval (checkSampleWitnesses Exponential.E.factorialApproximation,
  checkSampleWitnesses Pi.Polygon.approximation)

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval checkSampleWitnesses Exponential.E.hornerApproximation

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval checkSampleWitnesses (Name.Sampling.approximation Pi.Integral.named.name)

example {approximation : ApproximationData} {start later : Nat}
    {value : Purelib.Data.Gaussian.Basic.Canonical}
    (valid : ApproximationData.WitnessValid approximation start later value) :
    approximation.Possible start value := ApproximationData.possible_of_witness valid

private def checkEntryPresentation (original : ApproximationData) : Bool × Bool × Bool × Bool :=
  let value := original.sample 1
  let entry : SamplePrefix.Entry original := ⟨1, value, rfl⟩
  let copy : SamplePrefix.Entry original := ⟨1, value, Eq.trans rfl rfl⟩
  let first := Presentation.quote entry
  let second := Presentation.quote copy
  let other : SamplePrefix.Entry original := ⟨0, original.sample 0, rfl⟩
  let wrong := { value with re := value.re + 1 }
  ((match Presentation.check original (1, value) with
    | .valid proof =>
      match Presentation.compare (Presentation.quote (Presentation.read ⟨(1, value), proof⟩)) first with
      | .isTrue _ => true | .isFalse _ => false
    | _ => false),
   (match Presentation.check original (1, wrong) with
    | .wrongSample _ => true | _ => false),
   (match Presentation.compare first second with
    | .isTrue _ => true | .isFalse _ => false),
   (match Presentation.compare first (Presentation.quote other) with
    | .isTrue _ => false | .isFalse _ => true))

/-- info: ((true, true, true, true), true, true, true, true) -/
#guard_msgs in
#eval (checkEntryPresentation Exponential.E.factorialApproximation,
  checkEntryPresentation Pi.Polygon.approximation)

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval checkEntryPresentation Exponential.E.hornerApproximation

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval checkEntryPresentation (Name.Sampling.approximation Pi.Integral.named.name)

example {original : ApproximationData} (index : Nat) (value : Purelib.Data.Gaussian.Basic.Canonical)
    (first second : value = original.sample index) :
    (⟨index, value, first⟩ : SamplePrefix.Entry original) = ⟨index, value, second⟩ := by
  cases Subsingleton.elim first second
  rfl

example {original : ApproximationData} (entry : SamplePrefix.Entry original) :
    Presentation.read (Presentation.quote entry) = entry := Presentation.read_quote entry

private def proofCopy {left right : ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (value : Equivalence.Comparison left right leftStart rightStart target) :
    Equivalence.Comparison left right leftStart rightStart target where
  leftIndex := value.leftIndex
  rightIndex := value.rightIndex
  left_ge := Nat.le_trans value.left_ge (Nat.le_refl _)
  right_ge := Nat.le_trans value.right_ge (Nat.le_refl _)
  close := fun leftOrder rightOrder => value.close leftOrder rightOrder

private def laterLeft {left right : ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (value : Equivalence.Comparison left right leftStart rightStart target) :
    Equivalence.Comparison left right leftStart rightStart target where
  leftIndex := value.leftIndex + 1
  rightIndex := value.rightIndex
  left_ge := Nat.le_trans value.left_ge (Nat.le_succ _)
  right_ge := value.right_ge
  close := fun leftOrder rightOrder => value.close (Nat.le_trans (Nat.le_succ _) leftOrder) rightOrder

private def checkIdentity {left right : ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (value : Equivalence.Comparison left right leftStart rightStart target) :
    Bool × Bool :=
  ((match Equivalence.Comparison.decideEquality value (proofCopy value) with
    | .isTrue _ => true | .isFalse _ => false),
   (match Equivalence.Comparison.decideEquality value (laterLeft value) with
    | .isTrue _ => false | .isFalse _ => true))

/-- info: ((true, true), true, true) -/
#guard_msgs in
#eval (checkIdentity (Exponential.E.factorial_equivalent_horner.compare 1 0 4 (by decide)),
  checkIdentity (Pi.Comparison.polygon_equivalent_integral.compare 1 0 4 (by decide)))

private def checkSuppliedFloors {left right : ApproximationData} {leftStart rightStart : Nat}
    {target : Fraction.Rational} (value : Equivalence.Comparison left right leftStart rightStart target) :
    Bool × Bool × Bool :=
  ((match Equivalence.Comparison.checkFloors left right leftStart rightStart target
      value.leftIndex value.rightIndex value.close with
    | .accepted found _ _ =>
      match Equivalence.Comparison.decideEquality value found with
      | .isTrue _ => true | .isFalse _ => false
    | _ => false),
   (match Equivalence.Comparison.checkFloors left right (value.leftIndex + 1) rightStart target
      value.leftIndex value.rightIndex value.close with
    | .leftBelow _ => true | _ => false),
   (match Equivalence.Comparison.checkFloors left right leftStart (value.rightIndex + 1) target
      value.leftIndex value.rightIndex value.close with
    | .rightBelow _ => true | _ => false))

/-- info: ((true, true, true), true, true, true) -/
#guard_msgs in
#eval (checkSuppliedFloors (Exponential.E.factorial_equivalent_horner.compare 1 0 4 (by decide)),
  checkSuppliedFloors (Pi.Comparison.polygon_equivalent_integral.compare 1 0 4 (by decide)))

example {left right : ApproximationData} {leftStart rightStart : Nat} {target : Fraction.Rational}
    (value : Equivalence.Comparison left right leftStart rightStart target) :=
  Equivalence.Comparison.checkFloors_comparison value

private def checkFloors {left right : ApproximationData} (bridge : Equivalence.Equivalent left right) : Bool :=
  let first := bridge.compare 1 0 4 (by decide)
  let later := (bridge.withFloors (first.leftIndex + 1) 0).compare 1 0 4 (by decide)
  match Equivalence.Comparison.decideEquality first later with
  | .isTrue _ => false
  | .isFalse _ => true

/-- info: (true, true) -/
#guard_msgs in
#eval (checkFloors Exponential.E.factorial_equivalent_horner,
  checkFloors Pi.Comparison.polygon_equivalent_integral)

example : 1 ≤ comparison.leftIndex := comparison.left_ge

example : 0 ≤ comparison.rightIndex := comparison.right_ge

example (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :=
  Pi.Comparison.polygon_equivalent_integral_indices leftStart rightStart target positive

/-- info: (7, 2, 2, 7) -/
#guard_msgs in
#eval (let original := Pi.Comparison.polygon_equivalent_integral.compare 7 2 4 (by decide)
  let selected := Pi.Comparison.polygon_equivalent_integral.compare 2 7 4 (by decide)
  (original.leftIndex, original.rightIndex, selected.leftIndex, selected.rightIndex))

example {leftLater rightLater : Nat} (left : comparison.leftIndex ≤ leftLater)
    (right : comparison.rightIndex ≤ rightLater) := comparison.close left right

#eval (comparison.leftIndex, comparison.rightIndex)

end TestPurelib.Approximation.Gaussian.Constants
