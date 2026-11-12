module
import Purelib.Approximation.Gaussian.Geometric.Enclosure.Inverse
import Purelib.Approximation.Gaussian.Geometric.Preparation
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.System.IO

namespace TestPurelib.Approximation.Gaussian.Geometric.Enclosure.Bounds

open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

/-- A supplied exact ball retains the complete original constant enclosure. -/
example (value : Basic.Canonical) (ball : Ball) (same : ball = Ball.point value) :
    Enclosure.exactFromBall value ball same = Enclosure.exact value :=
  Enclosure.exactFromBall_eq value ball same

/-- Supplied unary bounds retain the complete original program, comparison and sample enclosure. -/
example {channel : CoherentNamed} (source : Enclosure channel) (negative power conjugate : Ball)
    (negative_eq : negative = source.ball.neg) (exponent : Nat)
    (power_eq : power = source.ball.pow exponent) (conjugate_eq : conjugate = source.ball.conj) :
    source.negFromBall negative negative_eq = source.neg ∧
      source.powFromBall exponent power power_eq = source.pow exponent ∧
      source.conjFromBall conjugate conjugate_eq = source.conj :=
  ⟨source.negFromBall_eq negative negative_eq, source.powFromBall_eq exponent power power_eq,
    source.conjFromBall_eq conjugate conjugate_eq⟩

/-- Supplied ordered binary bounds retain both complete original operands and their arithmetic programs. -/
example {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (sum difference product : Ball) (sum_eq : sum = left.ball.add right.ball)
    (difference_eq : difference = left.ball.sub right.ball) (product_eq : product = left.ball.mul right.ball) :
    left.addFromBall right sum sum_eq = left.add right ∧
      left.subFromBall right difference difference_eq = left.sub right ∧
      left.mulFromBall right product product_eq = left.mul right :=
  ⟨left.addFromBall_eq right sum sum_eq, left.subFromBall_eq right difference difference_eq,
    left.mulFromBall_eq right product product_eq⟩

/-- Supplied reciprocal bounds retain the original prepared denominator and complete inverse enclosure. -/
example {channel : CoherentNamed} (source : Enclosure channel) (prepared : Prepared channel)
    (apart : Ball.Apart source.ball) (ball : Ball) (same : ball = (Ball.point 1).div source.ball apart) :
    source.inverseFromBall prepared apart ball same = source.inverse prepared apart :=
  source.inverseFromBall_eq prepared apart ball same

/-- Every original sample belongs to the supplied product enclosure without replacing its program. -/
example {first second : CoherentNamed} (left : Enclosure first) (right : Enclosure second)
    (ball : Ball) (same : ball = left.ball.mul right.ball) (index : Nat) :
    ball.Contains ((left.mulFromBall right ball same).source.sample index) :=
  left.mulFromBall_contains right ball same index

/-- Exercise once-computed bounds for all operations and an actual paid nonreal reciprocal. -/
public def check : IO Unit := do
  let value : Basic.Canonical := ⟨3, 4⟩
  let baseBall := Ball.point value
  let original := Enclosure.exactFromBall value baseBall rfl
  let oneBall := Ball.point 1
  let one := Enclosure.exactFromBall 1 oneBall rfl
  let negativeBall := original.ball.neg
  let negative := original.negFromBall negativeBall rfl
  let sumBall := original.ball.add one.ball
  let sum := original.addFromBall one sumBall rfl
  let differenceBall := original.ball.sub one.ball
  let difference := original.subFromBall one differenceBall rfl
  let productBall := original.ball.mul original.ball
  let product := original.mulFromBall original productBall rfl
  let powerBall := original.ball.pow 3
  let power := original.powFromBall 3 powerBall rfl
  let conjugateBall := original.ball.conj
  let conjugate := original.conjFromBall conjugateBall rfl
  unless negative.source.sample 7 == -value && sum.source.sample 7 == value + 1 &&
      difference.source.sample 7 == value - 1 && product.source.sample 7 == value * value &&
      power.source.sample 7 == value ^ 3 && conjugate.source.sample 7 == Basic.conj value do
    throw (IO.userError "A supplied bound changed the original formal arithmetic samples")
  unless negative.ball.center == negativeBall.center && sum.ball.center == sumBall.center &&
      difference.ball.center == differenceBall.center && product.ball.center == productBall.center &&
      power.ball.center == powerBall.center && conjugate.ball.center == conjugateBall.center do
    throw (IO.userError "An arithmetic constructor discarded its supplied exact ball")
  have separated : Preparation.Separated original.ball := by
    rewrite [Enclosure.exactFromBall_ball]
    change (2 : Rational) * 0 < Norm.Basic.normSq (⟨3, 4⟩ : Basic.Canonical)
    decide +kernel
  let apart := Purelib.Approximation.Gaussian.Enclosure.Residual.apartOfCenter original.ball separated
  let initial := Refinement.State.initial (Preparation.sampledChannel original.source)
  let paid := Preparation.fromLower original.source (CoherentNamed.Coherence.exact value) original.equivalent
    initial apart.lowerSq apart.positive (fun index => apart.lower (original.contains index))
  let inverseBall := oneBall.div original.ball apart
  let inverse := original.inverseFromBall paid.prepared apart inverseBall rfl
  unless inverse.source.sample 7 == (⟨3 / 25, -4 / 25⟩ : Basic.Canonical) &&
      inverse.ball.center == inverseBall.center && inverse.ball.radiusSq == inverseBall.radiusSq do
    throw (IO.userError "The supplied reciprocal bound changed its original prepared inverse")
  let compared := inverse.equivalent.compare 3 7 (1 / 16 : Rational) (by decide +kernel)
  unless 3 ≤ compared.leftIndex && 7 ≤ compared.rightIndex do
    throw (IO.userError "The supplied inverse changed its original comparison starts")
  Purelib.System.IO.println "Retained exact balls: all arithmetic programs and paid reciprocal checked"

end TestPurelib.Approximation.Gaussian.Geometric.Enclosure.Bounds
