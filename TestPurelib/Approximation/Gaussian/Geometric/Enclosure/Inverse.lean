module
import Purelib.System.IO
import Purelib.Approximation.Gaussian.Geometric.Enclosure.Inverse
import Purelib.Approximation.Gaussian.Geometric.Preparation
import Purelib.Approximation.Gaussian.Enclosure.Residual

namespace TestPurelib.Approximation.Gaussian.Geometric.Enclosure.Inverse

open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

/-- Every actual original sample inverse remains in the same original common-ball division enclosure. -/
example {channel : CoherentNamed} (original : Enclosure channel) (prepared : Prepared channel)
    (apart : Ball.Apart original.ball) (index : Nat) :
    (original.inverse prepared apart).ball.Contains ((original.source.sample index)⁻¹) :=
  original.inverse_contains prepared apart index

/-- Reciprocal enclosure preparation retains the same original prepared quotient channel. -/
example {channel : CoherentNamed} (original : Enclosure channel) (prepared : Prepared channel)
    (apart : Ball.Apart original.ball) :
    NamedEquivalent (prepared.quotient (CoherentNamed.Coherence.exact 1)).name
      (original.inverse prepared apart).source.toApproximation.toNamed :=
  (original.inverse prepared apart).equivalent

/-- Reciprocal enclosure readback retains the original domain certificate and complete common division ball. -/
example {channel : CoherentNamed} (original : Enclosure channel) (prepared : Prepared channel)
    (apart : Ball.Apart original.ball) :
    (original.inverse prepared apart).ball = (Ball.point 1).div original.ball apart :=
  original.inverse_ball prepared apart

/-- The intrinsic geometric inverse retains its computed movement scale from every original source and lower bound. -/
example (source : GeometricApproximation) (lower : Rational) (positive : 0 < lower)
    (bound : ∀ index, lower ≤ Norm.Basic.normSq (source.sample index)) :
    (source.inverse lower positive bound).errorScale = source.errorScale * (lower⁻¹ * lower⁻¹) :=
  source.inverse_errorScale lower positive bound

/-- The intrinsic geometric inverse retains its original all-index quantitative norm bound. -/
example (source : GeometricApproximation) (lower : Rational) (positive : 0 < lower)
    (bound : ∀ index, lower ≤ Norm.Basic.normSq (source.sample index)) (index : Nat) :
    Norm.Basic.normSq ((source.inverse lower positive bound).sample index) ≤ lower⁻¹ := by
  have bounded := (source.inverse lower positive bound).sample_bounded index
  rewrite [GeometricApproximation.inverse_centerBound] at bounded
  exact bounded

/-- Exercise the formal reciprocal using actual original lower-driven preparation and a nonreal common ball. -/
public def check : IO Unit := do
  let point : Basic.Canonical := ⟨3, 4⟩
  let original := Enclosure.exact point
  have separated : Preparation.Separated original.ball := by
    rewrite [Enclosure.exact_ball]
    change (2 : Rational) * 0 < Norm.Basic.normSq (⟨3, 4⟩ : Basic.Canonical)
    decide +kernel
  let apart := Purelib.Approximation.Gaussian.Enclosure.Residual.apartOfCenter original.ball separated
  let initial := Refinement.State.initial (Preparation.sampledChannel original.source)
  let paid := Preparation.fromLower original.source (CoherentNamed.Coherence.exact point) original.equivalent
    initial apart.lowerSq apart.positive (fun index => apart.lower (original.contains index))
  let reciprocal := original.inverse paid.prepared apart
  let expected : Basic.Canonical := ⟨3 / 25, -4 / 25⟩
  unless reciprocal.source.sample 7 == expected && reciprocal.ball.center == expected &&
      reciprocal.ball.radiusSq == 0 && reciprocal.ball.Contains (reciprocal.source.sample 7) do
    throw (IO.userError "The formal reciprocal changed its original sample or common division ball")
  let comparison := reciprocal.equivalent.compare 3 7 (1 / 16 : Rational) (by decide +kernel)
  unless 3 ≤ comparison.leftIndex && 7 ≤ comparison.rightIndex do
    throw (IO.userError "The prepared reciprocal comparison changed the original requested starts")
  Purelib.System.IO.println
    s!"Original prepared formal inverse: comparison {comparison.leftIndex}/{comparison.rightIndex}"

end TestPurelib.Approximation.Gaussian.Geometric.Enclosure.Inverse
