module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart.Witness
public import Purelib.Approximation.Gaussian.Process.Apart
public import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Rational.Request.Common
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure.Ball.Apart

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Gaussian

open Purelib.Approximation.Rational.Request

section
@[expose] public section

/-!
# Constructive chart preparation for progressive CCL arithmetic

The local arithmetic controller needs two chart-side facts which are stronger
than mere convergence of a squared-error radius:

* a possible-value lower norm must be turned into apartness of the whole
  displayed rational ball before affine inversion; and
* a strict possible-value lower norm above one must be turned into a centre
  norm at least one before the redundant loop decision.

This module begins that bridge.  All witnesses are rational candidates in one
explicit finite state.  No completed value is selected.
-/

namespace Purelib.Approximation.Gaussian.Process.Apart.Preparation

set_option genInjectivity false in
/-- State of a process whose whole displayed ball, rather than merely its finite candidates, has been made uniformly
apart from zero. -/
structure ApartState (process :
  Approximation.Gaussian.Process) (apart : Possible.PossibleApart process) where
  /-- The retained finite state of the original process. -/ source : process.State
  /-- Every reading in the retained state's entire ball has quadrance at least one eighth of the original
    possible-reading lower bound. -/ wholeBallLower : ∀ {value : Data.Gaussian.Basic.Canonical},
    (process.ball source).Contains value → apart.lowerSq / 8 ≤ Data.Gaussian.Norm.Basic.normSq value

constructive_injectivity ApartState

/-- One finite refinement prepares an arbitrary state for safe affine inversion. -/
def prepareApartState {process :
  Approximation.Gaussian.Process} (apart : Possible.PossibleApart process)
    (state : process.State) : ApartState process apart := by
  let refined := process.refine state (apart.lowerSq / 12) apart.twelfth_pos
  rcases process.witness refined with ⟨witness, possible⟩
  let certificate := Witness.apartBallOfPossibleLower (process.ball refined)
    apart.lowerSq apart.positive witness (process.possible_inside possible)
    (apart.lower refined possible) (process.accurate state _ _)
  exact
    { source := refined
      wholeBallLower := certificate.lower }

/-- The apartified process. Its state type retains only explicit finite source states together with their finite
whole-ball separation proofs. -/
def apartify {source : Approximation.Gaussian.Process}
  (possibleApart : Possible.PossibleApart source) : Approximation.Gaussian.Process where
  State := ApartState source possibleApart
  ball state := source.ball state.source
  Possible state value := source.Possible state.source value
  witness state := source.witness state.source
  possible_inside possible := source.possible_inside possible
  refine state target positive := by
    let apartTarget := possibleApart.lowerSq / 12
    let inputTarget := Common.commonTarget target apartTarget
    have inputPositive : 0 < inputTarget :=
      Common.commonTarget_pos positive possibleApart.twelfth_pos
    let refined := source.refine state.source inputTarget inputPositive
    rcases source.witness refined with ⟨witness, possible⟩
    have fine : (source.ball refined).radiusSq < possibleApart.lowerSq / 12 :=
      (source.accurate state.source inputTarget inputPositive).trans
        (Common.commonTarget_lt_right positive possibleApart.twelfth_pos)
    let certificate := Witness.apartBallOfPossibleLower (source.ball refined)
      possibleApart.lowerSq possibleApart.positive witness
      (source.possible_inside possible) (possibleApart.lower refined possible)
      fine
    exact
      { source := refined
        wholeBallLower := certificate.lower }
  refine_persists := by
    intro state target positive value possible
    exact source.refine_persists state.source _ _ possible
  accurate := by
    intro state target positive
    exact (source.accurate state.source _ _).trans
      (Common.commonTarget_lt_left positive possibleApart.twelfth_pos)
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  center_bounded state := source.center_bounded state.source

/-- Uniform ball apartness of the apartified process. -/
def apartifyApart {source :
  Approximation.Gaussian.Process} (possibleApart : Possible.PossibleApart source) :
    Process.Apart
      (apartify possibleApart) where
  lowerSq := possibleApart.lowerSq / 8
  positive := possibleApart.eighth_pos
  lower state := state.wholeBallLower

/-- The prepared state belongs to the apartified process and preserves every later candidate as a candidate of the
original supplied state. -/
theorem prepareApartState_persists {process :
  Approximation.Gaussian.Process}
    (apart : Possible.PossibleApart process) (state : process.State) {value : Data.Gaussian.Basic.Canonical}
    (possible : (apartify apart).Possible
      (prepareApartState apart state) value) :
    process.Possible state value :=
  process.refine_persists state _ _ possible
end Purelib.Approximation.Gaussian.Process.Apart.Preparation

end
