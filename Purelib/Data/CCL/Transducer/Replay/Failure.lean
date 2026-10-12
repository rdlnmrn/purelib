module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
import Purelib.Approximation.Gaussian.Process.Recipe.Cursor
import Purelib.CCL.Progressive.IntegrationQueries
public import Purelib.Data.CCL.Transducer.Replay.Emission
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Finite numerical controller and adaptive replay

All executable state below is finite chart syntax, rational bounds, natural
source indices and bit lists.  In particular, neither a `Process` nor a
source evaluator occurs in a returned state.  Each productive chunk records
its model reads, including the second read after a residual inverse chart
change.  Buffered bits do not perform a model query.

This is the numerical interpreter.  Its connection to the certified
transducer is established separately; successful replay of an invented log
does not certify global coherence of its replies.
-/

namespace Purelib.Data.CCL.Transducer.Replay

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain a replay failure with the exact offending reply, observation or empty emission and its violated condition.

The alternatives distinguish source validation, an inaccurate radius, a missing normalization lower bound, a low-state
overshoot and an empty emitted chunk. Each observation remains attached to its original index or recipe cursor. -/
inductive Failure where
  /-- Retain the exact invalid source reply and its existing validation evidence. -/ | source (error :
    CCL.Progressive.IntegrationReplay.InvalidReply)
  /-- Retain the source index, requested target and returned ball violating nonnegative radius squared strictly below
    target. -/ | inaccurate (index : Nat) (target : Fraction.Rational) (ball : Enclosure.Ball.Data.BallData)
      (violated : ¬ (0 ≤ ball.radiusSq ∧ ball.radiusSq < target))
  /-- Retain the exact recipe cursor and ball whose center fails the unit squared-norm lower bound. -/ | unnormalized
    (cursor : Approximation.Gaussian.Process.Recipe.Cursor) (ball : Enclosure.Ball.Data.BallData)
      (violated : ¬ 1 ≤ Gaussian.Norm.Basic.normSq ball.center)
  /-- Retain the exact recipe cursor and ball whose center fails the strict 13/6 squared-norm upper bound. -/ |
    lowOvershoot (cursor : Approximation.Gaussian.Process.Recipe.Cursor) (ball : Enclosure.Ball.Data.BallData)
      (violated : ¬ Gaussian.Norm.Basic.normSq ball.center < 13 / 6)
  /-- Retain the emitted prefix, exact replay emission and proof that its bit chunk is empty. -/ | emptyEmission
    (emitted : List Bool) (emission : Emission) (empty : emission.bits = [])
deriving DecidableEq

constructive_injectivity Failure

end Purelib.Data.CCL.Transducer.Replay

end
