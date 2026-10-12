module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Sector.Decision
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Transducer.Emission.Basic
import Purelib.Data.CCL.Transducer.Emission.Initial
import Purelib.Data.CCL.Transducer.Emission.Initial.Preparation
public import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Step
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.List.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Numerical observation of the actual initial CCL decision

This finite projection records which initial chart the existing controller
selects from its refined rational center.  The projection theorems refer to
`initialStep` and `advance`, not to an unrelated encoder.  They cover the
initial decision and first bit only; they do not claim to replay later chart
states or an arbitrary-length prefix.
-/

namespace Purelib.Data.CCL.Transducer.Initial.Observation

open Purelib.Data.ComplexContinuedFraction.Encoding in
set_option genInjectivity false in
/-- Distinguish the initial low-entry, unary and selected-sector observations. -/
inductive Decision where
  /-- The initial center selects the low-normalization entry. -/ | low
  /-- The initial center selects the high unary step. -/ | unary
  /-- Retain the exact sector selected by the initial center. -/ | sector (sector :
    Data.ComplexContinuedFraction.Encoding.Sector)

constructive_injectivity Decision

namespace Decision

open Purelib.Data.CCL.Transducer
/-- Read the exact initial chunk selected by the retained observation. -/
def bits : Decision → List Bool
  | .low => [false, true]
  | .unary => [true]
  | .sector sectorValue => false :: false :: sectorValue.code

/-- Read the first bit of the exact chunk selected by the retained observation. -/
def firstBit : Decision → Bool
  | .low => false
  | .unary => true
  | .sector _ => false

end Decision

open Purelib.Data.CCL.Transducer in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
/-- Classify the exact center squared norm into low, selected-sector or unary initial emission.

Below one selects low entry; the closed one-to-13/6 band selects the center's exact sector. A value above 13/6 selects
unary emission. -/
def classify (center : Basic.Canonical) :
  Decision :=
  if 1 ≤ Data.Gaussian.Norm.Basic.normSq center then
    if Data.Gaussian.Norm.Basic.normSq center ≤ 13 / 6 then .sector
      (Data.ComplexContinuedFraction.Encoding.Sector.select center)
    else .unary
  else .low

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
/-- Classifying the exact initial-refined center gives the same bits as the certified initial emission. -/
theorem classify_bits (process : Approximation.Gaussian.Process)
    (state :
  process.State) :
    (classify (process.ball (Emission.Initial.Preparation.initialRefinedState process
      state)).center).bits =
      (Emission.Initial.initialStep ⟨process, state⟩).bits := by
  unfold classify Emission.Initial.initialStep
  by_cases normalized : 1 ≤ Data.Gaussian.Norm.Basic.normSq (process.ball
    (Emission.Initial.Preparation.initialRefinedState
    process state)).center
  · rw [if_pos normalized, dif_pos normalized]
    unfold Enclosure.Sector.Decision.decide
    by_cases upper : Data.Gaussian.Norm.Basic.normSq (process.ball (Emission.Initial.Preparation.initialRefinedState
      process
      state)).center ≤ 13 / 6
    · rw [if_pos upper, dif_pos upper]
      rfl
    · rw [if_neg upper, dif_neg upper]
      rfl
  · rw [if_neg normalized, dif_neg normalized]
    rfl

/-- Read a finite word's first bit, returning false for the empty word. -/
private def first (bits : List Bool) : Bool :=
  match bits with
  | [] => false
  | bit :: _ => bit

section
open Purelib.Data.CCL.Transducer
/-- The returned bit of a certified nonempty emission is exactly the first bit of its retained word. -/
private theorem consume_first (emitted : List Bool) (emission :
  Data.CCL.Transducer.Emission) :
    (Machine.Step.consumeEmission emitted emission).1 = first emission.bits := by
  cases emission with
  | mk bits nonempty next =>
      cases bits with
      | nil => exact (nonempty rfl).elim
      | cons bit tail => rfl

/-- Reading an observation's chunk head gives its retained first-bit observation. -/
private theorem first_bits (decision :
  Decision) : first decision.bits = decision.firstBit := by
  cases decision <;> rfl

end

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
/-- One initial machine advance emits exactly the first bit classified from the same retained refined center. -/
theorem advance_one (process : Approximation.Gaussian.Process)
    (state :
  process.State) :
    (Machine.Advance.advance (Data.CCL.Transducer.Machine.initial process state) 1).emitted =
      [(classify (process.ball (Emission.Initial.Preparation.initialRefinedState process
        state)).center).firstBit] := by
  change (Machine.Step.consumeEmission [] (Emission.Initial.initialStep ⟨process, state⟩)).2.emitted = _
  rw [Machine.Step.consumeEmission_emitted, consume_first, ← classify_bits,
    first_bits]
  rfl

open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A center with squared norm strictly above 13/6 is classified as unary. -/
theorem classify_large {center : Basic.Canonical} (large : (13 /
  6 : Fraction.Rational) < Data.Gaussian.Norm.Basic.normSq center) :
    classify center = .unary := by
  have normalized : (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq center :=
    (show (1 : Fraction.Rational) ≤ 13 / 6 from by decide).trans large.le
  rw [classify, if_pos normalized, if_neg (not_le_of_gt large)]

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- An initial-refined center above squared norm 13/6 makes one machine advance emit exactly true. -/
theorem advance_one_large (process :
    Approximation.Gaussian.Process)
  (state : process.State)
    (large : (13 / 6 : Fraction.Rational) < Data.Gaussian.Norm.Basic.normSq
      (process.ball (Emission.Initial.Preparation.initialRefinedState process state)).center) :
    (Machine.Advance.advance (Data.CCL.Transducer.Machine.initial process state) 1).emitted = [true] := by
  rw [advance_one, classify_large large]
  rfl

end Purelib.Data.CCL.Transducer.Initial.Observation

end
