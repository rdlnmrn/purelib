module
import Purelib.Data.Gaussian.Norm.Comparison
import Purelib.Data.CCL.Transducer.Replay.Emission
import Purelib.Data.CCL.Transducer.Replay.Mode
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Data.Bounds
import Purelib.Approximation.Gaussian.Process.Recipe.Cursor
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.CCL.Transducer.Mode.Basic
public import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Constants
public import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Gaussian.Process.Normalization.Data
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Norm.Basic

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

namespace Purelib.Data.CCL.Transducer.Replay.Emission.Step

section
open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- Retain a zero-count residual replay cursor translated by the selected sector representative and its exact residual
upper bound. -/
def sectorNext (control :
  CCL.Progressive.IntegrationReplay.Control) (cursor : Approximation.Gaussian.Process.Recipe.Cursor) (ball :
  Enclosure.Ball.Data.BallData)
    (sector : Data.ComplexContinuedFraction.Encoding.Sector) : Data.CCL.Transducer.Replay.Mode :=
  .residual (cursor.translated control sector.rep) 0 (Enclosure.Ball.Data.Bounds.residualUpper sector ball)

section
open Purelib.Data.Gaussian
/-- Retain the supplied regular kind and count at the inverse-gamma-scaled cursor with the ball's exact unary
lower-bound data. -/
def unaryNext (control :
  CCL.Progressive.IntegrationReplay.Control) (cursor : Approximation.Gaussian.Process.Recipe.Cursor) (ball :
  Enclosure.Ball.Data.BallData)
    (kind : Mode.Basic.RegularKind) (count : Nat) : Data.CCL.Transducer.Replay.Mode :=
  .loop kind count (cursor.scaled control Basic.Canonical.gamma⁻¹) (.ofLower (Enclosure.Ball.Data.Bounds.unaryLower
    ball))

/-- Retain the supplied low count at the exact cursor scaled by the first gamma power. -/
def lowNext (control :
  CCL.Progressive.IntegrationReplay.Control) (cursor : Approximation.Gaussian.Process.Recipe.Cursor) (count : Nat) :
      Data.CCL.Transducer.Replay.Mode :=
  .low count (cursor.scaled control (Power.natPow Basic.Canonical.gamma 1))

end

section
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
/-- Select the initial replay chunk from the returned ball's exact center squared norm.

Below one, emit the low-entry pair; in the closed one-to-13/6 band, emit the selected sector chunk. Above that band,
emit one true bit and retain the initial-high unary successor. -/
def initialAfter (control :
  CCL.Progressive.IntegrationReplay.Control) (cursor : Approximation.Gaussian.Process.Recipe.Cursor) (ball :
  Enclosure.Ball.Data.BallData) : Data.CCL.Transducer.Replay.Emission :=
  letI := Basic.Canonical.Norm.Comparison.decidableLENormSq 1 ball.center
  letI := Basic.Canonical.Norm.Comparison.decidableNormSqLE ball.center (13 / 6)
  if 1 ≤ Data.Gaussian.Norm.Basic.normSq ball.center then
    if Data.Gaussian.Norm.Basic.normSq ball.center ≤ 13 / 6 then
      let sector := Data.ComplexContinuedFraction.Encoding.Sector.select ball.center
      ⟨false :: false :: sector.code, sectorNext control cursor ball sector⟩
    else ⟨[true], unaryNext control cursor ball .initialHigh 1⟩
  else ⟨[false, true], lowNext control cursor 1⟩

/-- Select the next low replay chunk or retain a certified center overshoot.

A center below unit squared norm emits a unary bit at the successor count. A normalized center strictly below 13/6 emits
its selected sector; otherwise failure keeps the same cursor and offending ball. -/
def lowAfter (control :
  CCL.Progressive.IntegrationReplay.Control) (count : Nat) (cursor : Approximation.Gaussian.Process.Recipe.Cursor) (ball
      :
  Enclosure.Ball.Data.BallData) :
    Except Data.CCL.Transducer.Replay.Failure Data.CCL.Transducer.Replay.Emission :=
  letI := Basic.Canonical.Norm.Comparison.decidableLENormSq 1 ball.center
  letI := Basic.Canonical.Norm.Comparison.decidableNormSqLT ball.center (13 / 6)
  if 1 ≤ Data.Gaussian.Norm.Basic.normSq ball.center then
    if below : Data.Gaussian.Norm.Basic.normSq ball.center < 13 / 6 then
      let sector := Data.ComplexContinuedFraction.Encoding.Sector.select ball.center
      .ok ⟨false :: sector.code, sectorNext control cursor ball sector⟩
    else .error (.lowOvershoot cursor ball below)
  else .ok ⟨[true], lowNext control cursor (count + 1)⟩

end

open Purelib.Data.Gaussian in
/-- A failed low replay decision retains the same cursor and ball with the violated strict 13/6 center bound. -/
theorem lowAfter_error {control :
  CCL.Progressive.IntegrationReplay.Control} {count : Nat} {cursor : Approximation.Gaussian.Process.Recipe.Cursor} {ball
      :
  Enclosure.Ball.Data.BallData}
    {error : Data.CCL.Transducer.Replay.Failure} (failure : lowAfter control count cursor ball =
      .error error)
      :
    ∃ violated : ¬ Data.Gaussian.Norm.Basic.normSq ball.center < 13 / 6, error = .lowOvershoot cursor ball violated :=
      by
  unfold lowAfter at failure
  split at failure
  · split at failure
    · cases failure
    · rename_i violated
      cases failure
      exact ⟨violated, rfl⟩
  · cases failure

open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
/-- Select the next regular replay chunk or retain a certified normalization failure.

A normalized center in the closed band through 13/6 emits the selected sector; a larger center emits a unary bit at the
successor count. Failure retains the same cursor and ball lacking the unit lower bound. -/
def loopAfter (control :
  CCL.Progressive.IntegrationReplay.Control) (kind : Mode.Basic.RegularKind) (count : Nat) (cursor :
  Approximation.Gaussian.Process.Recipe.Cursor) (ball : Enclosure.Ball.Data.BallData) :
    Except Data.CCL.Transducer.Replay.Failure Data.CCL.Transducer.Replay.Emission :=
  letI := Basic.Canonical.Norm.Comparison.decidableLENormSq 1 ball.center
  letI := Basic.Canonical.Norm.Comparison.decidableNormSqLE ball.center (13 / 6)
  if normalized : 1 ≤ Data.Gaussian.Norm.Basic.normSq ball.center then
    if Data.Gaussian.Norm.Basic.normSq ball.center ≤ 13 / 6 then
      let sector := Data.ComplexContinuedFraction.Encoding.Sector.select ball.center
      .ok ⟨false :: sector.code, sectorNext control cursor ball sector⟩
    else .ok ⟨[true], unaryNext control cursor ball kind (count + 1)⟩
  else .error (.unnormalized cursor ball normalized)

open Purelib.Data.Gaussian in
/-- A failed regular replay decision retains the same cursor and ball with the violated unit center lower bound. -/
theorem loopAfter_error {control :
  CCL.Progressive.IntegrationReplay.Control} {kind : Mode.Basic.RegularKind} {count : Nat} {cursor :
  Approximation.Gaussian.Process.Recipe.Cursor} {ball : Enclosure.Ball.Data.BallData}
    {error : Data.CCL.Transducer.Replay.Failure} (failure : loopAfter control kind count cursor
      ball = .error
      error) :
    ∃ violated : ¬ 1 ≤ Data.Gaussian.Norm.Basic.normSq ball.center, error = .unnormalized cursor ball violated := by
  unfold loopAfter at failure
  split at failure
  · split at failure <;> cases failure
  · rename_i violated
    cases failure
    exact ⟨violated, rfl⟩
end

end Purelib.Data.CCL.Transducer.Replay.Emission.Step

end
