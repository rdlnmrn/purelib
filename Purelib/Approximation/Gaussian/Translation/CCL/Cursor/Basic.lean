module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.CCL.Semantics
public import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Representation.Basic
public import Purelib.Approximation.Gaussian.Representation.Sequence
public import Purelib.Approximation.Gaussian.Translation.Observation
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Translation.Schedule
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.Deriving.Repr

open Purelib.Approximation.Gaussian.Name.Basic (Named)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Representation

open Purelib.Approximation.Gaussian.Representation.Basic

open Purelib.Approximation.Gaussian.Sequence

open Purelib.Approximation.Gaussian.Translation

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.Nat
open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite translations through a progressive CCL cursor

A finite CCL observation contains two synchronized interfaces to one named
program: a persistent raw prefix of an explicitly requested length and a
finite rational sample/error observation.  The prefix has exact projective
machine semantics; the sidecar supplies the rational precision gauge used for
cross-representation comparison.
-/

namespace Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Basic

set_option genInjectivity false in
/-- One finite raw prefix together with one finite quantitative observation of the same progressive CCL name. -/
structure CursorObservation (name :
  Named) where
  /-- The index of the retained finite quantitative approximation observation. -/ sampleIndex : Nat
  /-- The number of visible raw CCL bits requested from the original name. -/ bitCount : Nat
deriving DecidableEq

constructive_injectivity CursorObservation

derive_exposed_repr CursorObservation

namespace CursorObservation

/-- Read the original name as its finite sampled approximation without changing the process owner. -/
def approximation (name :
  Named) : ApproximationData :=
  Sampling.approximation name

/-- The raw word emitted by advancing the original name's cursor by the retained bit count. -/
def word {name :
  Named} (observation : Approximation.Gaussian.Translation.CCL.Cursor.Basic.CursorObservation name)
  : List Bool :=
  (Advance.advance name.machine
    observation.bitCount).emitted

/-- The retained raw word has exactly the requested finite bit count. -/
theorem word_length {name :
  Named} (observation : Approximation.Gaussian.Translation.CCL.Cursor.Basic.CursorObservation name)
  :
    observation.word.length = observation.bitCount :=
  (name.productive observation.bitCount).2

/-- Increasing the retained bit count extends the earlier word from the same original name. -/
theorem
  word_isPrefix_of_bitCount_le
  {name : Named}
    {earlier later : Approximation.Gaussian.Translation.CCL.Cursor.Basic.CursorObservation name}
    (order : earlier.bitCount ≤ later.bitCount) :
    earlier.word.IsPrefix later.word := by
  let extra := later.bitCount - earlier.bitCount
  have identity : later.bitCount = earlier.bitCount + extra :=
    (Subtraction.add_sub_of_le order).symm
  change
    (Advance.advance name.machine
      earlier.bitCount).emitted.IsPrefix
      (Advance.advance name.machine
        later.bitCount).emitted
  rw [identity, ← Advance.advance_add]
  exact Advance.advance_extends
    (Advance.advance name.machine earlier.bitCount) extra

/-- The whole internally committed parser chunk has exact projective semantics after every finite exposed-prefix
request. -/
theorem exactCursor {name :
  Named} (observation : Approximation.Gaussian.Translation.CCL.Cursor.Basic.CursorObservation name)
  :
    Semantics.Basic.ExactCursor name.process name.state
      (Advance.advance name.machine observation.bitCount) :=
  CCL.Semantics.Named.advance_exact name
    observation.bitCount

end CursorObservation

/-- Finite CCL cursor observations. Refinement simultaneously advances the quantitative sample index and preserves the
raw prefix. -/
def cursorRepresentation (name :
  Named) : Approximation.Gaussian.Representation where
  Observation := CursorObservation name
  Possible observation value :=
    (CursorObservation.approximation name).Possible
      observation.sampleIndex value
  witness observation :=
    (CursorObservation.approximation name).sample
      observation.sampleIndex
  witness_possible observation :=
    (CursorObservation.approximation name).sample_possible
      observation.sampleIndex
  Refines inner outer :=
    outer.sampleIndex ≤ inner.sampleIndex ∧
      outer.bitCount ≤ inner.bitCount
  refines_refl _ := ⟨Nat.le_refl _, Nat.le_refl _⟩
  refines_trans innerMiddle middleOuter :=
    ⟨middleOuter.1.trans innerMiddle.1,
      middleOuter.2.trans innerMiddle.2⟩
  possible_persists refines possible :=
    (CursorObservation.approximation name).possible_persists
      refines.1 possible
  precisionSq observation :=
    (CursorObservation.approximation name).radiusSq
      observation.sampleIndex
  precisionSq_nonneg observation :=
    (CursorObservation.approximation name).radiusSq_nonneg
      observation.sampleIndex
  boundary := .projective

/-- Forgetting the persistent raw-prefix counter recovers the ordinary finite approximation observation with no
precision loss. -/
def cursorToApproximation (name :
  Named) :
    Observation.ObservationMap (cursorRepresentation name)
      (Sequence.approximationRepresentation
        (CursorObservation.approximation name)) where
  map observation := observation.sampleIndex
  covers possible := possible
  coherent refines :=
    Approximation.Gaussian.Representation.compatible_of_refines refines.1
  precisionLoss _ := 0
  precisionLoss_nonneg _ := le_rfl
  precision_le _ := by
    simp only [cursorRepresentation,
      Sequence.approximationRepresentation, -eq_self, -iff_self]
    rewrite [Fraction.Field.add_comm _ 0, Fraction.Field.zero_add]
    exact Fraction.Order.Basic.le_refl _
  schedule _ :=
    { sourceRefinements := 0
      emittedUnits := 0
      arithmeticSteps := 1 }
  costBound _ := 1
  cost_le _ := Nat.le_refl 1
end Purelib.Approximation.Gaussian.Translation.CCL.Cursor.Basic

end
