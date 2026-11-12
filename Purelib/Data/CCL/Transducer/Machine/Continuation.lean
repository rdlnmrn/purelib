module

public import Purelib.Data.CCL.Transducer.Mode.Exact
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
public import Purelib.Data.CCL.Progressive.Cursor.Image
public import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Committed
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Line.Matrix.Gaussian

/-!
# Exact continuation of a retained productive cursor

The constructor replaces the quantitative mode at a selected possible
rational tail and retains the exact emitted prefix and pending queue. Its
parser phase, committed word and projective image remain those of the
original cursor at that reading. Productive residual padding keeps its
original homogeneous interpretation.
-/

public section

namespace Purelib.Data.CCL.Transducer.Machine.Continuation

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Progressive
open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
open Purelib.Geometry.Projective

set_option genInjectivity false in
/-- Retain the original cursor's exact mode realization and its cached replacement machine. -/
structure Result (original : Machine) where
  /-- The selected original possible tail and its exact counterpart with unchanged phase and bounds. -/ realization :
    Mode.Exact.Realization original.mode
  /-- The replacement machine computed once from that same retained realization and original words. -/ machine : Machine
  /-- The replacement uses this exact retained mode realization. -/ modeEq : machine.mode = realization.mode
  /-- The exact earlier emitted prefix is retained. -/ emittedEq : machine.emitted = original.emitted
  /-- The original pending queue is retained in its actual order. -/ pendingEq : machine.pending = original.pending

/-- Construct a cached productive cursor counterpart from a realization of its original mode. -/
def ofRealization (original : Machine) (realization : Mode.Exact.Realization original.mode) : Result original :=
  let machine : Machine := ⟨realization.mode, original.emitted, original.pending⟩
  ⟨realization, machine, rfl, rfl, rfl⟩

/-- Construct the productive cursor counterpart using its original mode's actual possible witness once. -/
def ofMachine (original : Machine) : Result original :=
  ofRealization original (Mode.Exact.ofMode original.mode)

/-- The cached builder retains the original supplied realization record exactly. -/
private theorem ofRealization_specification (original : Machine)
    (realization : Mode.Exact.Realization original.mode) :
    (ofRealization original realization).realization = realization := rfl

/-- The cached cursor constructor consumes the exact supplied mode realization. -/
theorem ofRealization_realization (original : Machine) (realization : Mode.Exact.Realization original.mode) :
    (ofRealization original realization).realization = realization :=
  ofRealization_specification original realization

namespace Result

/-- The replacement retains the exact full committed word, including its original pending bits. -/
theorem committedEq {original : Machine} (result : Result original) :
    Machine.committed result.machine = Machine.committed original :=
  congrArg₂ List.append result.emittedEq result.pendingEq

/-- The replacement retains the original committed parser phase certificate. -/
theorem grammar {original : Machine} (result : Result original) (originalGrammar : Machine.Grammar.Invariant original) :
    Machine.Grammar.Invariant result.machine := by
  change (Parser.State.parse (Machine.committed result.machine)).phase =
    Mode.Grammar.modeRawPhase result.machine.mode
  rewrite [result.committedEq, result.modeEq, result.realization.phaseEq]
  exact originalGrammar

/-- The selected exact replacement tail has the same complete projective cursor image as the original reading. -/
theorem imageEq {original : Machine} (result : Result original) :
    Cursor.Image.Machine.image result.machine result.realization.value =
      Cursor.Image.Machine.image original result.realization.value := by
  unfold Cursor.Image.Machine.image
  rewrite [result.committedEq, result.modeEq, result.realization.tailEq]
  rfl

/-- The replacement preserves an original exact cursor certificate with the same process and dependent origin state. -/
theorem exactCursor {original : Machine} (result : Result original)
    {origin : Process} {originState : origin.State}
    (cursor : Machine.Semantics.Basic.ExactCursor origin originState original) :
    Machine.Semantics.Basic.ExactCursor origin originState result.machine where
  grammar := result.grammar cursor.grammar
  exact := by
    intro candidate possible
    rewrite [result.modeEq] at possible
    have equal := (result.realization.possibleEq candidate).mp possible
    cases equal
    rcases cursor.exact result.realization.possible with ⟨value, originalPossible, represented⟩
    refine ⟨value, originalPossible, ?_⟩
    change (Cursor.Image.Machine.image result.machine result.realization.value).Equivalent _
    exact result.imageEq.symm ▸ represented

set_option genInjectivity false in
/-- A selected rational cursor image with proved affine denominator and the same fixed future reading.

The cached homogeneous image is computed from the original committed parser
and selected mode tail. Its explicit quotient is proved possible at the
original source state. The replacement cursor's exact origin is the singleton
process at that same quotient, so future cursor advances retain one reading.
-/
structure Reading {original : Machine} (result : Result original) (origin : Process) (originState : origin.State) where
  /-- The original cursor certificate belonging to the same source state. -/ originalCursor :
    Machine.Semantics.Basic.ExactCursor origin originState original
  /-- The cached complete homogeneous image of the selected original tail. -/ image : Line.GaussianLine
  /-- The cached image is this exact original cursor image. -/ imageEq :
    image = Cursor.Image.Machine.image original result.realization.value
  /-- The cached homogeneous pair has a nonzero coordinate. -/ imageValid :
    Line.Gaussian.Proj.HasNonzeroCoordinate image
  /-- This Gaussian-source image is affine; its actual denominator is nonzero. -/ denominatorNonzero : image.q ≠ 0
  /-- The exact Gaussian rational quotient computed from the cached image. -/ value : Basic.Canonical
  /-- The cached rational reading is the explicit quotient of that same image. -/ valueEq :
    value = Line.Gaussian.Proj.affineReading image
  /-- The computed rational reading was possible at the original dependent source state. -/ originalPossible :
    origin.Possible originState value
  /-- The cached homogeneous image represents the same rational reading. -/ represented :
    image.Equivalent (Line.Proj.affine value)
  /-- Every replacement cursor tail represents this same fixed exact rational origin. -/ exactCursor :
    Machine.Semantics.Basic.ExactCursor (Process.exact value) () result.machine

/-- Compute the affine rational reading of a retained Gaussian-source cursor by explicit algebra.

The image and quotient are executable finite algebra. The original cursor's
existential semantic law is used only to prove denominator nonvanishing and
correctness of that computed quotient. The selected exact mode and both
original words are reused; no source refinement or bit emission is rerun.
-/
def read {original : Machine} (result : Result original) {origin : Process} {originState : origin.State}
    (cursor : Machine.Semantics.Basic.ExactCursor origin originState original) : Reading result origin originState := by
  let image := Cursor.Image.Machine.image original result.realization.value
  have imageValid : Line.Gaussian.Proj.HasNonzeroCoordinate image :=
    Line.Matrix.Gaussian.Mat2.act_hasNonzeroCoordinate
      (Parser.State.parse_det_ne (Machine.committed original))
      (Mode.Semantics.SemanticMode.parserTail_valid original.mode result.realization.value)
  have affine : ∃ value : Basic.Canonical,
      origin.Possible originState value ∧ image.Equivalent (Line.Proj.affine value) :=
    cursor.exact result.realization.possible
  have denominatorNonzero : image.q ≠ 0 := by
    rcases affine with ⟨value, _possible, equivalent⟩
    exact Line.Gaussian.Proj.denominator_ne_zero_of_equivalent_affine imageValid equivalent
  let value := Line.Gaussian.Proj.affineReading image
  have originalPossible : origin.Possible originState value := by
    rcases affine with ⟨previous, possible, equivalent⟩
    have equal : value = previous :=
      Line.Gaussian.Proj.affineReading_eq_of_equivalent denominatorNonzero equivalent
    exact equal.symm ▸ possible
  have represented : image.Equivalent (Line.Proj.affine value) :=
    Line.Gaussian.Proj.equivalent_affineReading image denominatorNonzero
  have exactCursor : Machine.Semantics.Basic.ExactCursor (Process.exact value) () result.machine :=
    { grammar := result.grammar cursor.grammar
      exact := by
        intro candidate possible
        rewrite [result.modeEq] at possible
        have equal := (result.realization.possibleEq candidate).mp possible
        cases equal
        refine ⟨value, rfl, ?_⟩
        change (Cursor.Image.Machine.image result.machine result.realization.value).Equivalent (Line.Proj.affine value)
        exact result.imageEq.symm ▸ represented }
  exact ⟨cursor, image, rfl, imageValid, denominatorNonzero, value, rfl, originalPossible, represented, exactCursor⟩

end Result

end Purelib.Data.CCL.Transducer.Machine.Continuation

end
