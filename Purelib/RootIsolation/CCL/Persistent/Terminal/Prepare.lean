module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.CCL.Encoding.Parser.Next
import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Encoding.Parser.Syntax
public import Purelib.Data.CCL.Encoding.Parser.Terminal.Candidates
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.CCL.Persistent.Sample.Basic
import Purelib.RootIsolation.CCL.Persistent.State.Basic
public import Purelib.RootIsolation.CCL.Persistent.Terminal.Finite
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix (CanStep)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.CCL.Persistent.Sample.Basic (CompatibleSample)

public section

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Resolving rational terminal samples on a persistent CCL track

Every displayed Gaussian-rational sample has a finite CCL terminal.  Reaching
that terminal while constructing a persistent prefix therefore does not by
itself mean that the polynomial root is rational.  This module makes the
necessary distinction executable: evaluate the polynomial at the displayed
terminal point; return an exact root when it vanishes, otherwise perform one
coefficient-computed winding-one refinement that excludes that point.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Terminal.Prepare

set_option genInjectivity false in
/-- A prepared state has removed every possible local rational terminal.
Consequently every compatible sample in its box admits a next raw bit. -/
structure Prepared
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) where
  /-- The actual refined persistent state used for the next dispatch. -/ state : State p
    ambient
  /-- The prepared box refines the original persistent state's box. -/ boxRefines : state.numerical.box.Refines
    current.numerical.box
  /-- Preparation preserves the exact original retained word. -/ word_eq : state.word = current.word
  /-- Every sample compatible with this prepared state admits the original continuation operation. -/ canContinue :
    ∀ sample : CompatibleSample state.word state.numerical.box,
      ∃ bit, CanStep
        (State.parse state.word) sample.point bit

constructive_injectivity Prepared

set_option genInjectivity false in
/-- Total bounded preparation outcome. -/
inductive Preparation
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) where
  /-- Preparation found an exact zero among the original terminal candidates. -/ | exact (root :
    State.Basic.ExactRootIn p current.numerical.box)
  /-- Preparation retained a same-word refined state on which every compatible sample can continue. -/ | ready (result :
    Prepared current)

constructive_injectivity Preparation

/-- A parser phase other than the terminal sector phase admits every compatible continuation sample. -/
private theorem canContinue_of_no_terminal_phase
    {word : List Bool} {box : Box}
    (sample : CompatibleSample word box)
    (notTerminalPhase : ¬∃ kind exponent first second,
      (State.parse word).phase =
        .sector kind exponent (.two first second)) :
    ∃ bit, CanStep
      (State.parse word) sample.point bit := by
  rcases sample.represented with ⟨before, represents⟩
  let parser := State.parse word
  cases Next.decideLocal parser sample.point before
      (State.parse_det_ne word) represents with
  | next bit possible _ => exact ⟨bit, possible⟩
  | terminal none =>
      have noAdvance : ∀ bit,
          ¬Next.CanAdvanceAt parser bit before := by
        intro bit advance
        exact none bit
          ((Next.canStep_iff_canAdvanceAt parser
            sample.point before (State.parse_det_ne word)
            represents bit).2 advance)
      exact (notTerminalPhase
        (Terminal.phase_eq_sectorTwo_of_no_advance
          parser sample.point before represents noAdvance)).elim

/-- Retain the continuation certificate for every compatible sample outside the terminal sector phase. -/
theorem canContinue_no_terminal_phase_certificate
    {word : List Bool} {box : Box}
    (sample : CompatibleSample word box)
    (notTerminalPhase : ¬∃ kind exponent first second,
      (State.parse word).phase =
        .sector kind exponent (.two first second)) :
    ∃ bit, CanStep
      (State.parse word) sample.point bit := by
  exact canContinue_of_no_terminal_phase sample notTerminalPhase

/-- When both original terminal candidates lie outside the refined box, every compatible sample can continue. -/
private theorem canContinue_of_candidates_outside
    {word : List Bool} {box : Box}
    (sample : CompatibleSample word box)
    (kind : Syntax.BlockKind) (exponent : Nat)
    (first second : Bool)
    (phase : (State.parse word).phase =
      .sector kind exponent (.two first second))
    (leftOutside : ¬box.Contains
      (Terminal.candidateInput
        (State.parse word) kind exponent first second false))
    (rightOutside : ¬box.Contains
      (Terminal.candidateInput
        (State.parse word) kind exponent first second true)) :
    ∃ bit, CanStep
      (State.parse word) sample.point bit := by
  rcases sample.represented with ⟨before, represents⟩
  let parser := State.parse word
  cases Next.decideLocal parser sample.point before
      (State.parse_det_ne word) represents with
  | next bit possible _ => exact ⟨bit, possible⟩
  | terminal none =>
      have noAdvance : ∀ bit,
          ¬Next.CanAdvanceAt parser bit before := by
        intro bit advance
        exact none bit
          ((Next.canStep_iff_canAdvanceAt parser
            sample.point before (State.parse_det_ne word)
            represents bit).2 advance)
      rcases
          Terminal.input_eq_candidate_of_sectorTwo_terminal
            parser sample.point before kind exponent first second phase
            represents noAdvance with left | right
      · exact (leftOutside (left ▸ sample.inside)).elim
      · exact (rightOutside (right ▸ sample.inside)).elim

/-- Convert the original two-candidate resolution to a same-word preparation at its exact parser phase.

The supplied resolution retains the actual refined state and both exclusion
certificates. This transport performs no polynomial evaluation or refinement.
-/
@[expose] def ofResolution {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) (kind : Syntax.BlockKind)
    (exponent : Nat) (first second : Bool)
    (phase : (State.parse current.word).phase =
      .sector kind exponent (.two first second)) :
    Finite.PairResolution current
      (Terminal.candidateInput
        (State.parse current.word) kind exponent first second false)
      (Terminal.candidateInput
        (State.parse current.word) kind exponent first second true) → Preparation current
  | .exact root => .exact root
  | .excluded state boxRefines wordEq leftOutside rightOutside =>
      .ready
        { state := state
          boxRefines := boxRefines
          word_eq := wordEq
          canContinue := fun sample => by
            have parserPhase : (State.parse state.word).phase =
                .sector kind exponent (.two first second) := by
              rw [wordEq]
              exact phase
            apply canContinue_of_candidates_outside sample kind exponent first second parserPhase
            · simpa only [wordEq, -eq_self, -iff_self] using leftOutside
            · simpa only [wordEq, -eq_self, -iff_self] using rightOutside }

/-- Prepare one retained parser phase, using its exact equality to the current raw prefix's phase.

Non-sector-two phases require no refinement; sector-two phases inspect the
same two candidates. The equality retains the original prefix owner.
-/
@[expose] def preparePhase
    {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient) (current : State p ambient)
    (selected : Syntax.Phase)
    (phase : (State.parse current.word).phase = selected) :
    Preparation current := by
  let parser := State.parse current.word
  cases selected with
  | initial =>
      exact .ready
        { state := current
          boxRefines := Box.refines_refl _
          word_eq := rfl
          canContinue := fun sample =>
            canContinue_no_terminal_phase_certificate sample (by
              rintro ⟨kind, exponent, first, second, equal⟩
              rw [phase] at equal
              contradiction) }
  | highUnary count =>
      exact .ready
        { state := current
          boxRefines := Box.refines_refl _
          word_eq := rfl
          canContinue := fun sample =>
            canContinue_no_terminal_phase_certificate sample (by
              rintro ⟨kind, exponent, first, second, equal⟩
              rw [phase] at equal
              contradiction) }
  | lowUnary count =>
      exact .ready
        { state := current
          boxRefines := Box.refines_refl _
          word_eq := rfl
          canContinue := fun sample =>
            canContinue_no_terminal_phase_certificate sample (by
              rintro ⟨kind, exponent, first, second, equal⟩
              rw [phase] at equal
              contradiction) }
  | loopUnary count =>
      exact .ready
        { state := current
          boxRefines := Box.refines_refl _
          word_eq := rfl
          canContinue := fun sample =>
            canContinue_no_terminal_phase_certificate sample (by
              rintro ⟨kind, exponent, first, second, equal⟩
              rw [phase] at equal
              contradiction) }
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          exact .ready
            { state := current
              boxRefines := Box.refines_refl _
              word_eq := rfl
              canContinue := fun sample =>
                canContinue_no_terminal_phase_certificate sample (by
                  rintro ⟨otherKind, otherExponent, first, second, equal⟩
                  rw [phase] at equal
                  cases equal) }
      | one first =>
          exact .ready
            { state := current
              boxRefines := Box.refines_refl _
              word_eq := rfl
              canContinue := fun sample =>
                canContinue_no_terminal_phase_certificate sample (by
                  rintro ⟨otherKind, otherExponent, otherFirst, second, equal⟩
                  rw [phase] at equal
                  cases equal) }
      | two first second =>
          let left :=
            Terminal.candidateInput parser kind
              exponent first second false
          let right :=
            Terminal.candidateInput parser kind
              exponent first second true
          exact ofResolution current kind exponent first second phase
            (Finite.resolvePair degreePositive track current left right)

/-- Remove every local rational terminal using the current prefix's original parser phase. -/
@[expose] def prepare {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient) (current : State p ambient) : Preparation current :=
  preparePhase degreePositive track current (State.parse current.word).phase rfl

end Purelib.RootIsolation.CCL.Persistent.Terminal.Prepare

/-!
# Finite dispatch through initial CCL boundary ownership

One persistent controller step first separates the current box from the
single affine pole of its decoder matrix, then removes the bounded set of
rational terminals, and finally inspects the current nonterminal child
formula.  It either executes a box-stable strict-sign/equality-owned step or
retains the first genuinely parameterized Hermitian boundary with its
analysis and a uniform positive decoder-denominator margin.  Universal zero
boundaries are discharged structurally, and finite zero sets are exhausted
by a bounded form-cache loop.  Coupling the remaining curve events to the
persistent sample provider remains.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Terminal.Prepare
/-- The prepared persistent dispatch state with its original source polynomial and retained word. -/
abbrev SourcePersistentDispatchPreparedAlias
    {p : CoefficientPolynomial} {ambient : Box} (current :
      State p ambient) :=
  Prepared current
end Purelib.RootIsolation.CCL.Persistent.Terminal.Prepare

end
