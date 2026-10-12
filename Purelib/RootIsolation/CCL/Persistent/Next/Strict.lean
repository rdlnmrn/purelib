module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.CCL.Encoding.Parser.Next
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Geometry.CCL.Parser.Formula.Advance
import Purelib.Geometry.CCL.Parser.Formula.Input
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Box.Sign
public import Purelib.Geometry.Projective.Hermitian.Formula.Box.Check
public import Purelib.Geometry.Projective.Hermitian.Formula.Box.Inspection
import Purelib.Geometry.Projective.Hermitian.Formula.Box.Stability
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.CCL.Persistent.Controller.Basic
public import Purelib.RootIsolation.CCL.Persistent.Sample.Extension
import Purelib.RootIsolation.CCL.Persistent.State.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.RootIsolation.CCL.Persistent.Sample.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

public section

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Strict-sign steps for the persistent CCL controller

This module implements the part of the one-bit controller where every atom
of the selected child formula is separated from its Hermitian boundary on the
current box.  The same displayed input remains a compatible sample after the
bit is appended, and formula stability proves this uniformly for every later
supplied winding-one refinement.

Boundary equality is intentionally not guessed here.  `stableNext?` returns
`none` when an atom margin is unresolved; the curve-count/equality-owner layer
must handle precisely those cases.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Next.Strict

set_option genInjectivity false in
/-- All finite evidence needed for a strict-sign one-bit persistent step. -/
structure StableNext
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) where
  /-- The actual next raw bit selected for the original persistent prefix. -/ bit : Bool
  /-- The next-bit formula has a stable truth value throughout the original numerical box. -/ stable :
    Geometry.Projective.Hermitian.Formula.Box.Stable
    ambient current.numerical.box
    (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula
      (Data.CCL.Encoding.Parser.State.parse current.word) bit)
  /-- The original current sample satisfies this exact next-bit formula. -/ currentHolds :
    (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula
    (Data.CCL.Encoding.Parser.State.parse current.word) bit).Holds current.currentSample.point

constructive_injectivity StableNext

/-- Inspect the local sample's finite next-bit decision, then execute every
strict atom-margin comparison for that child formula. -/
@[expose] def stableNext?
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) : Option (StableNext current) :=
  let sample := current.currentSample
  let next := sample.nextDecision
  match next.decision with
  | .terminal _ => none
  | .next bit tailHolds _ =>
      let formula := Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula
        (Data.CCL.Encoding.Parser.State.parse current.word) bit
      match Geometry.Projective.Hermitian.Formula.Box.stable? formula ambient
          current.numerical.box current.numerical.refinesAmbient
          sample.point sample.inside with
      | none => none
      | some stable =>
          some
            { bit := bit
              stable := stable
              currentHolds :=
                CCL.Persistent.Sample.Extension.CompatibleSample.inputIncrementalAdvanceFormula_holds_of_advance
                  sample bit tailHolds }

/-- The displayed current sample is locally terminal. -/
structure LocalTerminal
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) where
  /-- Neither raw bit can extend the original prefix at its displayed current sample. -/ none : ∀ bit,
    ¬Data.CCL.Encoding.Parser.Semantics.Prefix.CanStep
    (Data.CCL.Encoding.Parser.State.parse current.word) current.currentSample.point bit

set_option genInjectivity false in
/-- A nonterminal child whose structural box inspection stopped at one
concrete unresolved Hermitian atom. -/
structure BoundaryNext
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) where
  /-- The actual next bit selected at the original current sample. -/ bit : Bool
  /-- The concrete Hermitian atom left unresolved by the box inspection. -/ atom : Geometry.Projective.Hermitian.Atom
  /-- The unresolved atom belongs to the exact selected next-bit formula. -/ member : atom ∈
    (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula
      (Data.CCL.Encoding.Parser.State.parse current.word) bit).atoms
  /-- The original atom-margin checker returned no certificate on this exact box and sample. -/ failure :
    Geometry.Projective.Hermitian.Box.certificate?
    atom.form ambient current.numerical.box current.numerical.refinesAmbient
      current.currentSample.point current.currentSample.inside = none
  /-- The original displayed sample satisfies the selected next-bit formula. -/ currentHolds :
    (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula
    (Data.CCL.Encoding.Parser.State.parse current.word) bit).Holds current.currentSample.point

constructive_injectivity BoundaryNext

set_option genInjectivity false in
/-- Total structural decomposition of one displayed next-bit decision. -/
inductive NextInspection
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) where
  /-- The original current sample has no possible next bit. -/ | terminal (result :
    LocalTerminal current)
  /-- The exact selected child formula is stable on the original box. -/ | stable (result :
    StableNext current)
  /-- The selected child formula retains a concrete unresolved box atom. -/ | boundary (result :
    BoundaryNext current)

constructive_injectivity NextInspection

/-- Decide the current sample's next bit and retain the first unresolved atom
when the full child formula is not yet box-stable. -/
@[expose] def inspectNext
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) : NextInspection current := by
  let sample := current.currentSample
  let next := sample.nextDecision
  match next.decision with
  | .terminal terminalNone =>
      exact .terminal
        { none := by
            intro bit possible
            apply terminalNone bit
            apply (Geometry.CCL.Parser.Formula.advanceFormula_iff
              (Data.CCL.Encoding.Parser.State.parse current.word) bit next.tail).2
            exact (Data.CCL.Encoding.Parser.Next.canStep_iff_canAdvanceAt
              (Data.CCL.Encoding.Parser.State.parse current.word) sample.point next.tail
              (Data.CCL.Encoding.Parser.State.parse_det_ne current.word)
              next.represents bit).1 possible }
  | .next bit tailHolds _unique =>
      let formula := Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula
        (Data.CCL.Encoding.Parser.State.parse current.word) bit
      have currentHolds : formula.Holds sample.point := by
        exact CCL.Persistent.Sample.Extension.CompatibleSample.inputIncrementalAdvanceFormula_holds_of_advance
          sample bit tailHolds
      match Geometry.Projective.Hermitian.Formula.Box.inspect formula ambient
          current.numerical.box current.numerical.refinesAmbient sample.point
          sample.inside with
      | .stable stable =>
          exact .stable
            { bit := bit
              stable := stable
              currentHolds := currentHolds }
      | .unresolved atom member failure =>
          exact .boundary
            { bit := bit
              atom := atom
              member := by simpa only [formula, -eq_self, -iff_self] using member
              failure := by simpa only [sample, formula, -eq_self, -iff_self] using failure
              currentHolds := by simpa only [sample, formula, -eq_self, -iff_self] using currentHolds }

namespace StableNext

/-- A box-stable child formula extends the persistent sample provider over
all later supplied subboxes. -/
@[expose] def state
    {p : CoefficientPolynomial} {ambient : Box}
    {current : State p ambient} (next : CCL.Persistent.Next.Strict.StableNext current) :
    State p ambient where
  numerical := current.numerical
  word := current.word ++ [next.bit]
  samples :=
    { sample := fun later laterRefines =>
        let prior := current.samples.sample later laterRefines
        have priorInsideCurrent : current.numerical.box.Contains prior.point :=
          laterRefines.contains prior.inside
        have priorHolds :
            (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula
              (Data.CCL.Encoding.Parser.State.parse current.word) next.bit).Holds prior.point :=
          (next.stable.holds_iff current.currentSample.inside
            priorInsideCurrent).1 next.currentHolds
        CCL.Persistent.Sample.Extension.CompatibleSample.extendIncremental prior next.bit priorHolds }

/-- The stable next state appends exactly its retained bit to the original raw prefix. -/
@[simp] theorem state_word
    {p : CoefficientPolynomial} {ambient : Box}
    {current : State p ambient} (next : CCL.Persistent.Next.Strict.StableNext current) :
    next.state.word = current.word ++ [next.bit] := rfl

/-- The stable next state retains the original numerical box. -/
@[simp] theorem state_box
    {p : CoefficientPolynomial} {ambient : Box}
    {current : State p ambient} (next : CCL.Persistent.Next.Strict.StableNext current) :
    next.state.numerical.box = current.numerical.box := rfl

/-- Package the implemented strict-sign case in the abstract controller's
one-step output contract. -/
@[expose] def stepResult
    {p : CoefficientPolynomial} {ambient : Box}
    {current : State p ambient} (next : CCL.Persistent.Next.Strict.StableNext current) :
    CCL.Persistent.Controller.Basic.StepResult current :=
  .next next.bit next.state
    (Box.refines_refl current.numerical.box) rfl

end StableNext

end Purelib.RootIsolation.CCL.Persistent.Next.Strict

/-!
# Finite equality ownership for CCL formula atoms

The parser's weak/strict convention decides every atom exactly at a zero of
its Hermitian form.  This module records that decision as finite data and
lets formula inspection reuse boundaries already proved identically zero.
Consequently a universal boundary is discharged once, and structural
reinspection either proves the complete formula stable or returns a
different unresolved atom.
-/

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

namespace Purelib.RootIsolation.CCL.Persistent.Next.Strict
/-- The original unresolved next-bit certificate for the finite dispatcher's state. -/
abbrev SourcePersistentDispatchBoundaryNextAlias
    {p : CoefficientPolynomial} {ambient : Box} (current :
      State p ambient) :=
  BoundaryNext current
end Purelib.RootIsolation.CCL.Persistent.Next.Strict

end
