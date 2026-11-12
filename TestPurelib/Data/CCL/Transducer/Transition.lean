module

import Purelib.Data.CCL.Transducer.Machine.Transition
import Purelib.Data.CCL.Progressive.Cursor.Refinement
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.CCL.Transducer.Machine.Grammar.Step
import Purelib.Data.Rat.Fraction.Cast

/-! # Cached chronological cursor transport boundaries -/

namespace TestPurelib.Data.CCL.Transducer.Transition

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.CCL.Progressive
open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Projective

/-- The actual computed bit-step predecessor is possible at the original mode for every retained frame and tail. -/
theorem predecessor_possible {machine : Machine} (frame : Cursor.Image.Machine.Frame machine)
    (grammar : Machine.Grammar.Invariant machine) (tail : Basic.Canonical)
    (possible : Mode.Semantics.SemanticMode.possible frame.nextBit.result.2.mode tail) :
    Mode.Semantics.SemanticMode.possible machine.mode
      ((Machine.Transition.ofStep frame.nextBit grammar).pullback tail possible).value :=
  ((Machine.Transition.ofStep frame.nextBit grammar).pullback tail possible).possible

/-- A finite small positive target using the direct denominator-one integer display. -/
private def target : Fraction.Rational := 1 / Fraction.Cast.fromInt 16

/-- Compare exact homogeneous image equivalence by its original scalar cross-products. -/
private def equivalent (left right : Line.GaussianLine) : Bool :=
  decide (left.p * right.q = right.p * left.q)

/-- Traverse actual bit and refinement receipts while retaining each earlier parser and matrix cache. -/
private def walk : Nat → {machine : Machine} →
    (frame : Cursor.Image.Machine.Frame machine) → Machine.Grammar.Invariant machine → IO Unit
  | 0, _, _, _ => pure ()
  | count + 1, machine, frame, grammar => do
      let step := frame.nextBit
      match machine.pending with
      | [] => pure ()
      | _ :: _ =>
          unless decide (step.after.parser = frame.parser) &&
              decide (step.after.normalization = frame.normalization) &&
              decide (step.after.matrix = frame.matrix) && decide (step.after.adjugate = frame.adjugate) do
            throw (IO.userError "queued bit changed an original retained chart cache")
      let refinement := step.after.refine target (by decide)
      unless decide (refinement.after.parser = step.after.parser) &&
          decide (refinement.after.normalization = step.after.normalization) &&
          decide (refinement.after.matrix = step.after.matrix) &&
          decide (refinement.after.adjugate = step.after.adjugate) do
        throw (IO.userError "actual refinement did not retain every original frame cache")
      let selected := Mode.Semantics.SemanticMode.witness refinement.machine.mode
      let first := Machine.Transition.ofStep step grammar
      let second := Machine.Transition.ofRefinement refinement
      let refinedPredecessor := second.pullback selected.val selected.property
      let bitPredecessor := first.pullback refinedPredecessor.value refinedPredecessor.possible
      let combined := (first.compose second).pullback selected.val selected.property
      unless decide (combined.value = bitPredecessor.value) &&
          equivalent combined.image (frame.image combined.value) && decide (combined.pulled.q ≠ 0) do
        throw (IO.userError "computed chronological predecessor changed its rational tail or projective reading")
      unless decide (step.after.parser =
          Parser.State.parse (Machine.committed step.result.2)) do
        throw (IO.userError "incrementally retained parser differed from the original committed-word parser")
      have bitGrammar : Machine.Grammar.Invariant step.result.2 :=
        (congrArg Prod.snd step.resultEq).symm ▸ Machine.Grammar.Step.nextBit_invariant machine grammar
      have nextGrammar : Machine.Grammar.Invariant refinement.machine :=
        refinement.machineEq.symm ▸
          Cursor.Refinement.Machine.refine_grammar step.result.2 target (by decide) bitGrammar
      walk count refinement.after nextGrammar

/-- Execute transports through unary, sector, pending-queue and terminal residual-padding transitions. -/
public def run : IO Unit := do
  let zero := Machine.initial (Process.exact 0) ()
  let one := Machine.initial (Process.exact 1) ()
  let two := Machine.initial (Process.exact 2) ()
  walk 12 (Cursor.Image.Machine.Frame.ofMachine zero) (Machine.Grammar.initial_invariant _ _)
  walk 12 (Cursor.Image.Machine.Frame.ofMachine one) (Machine.Grammar.initial_invariant _ _)
  walk 12 (Cursor.Image.Machine.Frame.ofMachine two) (Machine.Grammar.initial_invariant _ _)
  IO.print "chronological cursor transport: 36 bit/refinement pairs preserved caches and exact predecessors\n"

end TestPurelib.Data.CCL.Transducer.Transition
