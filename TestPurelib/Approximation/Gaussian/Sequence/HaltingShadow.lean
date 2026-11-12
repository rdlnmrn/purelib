module

public import Purelib.Approximation.Gaussian.Sequence.HaltingShadow
public import TestPurelib.Computation.Machine.Halting
import Purelib.Data.Rat.Fraction.Cast

/-! # Total shadow refinement, operational zero and correctly based post-halt apartness -/

namespace TestPurelib.Approximation.Gaussian.Sequence.HaltingShadow

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Sequence.HaltingShadow
open Purelib.Computation
open Purelib.Data.Rat

/-- The explicit loop's shadow has no actual finite halting witness at any bound. -/
public theorem loop_noHalt (input : Machine.Value) :
    ¬ Machine.Halting.Halts (Code.ofProgram Machine.Program.loop input).initial := by
  intro halted
  rcases (Machine.Halting.halts_iff_firstHalt _).mp halted with ⟨bound, stage, observed⟩
  have absent := Machine.Halting.loop_absent input bound
  have impossible := absent.symm.trans observed
  nomatch impossible

/-- The explicit never-returning program's original shadow is operationally equivalent to exact zero. -/
public def loop_zero (input : Machine.Value) :
    Equivalence.NamedEquivalent (Code.ofProgram Machine.Program.loop input).named.name
      (Name.Basic.Named.exact 0) :=
  (Code.ofProgram Machine.Program.loop input).zero_of_noHalt (loop_noHalt input)

/-- Observe an actual first halt and check the same reached process's retained positive candidate bound. -/
private def checkApart (code : Code) (bound : Nat) : IO Unit := do
  match observed : code.firstHalt bound with
  | none => throw (IO.userError "shadow fixture did not observe its expected finite halt")
  | some stage =>
      let reached := code.apart_of_observed observed
      let state : Nat := reached.state
      unless bound ≤ state && decide (reached.apart.lowerSq = radiusSq stage) &&
          decide (0 < reached.apart.lowerSq) do
        throw (IO.userError "shadow apartness lost its actual reached state or positive retained bound")
      for later in [state, state + 1, state + 5] do
        unless decide (code.sample later = point stage) &&
            decide (reached.apart.lowerSq ≤ Data.Gaussian.Norm.Basic.normSq (code.sample later)) do
          throw (IO.userError "shadow reached-state candidates changed their constant post-halt tail")

/-- Run stage-zero, delayed and never-halting shadows and verify actual positive refinement requests. -/
public def run : IO Unit := do
  let initial := Code.ofProgram [] (.number 7)
  let delayed := Code.ofProgram [.tick, .tick, .halt] (.number 7)
  let never := Code.ofProgram Machine.Program.loop (.number 7)
  unless decide (initial.sample 0 = point 0) && decide (delayed.sample 0 = 0) &&
      decide (delayed.sample 2 = 0) && decide (delayed.sample 3 = point 3) &&
      decide (delayed.sample 8 = point 3) && decide (never.sample 100 = 0) do
    throw (IO.userError "shadow samples changed the original first-halt or stage-zero convention")
  checkApart initial 0
  checkApart delayed 3
  let target : Fraction.Rational := 1 / Fraction.Cast.fromInt 256
  for code in [initial, delayed, never] do
    let index := code.approximation.refineIndex 1 target (by decide)
    unless 1 ≤ index && decide (radiusSq index < target) do
      throw (IO.userError "shadow failed total monotone refinement of its actual positive target")
    for earlier in [0, 1, 2, 3, 5] do
      for later in [earlier, earlier + 1, earlier + 5] do
        unless decide (Data.Gaussian.Norm.Basic.normSq (code.sample later - code.sample earlier) ≤ radiusSq earlier) do
          throw (IO.userError "shadow violated its original later-close allowance")
  let comparison := (loop_zero (.number 7)).compare 0 0 target (by decide)
  unless decide (Data.Gaussian.Norm.Basic.normSq
      ((Name.Sampling.approximation never.named.name).sample comparison.leftIndex -
        (Name.Sampling.approximation (Name.Basic.Named.exact 0)).sample comparison.rightIndex) < target) do
    throw (IO.userError "never-halting shadow failed its retained operational comparison with exact zero")
  IO.print ("halting shadows: stage zero, delayed and never-halt samples, " ++
    "total refinement and reached apartness passed\n")

end TestPurelib.Approximation.Gaussian.Sequence.HaltingShadow
