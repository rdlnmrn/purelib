module
public import Purelib.System.IO
import Purelib.Data.String.Basic
public import Purelib.Data.List.Control
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Degree
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decision
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Exact.LargeSquare
import Purelib.RootIsolation.FTA.Squarefree.Input
public import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Init.Prelude
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

set_option backward.match.sparseCases false

open scoped Purelib.Data.String Purelib.Data.List

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Squarefree

open Purelib.RootIsolation.Exact

open Purelib.RootIsolation.FTA.Squarefree

public section

/-!
Short-iteration diagnostic for the actual coefficient-first initial isolator.
It imports no CCL or generated period bank.  Squarefreeness is computed from
the coefficients; the production isolator supplies all root boxes.  Runtime
regression checks supplement, and do not replace, its universal Lean proofs.
Run under an explicit SIGKILL timeout and a systemd memory bound.
-/

namespace InitialIsolationHarness

/-- Dense Gaussian polynomials with exact rational coordinates. -/
abbrev Polynomial := Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial

/-- Print and flush one isolation progress message. -/
@[expose] def report (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Evaluate a thunk through IO without inlining its computation boundary. -/
@[noinline, expose] def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

/-- Isolate the supplied squarefree polynomial and check its retained finite root data.

Verify degree, root count, pairwise box separation, positive box dimensions, winding one for each root and zero winding
for every remaining region. -/
@[expose] def run (label : String) (p : Polynomial) : IO Unit := do
  report s!"initial-isolation: {label}; checking raw coefficients"
  let started ← IO.monoMsNow
  if degree : 2 ≤ p.natDegree then
    have nonzero : p.isZero = false := Degree.Global.isZero_false_of_natDegree_pos
      ((show (0 : Nat) < 2 by decide).trans_le degree)
    match Decision.squarefreeOutcome p nonzero with
    | .commonDivisor _ => throw (IO.userError "regression polynomial is not squarefree")
    | .coprime squarefree =>
        let input : Purelib.RootIsolation.FTA.Squarefree.Input p := ⟨squarefree, degree⟩
        report
          s!"initial-isolation: {label}; squarefree coefficients checked in {(← IO.monoMsNow) - started} ms; computing \
            axis eliminants"
        let eliminationStarted ← IO.monoMsNow
        let elimination ← evaluate fun _ => input.elimination
        report
          s!"initial-isolation: {label}; axis eliminants in {(← IO.monoMsNow) - eliminationStarted} ms; \
            degrees=({elimination.vertical.natDegree},{elimination.horizontal.natDegree}); extracting root boxes"
        -- This is exactly `input.isolation`, with its once-computed axis
        -- certificate retained explicitly to expose the diagnostic boundary.
        let result ← evaluate fun _ => LargeSquare.isolateLargeSquare
          input.degreeAtLeastTwo input.squarefree elimination
        let boxes ← evaluate fun _ => result.tracks.map (·.initial.box)
        report s!"initial-isolation: {label}; {boxes.length} boxes in {(← IO.monoMsNow) - started} ms"
        unless boxes.length == p.natDegree do
          throw (IO.userError "incorrect root count")
        unless decide (boxes.Pairwise fun left right => left.Separated right) do
          throw (IO.userError "root boxes are not pairwise separated")
        for box in boxes do
          unless decide (box.xLower < box.xUpper ∧ box.yLower < box.yUpper ∧
              Winding.Box.Basic.quadrupledBoxWinding p box = 4) do
            throw (IO.userError "invalid winding-one root box")
        for region in result.remainder do
          unless Winding.Box.Basic.quadrupledBoxWinding p region.box == 0 do
            throw (IO.userError "nonzero residual winding")
        report s!"initial-isolation: {label}; count, separation, all root windings and remainder checked"
  else throw (IO.userError "regression requires degree at least two")

/-- Select the exact real, negative, complex, cubic or scaled period-cubic regression polynomial. -/
@[expose] def fixture (label : String) : IO Unit :=
  match label with
  | "real" => run label ⟨[1, 0, -2]⟩
  | "negative" => run label ⟨[1, 0, 2]⟩
  | "complex" => run label ⟨[1, 0, ⟨-2, -1⟩]⟩
  | "cubic" => run label ⟨[1, 0, 0, -2]⟩
  -- Exact reduced radicand of the coefficient-first period acceptance run.
  -- Retain the nontrivial scalar; this is not a monic replacement fixture.
  | "period-cubic" => run label ⟨[⟨1/4, 0⟩, 0, 0, ⟨1/4, 0⟩]⟩
  | _ => throw (IO.userError "unknown isolation fixture")

end InitialIsolationHarness

/-- Run one requested root-isolation fixture or the complete finite fixture list. -/
@[expose] def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["all"] =>
      for label in ["real", "negative", "complex", "cubic", "period-cubic"] do
        InitialIsolationHarness.fixture label
  | [label] => InitialIsolationHarness.fixture label
  | _ => throw (IO.userError "usage: initial_isolation_harness all | real | negative | complex | cubic | period-cubic")
