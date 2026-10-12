module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Newton.Search.Center.Basic
import Purelib.RootIsolation.Newton.Search.Iteration
public import Purelib.RootIsolation.Newton.Search.Trace
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.Geometry.Rational.Box.Sample.Five
public import Purelib.RootIsolation.Newton.Extraction.Initial.Build
import Purelib.RootIsolation.Newton.Extraction.Initial.Search
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

@[expose] public section

/-!
# Replay of the canonical ordered initial-extraction seeds

Initial isolation tries five fixed seeds, each with the checked six-proposal
search.  This trace retains every failed earlier seed, so a successful later
seed identifies the original extractor's choice, not merely a valid root.
Exhaustion certifies only these finite attempts; the total fallback is not run
by replay and is not claimed to fail.  All dependencies are existing finite
isolation and exact proposal-checking modules.
-/

namespace Purelib.RootIsolation.Isolation.InitialExtractionReplay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound
  : Nat}
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
  (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)

set_option genInjectivity false in
/-- The result and stopping reason of each executed seed remain executable
data; proofs identify the ordered canonical search without regenerating it. -/
inductive Trace : List Gaussian.Basic.Canonical → Option (Refinement current epsilon) → Type where
  /-- The empty remaining seed list yields no accepted refinement. -/ | exhausted : Trace [] none
  /-- The retained first seed attempt returns the displayed accepted refinement. -/ | accepted {seed :
    Gaussian.Basic.Canonical} {rest : List Gaussian.Basic.Canonical}
      (trial : Newton.Search.Trace.Finished elimination current epsilon
        (.canonical elimination) seed)
      (value : Refinement current epsilon) (found : trial.value = some value) :
      Trace (seed :: rest) (some value)
  /-- The retained first seed attempt failed, followed by the actual replay on the original tail. -/ | missed {seed :
    Gaussian.Basic.Canonical} {rest : List Gaussian.Basic.Canonical} {value : Option (Refinement
    current epsilon)}
      (trial : Newton.Search.Trace.Finished elimination current epsilon
        (.canonical elimination) seed)
      (empty : trial.value = none) (tail : Trace rest value) :
      Trace (seed :: rest) value

constructive_injectivity Trace

attribute [local irreducible] Newton.Search.Iteration.search
  Newton.Search.Center.Basic.checkCenter Clearance.Box.Line.Elimination.Provider.AxisClearances.canonical

/-- The original initial search tries the displayed first seed before considering its retained tail. -/
private theorem search_cons (seed : Gaussian.Basic.Canonical) (rest : List Gaussian.Basic.Canonical) :
    Newton.Extraction.Initial.Search.search elimination current epsilon (seed :: rest) =
      match Newton.Search.Iteration.search elimination current epsilon 6 0 seed (.canonical elimination) with
      | some accepted => some accepted
      | none => Newton.Extraction.Initial.Search.search elimination current epsilon rest := rfl

/-- The original initial search returns no accepted refinement on an empty seed list. -/
private theorem search_nil :
    Newton.Extraction.Initial.Search.search elimination current epsilon [] = none := rfl

attribute [local irreducible] Newton.Extraction.Initial.Search.search

/-- The retained finite trace reproduces the original ordered seed search result exactly. -/
theorem Trace.equation {seeds : List Gaussian.Basic.Canonical} {value : Option (Refinement current
  epsilon)}
    (trace : Trace elimination current epsilon seeds value) :
    Newton.Extraction.Initial.Search.search elimination current epsilon seeds = value := by
  induction trace with
  | exhausted => exact search_nil elimination current epsilon
  | accepted trial value found =>
      rw [search_cons, Newton.Search.Trace.Finished.equation _ _ _ _ _ trial, found]
  | missed trial empty tail ih =>
      rw [search_cons, Newton.Search.Trace.Finished.equation _ _ _ _ _ trial, empty]
      exact ih

/-- Count the actual seed attempts retained by the finite replay, stopping at its first success. -/
def Trace.tried {seeds : List Gaussian.Basic.Canonical} {value : Option (Refinement current epsilon)} :
    Trace elimination current epsilon seeds value → Nat
  | .exhausted => 0
  | .accepted _ _ _ => 1
  | .missed _ _ tail => tail.tried + 1

/-- The retained replay attempts no more seeds than its original seed list contains. -/
theorem Trace.tried_le {seeds : List Gaussian.Basic.Canonical} {value : Option (Refinement current
  epsilon)}
    (trace : Trace elimination current epsilon seeds value) : trace.tried ≤ seeds.length := by
  induction trace with
  | exhausted => exact Nat.le_refl 0
  | accepted => exact Nat.succ_le_succ (Nat.zero_le _)
  | missed trial empty tail ih => exact Nat.succ_le_succ ih

/-- An unsuccessful retained replay attempts every original seed exactly once. -/
theorem Trace.tried_eq_of_exhausted {seeds : List Gaussian.Basic.Canonical} {value : Option (Refinement
  current epsilon)}
    (trace : Trace elimination current epsilon seeds value) (empty : value = none) :
    trace.tried = seeds.length := by
  induction trace with
  | exhausted => rfl
  | accepted => cases empty
  | missed trial missed tail ih => exact congrArg Nat.succ (ih empty)

set_option genInjectivity false in
/-- Complete finite result for the coefficient/box-derived seed list. -/
structure Replay where
  /-- The actual accepted refinement or unsuccessful result of the original finite seed search. -/ value : Option
    (Refinement current epsilon)
  /-- The retained ordered attempt trace on the exact canonical seed list for the original box. -/ trace : Trace
    elimination current epsilon (Box.Sample.Five.seeds current.box) value

constructive_injectivity Replay

/-- The retained replay result equals the original search on the canonical five seeds. -/
theorem Replay.equation (replay : Replay elimination current epsilon) :
    Newton.Extraction.Initial.Search.search elimination current epsilon
      (Box.Sample.Five.seeds current.box) = replay.value :=
  replay.trace.equation

/-- The retained initial extraction replay tries at most the original five seeds. -/
theorem Replay.seedBudget (replay : Replay elimination current epsilon) : replay.trace.tried ≤ 5 :=
  replay.trace.tried_le

/-- A retained unsuccessful initial extraction replay has tried all five original seeds. -/
theorem Replay.exhaustedBudget (replay : Replay elimination current epsilon) (empty : replay.value = none) :
    replay.trace.tried = 5 := by
  rcases replay with ⟨value, trace⟩
  cases empty
  exact Trace.tried_eq_of_exhausted elimination current epsilon trace rfl

/-- A successful replay determines the original total extractor, including
its first-success seed ordering.  It never executes the unused fallback. -/
theorem extract_eq (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) (positive : 0 <
      epsilon)
    (replay : Replay elimination current epsilon) (value : Refinement current epsilon)
    (found : replay.value = some value) :
    Newton.Extraction.Initial.Build.extract degreeAtLeastTwo squarefree elimination current positive = value := by
  unfold Newton.Extraction.Initial.Build.extract
  rw [replay.equation, found]

end Purelib.RootIsolation.Isolation.InitialExtractionReplay
