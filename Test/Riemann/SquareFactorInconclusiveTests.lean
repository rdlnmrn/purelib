module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Geometry.PolynomialClearanceDiagnostics
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Cover.Leaf
import Purelib.Polynomial.Dense.Rational.Basic

import Purelib.Integration.Algebraic.SquareFactor.PathInput
public import Purelib.Integration.Algebraic.SquareFactor.ObservationInput
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Pair.Cover.Retained
import Purelib.Polynomial.Clearance.Pair.Enclosure
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Polynomial.Geometry.PolynomialPathDiagnostics

open Purelib.Data.Rat

open Purelib.Integration.Algebraic.SquareFactor

open Purelib.Polynomial.Clearance.Pair.Cover

open Purelib.Polynomial.Dense.Rational.Basic

open Purelib.Polynomial.Geometry

@[expose] public section

/-!
# Kernel checks of the public certified-inconclusivity boundary

These inspect the actual coefficient-first constructor's retained reports.
They do not run numerical observations or stand in for the paused examples.
-/

namespace Test.Riemann.SquareFactorInconclusiveTests

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput (Coordinate)

set_option genInjectivity false in
/-- The exact parameter cell, attempted depth, norm floor and coordinate enclosures of one retained clearance leaf. -/
structure LeafSummary where
  /-- The original unresolved parameter interval's lower endpoint. -/ lower : PathInput.Coordinate
  /-- The original unresolved parameter interval's upper endpoint. -/ upper : PathInput.Coordinate
  /-- The actual subdivision depth retained by this leaf. -/ depth : Nat
  /-- The computed squared-norm lower proposal for this original cell. -/ normFloor : PathInput.Coordinate
  /-- The retained real polynomial enclosure's lower endpoint. -/ realLower : PathInput.Coordinate
  /-- The retained real polynomial enclosure's upper endpoint. -/ realUpper : PathInput.Coordinate
  /-- The retained imaginary polynomial enclosure's lower endpoint. -/ imagLower : PathInput.Coordinate
  /-- The retained imaginary polynomial enclosure's upper endpoint. -/ imagUpper : PathInput.Coordinate
deriving DecidableEq

constructive_injectivity LeafSummary

/-- Read the exact interval, depth and enclosure bounds from the original retained clearance snapshot. -/
public def summarize {realPolynomial imagPolynomial : Purelib.Polynomial.Dense.Rational.Basic.CoordinatePolynomial}
    {source : Leaf.Source realPolynomial imagPolynomial}
    (snapshot : PolynomialClearanceCover.Snapshot source) : LeafSummary :=
  ⟨snapshot.parameters.lower, snapshot.parameters.upper, snapshot.depth, snapshot.data.normFloor,
    snapshot.data.enclosures.realRange.lower, snapshot.data.enclosures.realRange.upper,
    snapshot.data.enclosures.imagRange.lower, snapshot.data.enclosures.imagRange.upper⟩

set_option backward.match.sparseCases false in
/-- Read the exhausted original radicand-clearance budget and every unresolved leaf of the displayed quadratic segment.
-/
public def radicandReport : Option (Nat × List LeafSummary) :=
  match ObservationInput.prepare
      ⟨[1, 0, -2]⟩ (.original 0) ⟨-2, 2⟩ 0 .originalCoordinate with
  | .error (.inconclusive _ _ (.radicand _ (.exhausted _ report _))) =>
      some (report.attempted.budget, report.unresolved.map summarize)
  | _ => none

set_option backward.match.sparseCases false in
/-- Exact failed parameter cells and Horner ranges, not a bare rejection tag or an assertion that these intervals
contain roots. -/
theorem radicand_failure_returns_exact_cells_and_bounds :
    radicandReport = some (8,
      [⟨37/256, 19/128, 8, 0, -65/2048, 63/2048, 0, 0⟩,
        ⟨109/128, 219/256, 8, 0, -65/2048, 63/2048, 0, 0⟩]) := by
  decide +kernel

set_option backward.match.sparseCases false in
/-- Read the exhausted original-coordinate clearance budget and its exact unresolved parameter cells. -/
public def originalCoordinateReport : Option (Nat × List (PathInput.Coordinate × PathInput.Coordinate × Nat)) :=
  match ObservationInput.prepare
      ⟨[1, 0, 1, 0, 0]⟩ (.original 1) ⟨-1, 1⟩ 0 .originalCoordinate with
  | .error (.originalCoordinateUncertified _ _ (.exhausted _ report _)) =>
      some (report.attempted.budget,
        report.unresolved.map fun snapshot => (snapshot.parameters.lower, snapshot.parameters.upper, snapshot.depth))
  | _ => none

set_option backward.match.sparseCases false in
/-- Original-coordinate inconclusivity retains the exact exhausted depth and both unresolved cells around one half. -/
theorem original_coordinate_failure_also_returns_a_certificate :
    originalCoordinateReport = some (8,
      [(127/256, 1/2, 8), (1/2, 129/256, 8)]) := by
  decide +kernel

set_option backward.match.sparseCases false in
/-- Read the exact endpoint obstruction and whether either clearance refinement was performed. -/
public def exactOriginalObstruction : Option (PathInput.Coordinate × Bool × Bool) :=
  match ObservationInput.prepare
      ⟨[1, 0, -2, 0, 0]⟩ (.original 1) ⟨0, 2⟩ 0 .originalCoordinate with
  | .error (.originalCoordinateObstruction _ data endpoint _) =>
      some (endpoint.parameter, data.radicand.clearance.isNone, data.squareFactor.clearance.isNone)
  | _ => none

set_option backward.match.sparseCases false in
/-- A known endpoint failure bypasses both refinement searches, including when the radicand would otherwise require an
inconclusive cover. -/
theorem exact_original_obstruction_skips_refinement :
    exactOriginalObstruction = some (0, true, true) := by
  decide +kernel

/-- The report's proof applies to every reported leaf, not just these fixtures: it was retained by this run, failed its
bound, and reached the cap. -/
theorem every_reported_leaf_is_accounted_for
    {realPolynomial imagPolynomial : Purelib.Polynomial.Dense.Rational.Basic.CoordinatePolynomial}
    {parameters : Purelib.Data.Rat.Interval.Bounds}
    (report : PolynomialClearanceCover.Inconclusive realPolynomial imagPolynomial parameters)
    (snapshot : PolynomialClearanceCover.Snapshot report.attempted.source)
    (member : snapshot ∈ report.unresolved) :
    snapshot ∈ report.leaves ∧ snapshot.data.normFloor ≤ 0 ∧ snapshot.depth = report.attempted.budget :=
  ⟨((report.unresolved_iff snapshot).mp member).1,
    ((report.unresolved_iff snapshot).mp member).2, report.failed_at_budget snapshot member⟩

end Test.Riemann.SquareFactorInconclusiveTests
