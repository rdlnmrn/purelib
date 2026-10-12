module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.RootIsolation.Track.Newton.Refinement

import Purelib.RootIsolation.Track.Newton.Canonical
import Purelib.Riemann.RootContinuation.RootReturnBox
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation.Uniqueness
import Purelib.RootIsolation.Newton.Search.Execution.Uniqueness
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Riemann.Paths.PreparedClearPathModels.Execution

@[expose] public section

namespace Purelib.Examples.Riemann.RootContinuation.RootRegions

open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Paths

open Purelib.RootIsolation.Track

open Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat.Fraction (Rational)

/-! The small rectangle is the fixture used by the line-clearance regressions.
The enclosing-box construction is exact geometry, and does not isolate a root.
The following refinement example instead consumes an existing winding-one
state and its original polynomial certificates. No preparation is rerun to
establish owner identity. -/
/-- The rational fixture rectangle [-2,2]×[-1,1]. -/
private def rectangle : Box where
  xLower := -2
  xUpper := 2
  yLower := -1
  yUpper := 1
  x_valid := by decide
  y_valid := by decide

/-- The displayed proper rectangle lies strictly inside its computed common enclosing box. -/
example : rectangle.StrictInterior
    (RootReturnBox.enclosure rectangle rectangle (by
      change (-2 : Rational) < 2 ∧ (-1 : Rational) < 1
      exact ⟨by decide, by decide⟩)) :=
  RootReturnBox.first_strict rectangle rectangle (by
      change (-2 : Rational) < 2 ∧ (-1 : Rational) < 1
      exact ⟨by decide, by decide⟩)

/-- The track built from a supplied winding-one state refines through the original canonical Newton refinement. -/
example {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Box} {degreeBound : Nat}
    (degree : 2 ≤ p.natDegree) (squarefree :
      Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p
      degreeBound)
    (state : RootIsolation.State.WindingOne.Basic.WindingOneState p ambient) (epsilon :
      Rational) (positive : 0 < epsilon) :
    (Newton.Build.ofInitial degree squarefree elimination state).refine state epsilon
      positive =
      Newton.Refinement.refineState degree squarefree elimination state epsilon positive :=
  (Newton.Canonical.initial
    degree squarefree elimination state) state epsilon positive

/-! A failed enclosing-box attempt retains two supplied owners, its actual
box, every preceding passed guard and a finite winding budget. Reading that
report establishes this attempt's outcome and query bound; it makes no claim
that the roots differ or that another finite attempt cannot succeed. -/
/-- An inconclusive enclosing-box observation reads back the actual failed check and its retained finite winding-query
budget. -/
example {parameter : Purelib.Data.Gaussian.Basic.Canonical}
    {first last : RootReturnBox.Owner parameter}
    (observation : RootReturnBox.Observation first last)
    (report : RootReturnBox.Inconclusive first last)
    (stopped : observation.outcome = .error report) :
    RootReturnBox.check first last = .error report ∧
      report.reason.windingQueries ≤ report.windingBudget :=
  ⟨observation.inconclusive_readback report stopped, report.queries_le_budget⟩

/-! Checked preparation retains its finite Newton execution and first failed
final guard. Its optional accepted result still obeys the original search and
diameter, predicted-clearance and ambient check order. -/

section
open Purelib.Polynomial.Geometry

/-- One checked construction retains its bounded warm-up and search, with the original optional guard specification. -/
example {polynomial : CheckedSquareRootPreparation.GaussianPolynomial}
    {ambient : CheckedSquareRootPreparation.Box} {start finish : CheckedSquareRootPreparation.Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : CheckedSquareRootPreparation.Coordinate)
    (owner : CheckedSquareRootPreparation.Owner (polynomial.eval (segment.pointAt parameter)))
    (diameter : CheckedSquareRootPreparation.Coordinate) :
    let report := CheckedSquareRootPreparation.attempt segment parameter owner diameter
    report.warmup.steps.length ≤ 2 ∧ report.search.steps.length ≤ 6 ∧ report.value =
      match CheckedSquareRootPreparation.searchValue segment parameter owner diameter with
      | none => none
      | some accepted => CheckedSquareRootPreparation.acceptedValue segment parameter owner diameter accepted :=
  ⟨(CheckedSquareRootPreparation.attempt segment parameter owner diameter).warmup.execution.length_le,
    (CheckedSquareRootPreparation.attempt segment parameter owner diameter).search.execution.length_le,
    CheckedSquareRootPreparation.attempt_value_eq segment parameter owner diameter⟩

end

section PathExecution

open Purelib.Polynomial
open Purelib.Riemann.Paths.PreparedClearPathModels
open PreparedPath.DyadicBank

/-- Prepare a finite path in two allowances while retaining its original owner and exact one-shot prepared value.

The initial report keeps successful segments and any current unresolved head. Continuing consumes only the saved suffix;
when the allowances cover the original finite segment count, all four execution policies agree with their original
prepared-data specification. Failed mathematical guards remain typed finite inconclusive results. -/
example {polynomial : GaussianPolynomial} {ambient : PreparedClearPathModels.Box} {start finish : Gaussian}
    (policy : Policy) (path : Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) (owner : Owner (polynomial.eval start))
    (depth : Nat) (diameter : Rational) (positive : 0 < diameter)
    (initialBudget extraBudget : Nat) (completeBudget : initialBudget + extraBudget = path.segmentCount) :
    let initial := executeBounded policy path within owner depth diameter positive initialBudget
    let continued := initial.resume extraBudget
    continued.budget = initialBudget + extraBudget ∧
      continued.outcome.prepared? = originalPrepared policy path within owner depth diameter positive := by
  constructor
  · exact Execution.resume_budget _ extraBudget
  · rw [executeBounded_resume, completeBudget]
    exact executeBounded_originalPrepared policy depth diameter positive path within owner

end PathExecution

end Purelib.Examples.Riemann.RootContinuation.RootRegions
