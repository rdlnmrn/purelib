module
import Purelib.Riemann.Paths.PreparedClearPathModels.Execution
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Rat.Fraction.Order.Basic

namespace Test.Riemann.Prepared.PathExecution

open Purelib.Riemann.Paths.PreparedClearPathModels
open Purelib.Polynomial
open Purelib.Data.Rat
open PreparedPath.DyadicBank

variable {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian} {depth : Nat} {diameter : Fraction.Rational}
    {positive : 0 < diameter} {policy : Policy}

/-- Zero budget retains the original unresolved two-segment path without preparing its first head. -/
theorem zero_budget
    (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (last : Geometry.ClearPath.ClearSegment polynomial ambient middle finish)
    (within : (Geometry.ClearPath.cons head (.cons last (.nil finish))).WithinAmbient)
    (owner : Owner (polynomial.eval start)) :
    (executeBounded policy (.cons head (.cons last (.nil finish))) within owner depth diameter positive 0).outcome =
      .inconclusive (.stopped head (.cons last (.nil finish)) within owner (.budget policy)) := rfl

/-- One paid acquisition retains its actual complete head and stops at that head's finish owner before the next
attempt. -/
theorem retains_first_segment
    (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (last : Geometry.ClearPath.ClearSegment polynomial ambient middle finish)
    (within : (Geometry.ClearPath.cons head (.cons last (.nil finish))).WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (first : Segment depth diameter positive head within.head owner)
    (success : executeHead policy head within.head owner depth diameter positive = .inl first) :
    (executeBounded policy (.cons head (.cons last (.nil finish))) within owner depth diameter positive 1).outcome =
      .inconclusive (.prefix head (.cons last (.nil finish)) within owner first
        (.stopped last (.nil finish) within.tail first.prepared.finishOwner (.budget policy))) := by
  simp only [executeBounded, boundedOutcome, success]
  rfl

/-- Resuming a real retained two-segment suspension consumes only the unresolved segment and matches one-shot
execution. -/
theorem resumed_two_segments
    (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
    (last : Geometry.ClearPath.ClearSegment polynomial ambient middle finish)
    (within : (Geometry.ClearPath.cons head (.cons last (.nil finish))).WithinAmbient)
    (owner : Owner (polynomial.eval start))
    (first : Segment depth diameter positive head within.head owner)
    (second : Segment depth diameter positive last within.tail.head first.prepared.finishOwner)
    (firstSuccess : executeHead policy head within.head owner depth diameter positive = .inl first)
    (secondSuccess : executeHead policy last within.tail.head first.prepared.finishOwner depth diameter positive =
      .inl second) :
    ((executeBounded policy (.cons head (.cons last (.nil finish))) within owner depth diameter positive 1).resume
      1).outcome =
      (executeBounded policy (.cons head (.cons last (.nil finish))) within owner depth diameter positive 2).outcome ∧
    ((executeBounded policy (.cons head (.cons last (.nil finish))) within owner depth diameter positive 1).resume
      1).completed = 2 ∧
    ((executeBounded policy (.cons head (.cons last (.nil finish))) within owner depth diameter positive 1).resume
      1).consumed = 2 := by
  have agreement := executeBounded_resume policy depth diameter positive (.cons head (.cons last (.nil finish)))
    within owner 1 1
  refine ⟨agreement, ?_, ?_⟩
  · change ((executeBounded policy (.cons head (.cons last (.nil finish))) within owner depth diameter positive
      1).resume 1).outcome.completed = 2
    rw [agreement]
    simp only [executeBounded, boundedOutcome, firstSuccess, secondSuccess]
    rfl
  · change ((executeBounded policy (.cons head (.cons last (.nil finish))) within owner depth diameter positive
      1).resume 1).outcome.consumed = 2
    rw [agreement]
    simp only [executeBounded, boundedOutcome, firstSuccess, secondSuccess]
    rfl

end Test.Riemann.Prepared.PathExecution
