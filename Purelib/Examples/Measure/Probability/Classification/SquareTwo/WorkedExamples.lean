module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic

import Purelib.Approximation.Bound.Process
import Purelib.Approximation.OneSided.Basic
public import Purelib.Approximation.OneSided.Located
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Classified.Split
import Purelib.Measure.Classified.Soundness
import Purelib.Data.List.Event
import Purelib.Measure.Classified.Distribution
public import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Data.List.Prefix.Cursor
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Elab.Deriving.Repr

@[expose] public section

/-!
# Finite probability for a quadratic inequality

Finite rational grids classify the event `x² < 2`, retaining certified lower
and upper probability bounds. A separate finite gap request turns the
classification into a located bound process.
-/

namespace Purelib.Examples.Measure.Probability.Classification.SquareTwo.WorkedExamples

open Purelib.Measure
open Purelib.Data.Rat
open Purelib.Examples
open Purelib

/-- The five retained rational sample labels of the square-threshold probability law. -/
inductive Sample where
  /-- The sample at negative three halves. -/ | farNegative
  /-- The sample at negative seven fifths. -/ | nearNegative
  /-- The sample at five quarters. -/ | center
  /-- The sample at seven fifths. -/ | nearPositive
  /-- The sample at three halves. -/ | farPositive
deriving DecidableEq

derive_exposed_repr Sample

/-- The original rational values assigned to the five sample labels. -/
def value :
  Sample → Fraction.Rational
  | .farNegative => -3 / 2
  | .nearNegative => -7 / 5
  | .center => 5 / 4
  | .nearPositive => 7 / 5
  | .farPositive => 3 / 2

/-- Whether the retained sample value has square strictly below two. -/
def event (sample :
  Sample) : Bool :=
  decide (value sample ^ 2 < 2)

/-- The certified five-sample law with weights 1/10, 1/5, 2/5, 1/5, 1/10.

Keeps the original sample order and exact nonnegative rational weights whose total is one. -/
def distribution :
  Measure.Distribution Sample where
  atoms :=
    [⟨.farNegative, 1 / 10, by decide⟩,
      ⟨.nearNegative, 1 / 5, by decide⟩,
      ⟨.center, 2 / 5, by decide⟩,
      ⟨.nearPositive, 1 / 5, by decide⟩,
      ⟨.farPositive, 1 / 10, by decide⟩]
  total_one := by decide

/-- The three retained event-classification stages. -/
inductive Stage where
  /-- The initial stage with every sample unresolved. -/ | unresolved
  /-- The stage certifying exactly the event's inside samples. -/ | insideCertified
  /-- The stage resolving every original sample. -/ | complete
deriving DecidableEq

derive_exposed_repr Stage

/-- Advance from unresolved through inside-certified to complete classification. -/
def next :
  Stage →
  Stage
  | .unresolved => .insideCertified
  | .insideCertified => .complete
  | .complete => .complete

/-- The retained sample status at the supplied classification stage.

The intermediate stage certifies inside samples while retaining the others as unresolved; the complete stage resolves
every original sample. -/
def status :
  Stage →
  Sample → Status
  | .unresolved, _ => .unresolved
  | .insideCertified, sample =>
      if event sample then .inside else .unresolved
  | .complete, sample =>
      if event sample then .inside else .outside

/-- The next classification stage refines the current status of each sample. -/
theorem status_next_refines (stage :
  Stage) (sample :
  Sample) :
    (status
      (next stage) sample).Refines
      (status stage sample) := by
  cases stage with
  | unresolved => trivial
  | insideCertified =>
      cases selected : event sample <;>
        (simp only [-eq_self, -iff_self, next,
          status, Status.Refines]
         rewrite [selected]
         trivial)
  | complete =>
      cases selected : event sample <;>
        (simp only [-eq_self, -iff_self, next,
          status, Status.Refines]
         rewrite [selected]
         trivial)

/-- Every retained sample status refines its initial unresolved status. -/
theorem status_refines_unresolved
  (stage : Stage) (sample :
  Sample) :
    (status stage sample).Refines
      (status .unresolved sample) := by
  trivial

/-- The complete status refines each sample's status at every stage. -/
theorem status_complete_refines
  (stage : Stage) (sample :
  Sample) :
    (status .complete sample).Refines
      (status stage sample) := by
  cases stage with
  | unresolved => trivial
  | insideCertified =>
      cases selected : event sample <;>
        (simp only [-eq_self, -iff_self, status,
          Status.Refines]
         rewrite [selected]
         trivial)
  | complete =>
      cases selected : event sample <;>
        (simp only [-eq_self, -iff_self, status,
          Status.Refines]
         rewrite [selected]
         trivial)

/-- Every retained status admits the original square-threshold event outcome. -/
theorem status_sound (stage :
  Stage) (sample :
  Sample) :
    (status stage sample).AdmitsSelection
      (event sample) := by
  cases stage with
  | unresolved => trivial
  | insideCertified =>
      cases selected : event sample <;>
        (simp only [-eq_self, -iff_self, status]
         rewrite [selected]
         trivial)
  | complete =>
      cases selected : event sample <;>
        (simp only [-eq_self, -iff_self, status]
         rewrite [selected]
         trivial)

/-- The classified-event probability interval at the retained stage. -/
def bound (stage :
  Stage) : Data.Rat.Interval :=
  Measure.eventBound (distribution.classifiedEventFrontier
    (status stage))

/-- Advancing classification refines the original probability interval. -/
theorem next_bound_refines (stage :
  Stage) :
    Interval.Refines (bound
      (next stage))
      (bound stage) := by
  apply distribution.classifiedEventFrontier_refines
  intro atom member
  exact status_next_refines stage atom.item

/-- Every retained stage refines the initial probability interval. -/
theorem bound_refines_initial (stage
  : Stage) :
    Interval.Refines (bound stage)
      (bound .unresolved) := by
  apply distribution.classifiedEventFrontier_refines
  intro atom member
  exact status_refines_unresolved stage atom.item

/-- The complete probability interval refines every retained stage interval. -/
theorem complete_bound_refines
  (stage : Stage) :
    Interval.Refines (bound .complete)
      (bound stage) := by
  apply distribution.classifiedEventFrontier_refines
  intro atom member
  exact status_complete_refines stage atom.item

/-- The lower probability process from the original three classification stages. -/
def lower :
  Approximation.LowerProcess :=
  Approximation.LowerProcess.ofBoundRefinement Stage
    bound .unresolved
    next
    next_bound_refines
      bound_refines_initial

/-- The upper probability process from the same retained stages. -/
def upper :
  Approximation.UpperProcess :=
  Approximation.UpperProcess.ofBoundRefinement Stage
    bound .unresolved
    next
    next_bound_refines
      bound_refines_initial

/-- Certified classification of the square-threshold event under the original law.

Every positive accuracy request reaches the complete stage with exactly zero unresolved mass, retaining the original
sample/event identities. -/
def classification :
  Measure.ClassificationProcess distribution
  event where
  State := Stage
  status := status
  initial := .unresolved
  request _ _ _ := .complete
  sound stage atom member := status_sound stage atom.item
  request_refines state epsilon positive atom member :=
    status_complete_refines state atom.item
  accurate state epsilon positive := by
    have noneUnresolved :
        distribution.probability
            (unresolvedStatusEvent (status .complete)) = 0
              := by
      decide
    rw [noneUnresolved]
    exact positive
  refinesInitial stage atom member :=
    status_refines_unresolved stage atom.item

/-- Pair lower and upper readings at the same original classification stage. -/
def observation (stage :
  Stage) : Approximation.PairedObservation
  lower
  upper where
  lowerState := stage
  upperState := stage
  ordered := (bound stage).valid

/-- The located pair of the retained square-threshold probability processes.

Requests reach the original complete stage with zero gap and preserve all initial and intermediate refinement bounds. -/
def located :
  Approximation.LocatedPair lower
  upper where
  State := Stage
  observation := observation
  initial := .unresolved
  request _ _ _ := .complete
  request_refines state epsilon positive := by
    have refines := complete_bound_refines state
    exact ⟨refines.lower, refines.upper⟩
  accurate state epsilon positive := by
    have zeroGap : (observation .complete).gap = 0 := by
      decide
    rw [zeroGap]
    exact positive
  refinesInitial state := by
    have refines := bound_refines_initial state
    exact ⟨refines.lower, refines.upper⟩

/-- Exactly the three middle retained samples have squares below two. -/
theorem event_table :
    event .farNegative = false ∧
      event .nearNegative = true ∧
      event .center = true ∧
      event .nearPositive = true ∧
      event .farPositive = false := by
  decide

/-- The original classification intervals tighten from [0,1] to exact four fifths.

The intermediate interval retains lower endpoint four fifths and upper endpoint one before the outside samples are
resolved. -/
theorem staged_endpoints :
    lower.bound .unresolved = 0 ∧
      upper.bound .unresolved = 1 ∧
      lower.bound .insideCertified = 4 / 5 ∧
      upper.bound .insideCertified = 1 ∧
      lower.bound .complete = 4 / 5 ∧
      upper.bound .complete = 4 / 5 := by
  decide

/-- The original five-sample law assigns the event probability four fifths. -/
theorem exact_probability :
  distribution.probability
  event = 4 / 5 := by
  decide

/-- The intermediate interval contains the actual event probability. -/
theorem
  probability_inside_middle_bound :
    (bound .insideCertified).Contains
      (distribution.probability
      event) :=
  classification.probability_mem_bound .insideCertified

/-- A one-tenth request yields the exact four-fifths probability interval. -/
theorem located_request_exact :
    let process := located.toBoundProcess
    let state := process.request process.initial (1 / 10) (by decide)
    (process.bound state).lower = 4 / 5 ∧
      (process.bound state).upper = 4 / 5 ∧
      (process.bound state).width = 0 := by
  decide

end Purelib.Examples.Measure.Probability.Classification.SquareTwo.WorkedExamples

end
