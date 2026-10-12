module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.List.Event
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Rational.Box.Content
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Kernel.Iteration
import Purelib.Measure.Distribution.Markov.Block
import Purelib.Measure.Distribution.Markov.Path.Basic
public import Purelib.Measure.Distribution.Markov.Resampling
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Run
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Run
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness
import Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.BadWindow
public import Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.FiniteDynamics
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.NumberTheory.Approximation.Best.Consecutive.Basic
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Pair
import Purelib.NumberTheory.Approximation.Dirichlet.Window.SourceBound
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
public section

/-!
# Area-calibrated finite dynamical critical regions

The fully robust critical box supplies a positive rational area and turns
every rational source carried inside it into a genuine bad window.  We package
this as a finite state event and give it the explicit rate
`area / (1 + area)`, with the complementary mass assigned to one supplied
background source.  Independent finite resampling is exactly stationary and
therefore yields a geometric path-hit lower bound after any finite burn-in.

This is an area-calibrated two-state rational model, not Haar or Lebesgue
measure and not a discretized minimal-vector transversal.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.BoxDynamics

set_option genInjectivity false in
/-- A critical state carries the proof that its displayed rational source is
inside the fully robust box.  A background state carries no such claim. -/
inductive RobustSourceState
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) where
  /-- A rational source with its retained certificate of membership in the common robust box. -/ | critical (source :
    GaussianInt.Fraction)
      (inside :
        (Dirichlet.Critical.Robust.Run.robustRunBox certificate requestedScale count).Contains
          source.value)
  /-- A retained rational source without a robust-box membership certificate. -/ | background (source :
    GaussianInt.Fraction)

constructive_injectivity RobustSourceState

namespace RobustSourceState

/-- Read the retained rational Gaussian source from either state constructor. -/
@[expose] def source
    {threshold : Fraction.Rational}
    {certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold}
    {requestedScale count : Nat} :
    Dirichlet.Sharpness.BoxDynamics.RobustSourceState certificate requestedScale count → GaussianInt.Fraction
  | .critical value _ => value
  | .background value => value

/-- Select exactly the states carrying a certificate of membership in the robust box. -/
@[expose] def criticalEvent
    {threshold : Fraction.Rational}
    {certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold}
    {requestedScale count : Nat} :
    Dirichlet.Sharpness.BoxDynamics.RobustSourceState certificate requestedScale count → Bool
  | .critical _ _ => true
  | .background _ => false

end RobustSourceState

/-- Selecting the critical tag at any chosen run offset constructs a genuine
bad window for that state's own displayed rational source. -/
@[expose] def robustBadWindowRegionAtOffset
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count) :
    Dirichlet.Sharpness.FiniteDynamics.BadWindowRegion
      (Dirichlet.Sharpness.BoxDynamics.RobustSourceState certificate requestedScale count)
      threshold requestedScale where
  event := Dirichlet.Sharpness.BoxDynamics.RobustSourceState.criticalEvent
  realize := by
    intro state selected
    cases state with
    | critical source inside =>
        let exactWindow :=
          (Dirichlet.Critical.Run.badWindowAtOffset
            certificate requestedScale count offset).1
        exact
          { source := source
            lower := exactWindow.lower
            upper := exactWindow.upper
            beyondScale := exactWindow.beyondScale
            consecutive :=
              Dirichlet.Critical.Robust.Run.robustRunBox_consecutiveAtOffset
                certificate requestedScale count source.value inside offset
            violates :=
              Dirichlet.Critical.Robust.Run.robustRunBox_violationAtOffset
                certificate requestedScale count source.value inside offset }
    | background source =>
        simp only [Dirichlet.Sharpness.BoxDynamics.RobustSourceState.criticalEvent] at selected
        cases selected

/-- The region event at every bounded offset is exactly the critical-state tag test. -/
@[simp] theorem robustBadWindowRegionAtOffset_event
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count) :
    (Dirichlet.Sharpness.BoxDynamics.robustBadWindowRegionAtOffset
      certificate requestedScale count offset).event =
      Dirichlet.Sharpness.BoxDynamics.RobustSourceState.criticalEvent := by
  rfl

/-- Exact area-calibrated mass assigned to the critical state. -/
@[expose] def criticalRate
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) : Fraction.Rational :=
  let area := Geometry.Rational.Box.Content.boxContent
    (Dirichlet.Critical.Robust.Run.robustRunBox certificate requestedScale count)
  area / (1 + area)

/-- The proper robust run box has positive exact rational area. -/
theorem robustRunBox_content_pos
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    0 < Geometry.Rational.Box.Content.boxContent
      (Dirichlet.Critical.Robust.Run.robustRunBox
        certificate requestedScale count) :=
  Geometry.Rational.Box.Content.boxContent_pos_of_proper
    (Dirichlet.Critical.Robust.Run.robustRunBox_proper
      certificate requestedScale count)

/-- The area-calibrated critical-state probability is positive. -/
theorem criticalRate_pos
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    0 < Dirichlet.Sharpness.BoxDynamics.criticalRate certificate requestedScale count := by
  unfold Dirichlet.Sharpness.BoxDynamics.criticalRate
  let area := Geometry.Rational.Box.Content.boxContent
    (Dirichlet.Critical.Robust.Run.robustRunBox certificate requestedScale count)
  have areaPositive : 0 < area := by
    simpa only [area] using
      Dirichlet.Sharpness.BoxDynamics.robustRunBox_content_pos certificate requestedScale count
  exact Fraction.Order.Field.div_pos_direct areaPositive
    ((show (0 : Fraction.Rational) < 1 by decide).trans_le
      (le_add_of_nonneg_right areaPositive.le))

/-- The area-calibrated critical-state probability is at most one. -/
theorem criticalRate_le_one
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    Dirichlet.Sharpness.BoxDynamics.criticalRate certificate requestedScale count ≤ 1 := by
  unfold Dirichlet.Sharpness.BoxDynamics.criticalRate
  let area := Geometry.Rational.Box.Content.boxContent
    (Dirichlet.Critical.Robust.Run.robustRunBox certificate requestedScale count)
  have areaPositive : 0 < area := by
    simpa only [area] using
      Dirichlet.Sharpness.BoxDynamics.robustRunBox_content_pos certificate requestedScale count
  apply (Fraction.Order.Field.div_le_iff_pos
    ((show (0 : Fraction.Rational) < 1 by decide).trans_le
      (le_add_of_nonneg_right areaPositive.le))).2
  calc
    area ≤ 1 + area := le_add_of_nonneg_left (by decide)
    _ = 1 * (1 + area) := by ring1

/-- The retained exact run source lies inside its robust box. -/
private theorem exactSource_inside_robustRunBox
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (Dirichlet.Critical.Robust.Run.robustRunBox certificate requestedScale count).Contains
      (Dirichlet.Critical.Run.criticalBadWindowRun
        certificate requestedScale count).source.value := by
  rw [← Dirichlet.Critical.Robust.Run.robustRunBox_anchor]
  exact (Dirichlet.Critical.Robust.Run.robustRunBox
    certificate requestedScale count).contains_anchor

/-- The exact common run source belongs to the displayed robust box. -/
theorem exactSource_inside_runBox
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (Dirichlet.Critical.Robust.Run.robustRunBox certificate requestedScale count).Contains
      (Dirichlet.Critical.Run.criticalBadWindowRun
        certificate requestedScale count).source.value :=
  Dirichlet.Sharpness.BoxDynamics.exactSource_inside_robustRunBox certificate requestedScale count

/-- Two-atom rational law: the exact critical source receives the
area-calibrated rate and the supplied background source receives the
complementary mass. -/
@[expose] def criticalAreaLaw
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (background : GaussianInt.Fraction) :
    Measure.Distribution
      (Dirichlet.Sharpness.BoxDynamics.RobustSourceState certificate requestedScale count) :=
  let rate := Dirichlet.Sharpness.BoxDynamics.criticalRate certificate requestedScale count
  { atoms :=
      [{ item := .critical
          (Dirichlet.Critical.Run.criticalBadWindowRun
            certificate requestedScale count).source
          (Dirichlet.Sharpness.BoxDynamics.exactSource_inside_runBox certificate requestedScale count)
         weight := rate
         nonnegative :=
          (Dirichlet.Sharpness.BoxDynamics.criticalRate_pos certificate requestedScale count).le },
       { item := .background background
         weight := 1 - rate
         nonnegative := Fraction.Order.Arithmetic.sub_nonneg_direct
          (Dirichlet.Sharpness.BoxDynamics.criticalRate_le_one certificate requestedScale count) }]
    total_one := by
      simp only [Measure.totalWeight_cons,
        Measure.totalWeight_nil]
      ring1 }

/-- The critical-state event has exactly the area-calibrated mass in the displayed two-atom law. -/
theorem criticalAreaLaw_probability_criticalEvent
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (background : GaussianInt.Fraction) :
    (Dirichlet.Sharpness.BoxDynamics.criticalAreaLaw certificate requestedScale count background).probability
        Dirichlet.Sharpness.BoxDynamics.RobustSourceState.criticalEvent =
      Dirichlet.Sharpness.BoxDynamics.criticalRate certificate requestedScale count := by
  unfold Dirichlet.Sharpness.BoxDynamics.criticalAreaLaw Measure.Distribution.probability
    Measure.eventWeight
  change Dirichlet.Sharpness.BoxDynamics.criticalRate certificate requestedScale count + (0 + 0) =
    Dirichlet.Sharpness.BoxDynamics.criticalRate certificate requestedScale count
  ring1

/-- The critical event in the area-calibrated law has strictly positive
rational probability. -/
theorem criticalAreaLaw_regionPositive
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (background : GaussianInt.Fraction) :
    0 < (Dirichlet.Sharpness.BoxDynamics.criticalAreaLaw certificate requestedScale count background).probability
      Dirichlet.Sharpness.BoxDynamics.RobustSourceState.criticalEvent := by
  rw [Dirichlet.Sharpness.BoxDynamics.criticalAreaLaw_probability_criticalEvent]
  exact Dirichlet.Sharpness.BoxDynamics.criticalRate_pos certificate requestedScale count

/-- Fully instantiated finite dynamical Chevallier analogue: after any
supplied burn-in, independent area-calibrated resampling hits a sound bad
window region with the displayed geometric probability lower bound. -/
theorem criticalArea_resampling_pathHit_probability_lower
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count)
    (background : GaussianInt.Fraction)
    (initial : Measure.Distribution
      (Dirichlet.Sharpness.BoxDynamics.RobustSourceState certificate requestedScale count))
    (burnIn blockCount : Nat) :
    let law := Dirichlet.Sharpness.BoxDynamics.criticalAreaLaw certificate requestedScale count background
    let region := Dirichlet.Sharpness.BoxDynamics.robustBadWindowRegionAtOffset
      certificate requestedScale count offset
    1 - (1 - Dirichlet.Sharpness.BoxDynamics.criticalRate certificate requestedScale count) ^ blockCount ≤
      (Measure.markovPaths
        (Measure.Distribution.blockTransition
          (Measure.Distribution.resamplingTransition law) 1)
        blockCount
        (Measure.Distribution.iterate
          (Measure.Distribution.resamplingTransition law)
          burnIn initial)).probability
        (Data.List.pathHits region.event) := by
  dsimp only
  have lower :=
    Measure.Distribution.resampling_pathHit_probability_lower
      (Dirichlet.Sharpness.BoxDynamics.criticalAreaLaw certificate requestedScale count background)
      (Dirichlet.Sharpness.BoxDynamics.robustBadWindowRegionAtOffset
        certificate requestedScale count offset).event
      (Dirichlet.Sharpness.BoxDynamics.criticalAreaLaw_regionPositive certificate requestedScale count
        background)
      initial burnIn blockCount
  rw [Dirichlet.Sharpness.BoxDynamics.robustBadWindowRegionAtOffset_event,
    Dirichlet.Sharpness.BoxDynamics.criticalAreaLaw_probability_criticalEvent] at lower
  exact lower

/-- Soundness of the probabilistic event remains constructive: a displayed
hit path returns the bad-window record itself. -/
@[expose] def badWindow_of_criticalArea_pathHits
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count)
    (path : List (Dirichlet.Sharpness.BoxDynamics.RobustSourceState certificate requestedScale count))
    (hits : Data.List.pathHits
      (Dirichlet.Sharpness.BoxDynamics.robustBadWindowRegionAtOffset
        certificate requestedScale count offset).event path = true) :
    BadWindow threshold requestedScale :=
  (Dirichlet.Sharpness.BoxDynamics.robustBadWindowRegionAtOffset certificate requestedScale count
    offset).badWindow_of_pathHits
    path hits

end Purelib.NumberTheory.Approximation.Dirichlet.Sharpness.BoxDynamics

end
