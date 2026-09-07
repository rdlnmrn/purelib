import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.ResamplingReturn
import RFAP.Approximation.DynamicalSharpness
import RFAP.Approximation.RobustCriticalRun
import RFAP.Measure.BoxContent

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

namespace RFAP.RobustDynamicalSharpness

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Fraction := RFAP.HurwitzRational.Fraction
abbrev BadWindow := RFAP.DynamicalSharpness.BadWindow

/-- A critical state carries the proof that its displayed rational source is
inside the fully robust box.  A background state carries no such claim. -/
inductive RobustSourceState
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) where
  | critical (source : Fraction)
      (inside :
        (RFAP.RobustCriticalRun.robustRunBox certificate requestedScale count).Contains
          source.value)
  | background (source : Fraction)

namespace RobustSourceState

def source
    {threshold : Coordinate}
    {certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold}
    {requestedScale count : Nat} :
    RobustSourceState certificate requestedScale count → Fraction
  | .critical value _ => value
  | .background value => value

def criticalEvent
    {threshold : Coordinate}
    {certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold}
    {requestedScale count : Nat} :
    RobustSourceState certificate requestedScale count → Bool
  | .critical _ _ => true
  | .background _ => false

end RobustSourceState

/-- Selecting the critical tag at any chosen run offset constructs a genuine
bad window for that state's own displayed rational source. -/
def robustBadWindowRegionAtOffset
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count) :
    RFAP.DynamicalSharpness.BadWindowRegion
      (RobustSourceState certificate requestedScale count)
      threshold requestedScale where
  event := RobustSourceState.criticalEvent
  realize := by
    intro state selected
    cases state with
    | critical source inside =>
        let exactWindow :=
          (RFAP.CriticalBadWindowRun.badWindowAtOffset
            certificate requestedScale count offset).1
        exact
          { source := source
            lower := exactWindow.lower
            upper := exactWindow.upper
            beyondScale := exactWindow.beyondScale
            consecutive :=
              RFAP.RobustCriticalRun.robustRunBox_consecutiveAtOffset
                certificate requestedScale count source.value inside offset
            violates :=
              RFAP.RobustCriticalRun.robustRunBox_violationAtOffset
                certificate requestedScale count source.value inside offset }
    | background source =>
        simp only [RobustSourceState.criticalEvent] at selected
        cases selected

@[simp] theorem robustBadWindowRegionAtOffset_event
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count) :
    (robustBadWindowRegionAtOffset
      certificate requestedScale count offset).event =
      RobustSourceState.criticalEvent := by
  rfl

/-- Exact area-calibrated mass assigned to the critical state. -/
def criticalRate
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) : Coordinate :=
  let area := RFAP.FiniteMeasure.boxContent
    (RFAP.RobustCriticalRun.robustRunBox certificate requestedScale count)
  area / (1 + area)

theorem robustRunBox_content_pos
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    0 < RFAP.FiniteMeasure.boxContent
      (RFAP.RobustCriticalRun.robustRunBox
        certificate requestedScale count) :=
  RFAP.FiniteMeasure.boxContent_pos_of_proper
    (RFAP.RobustCriticalRun.robustRunBox_proper
      certificate requestedScale count)

theorem criticalRate_pos
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    0 < criticalRate certificate requestedScale count := by
  unfold criticalRate
  let area := RFAP.FiniteMeasure.boxContent
    (RFAP.RobustCriticalRun.robustRunBox certificate requestedScale count)
  have areaPositive : 0 < area := by
    simpa only [area] using
      robustRunBox_content_pos certificate requestedScale count
  exact RFAP.ConstructiveFraction.div_pos_direct areaPositive
    ((show (0 : Coordinate) < 1 by decide).trans_le
      (le_add_of_nonneg_right areaPositive.le))

theorem criticalRate_le_one
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    criticalRate certificate requestedScale count ≤ 1 := by
  unfold criticalRate
  let area := RFAP.FiniteMeasure.boxContent
    (RFAP.RobustCriticalRun.robustRunBox certificate requestedScale count)
  have areaPositive : 0 < area := by
    simpa only [area] using
      robustRunBox_content_pos certificate requestedScale count
  apply (RFAP.ConstructiveFraction.div_le_iff_pos
    ((show (0 : Coordinate) < 1 by decide).trans_le
      (le_add_of_nonneg_right areaPositive.le))).2
  calc
    area ≤ 1 + area := le_add_of_nonneg_left (by decide)
    _ = 1 * (1 + area) := by ring1

private theorem exactSource_inside_robustRunBox
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) :
    (RFAP.RobustCriticalRun.robustRunBox certificate requestedScale count).Contains
      (RFAP.CriticalBadWindowRun.criticalBadWindowRun
        certificate requestedScale count).source.value := by
  rw [← RFAP.RobustCriticalRun.robustRunBox_anchor]
  exact (RFAP.RobustCriticalRun.robustRunBox
    certificate requestedScale count).contains_anchor

/-- Two-atom rational law: the exact critical source receives the
area-calibrated rate and the supplied background source receives the
complementary mass. -/
def criticalAreaLaw
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (background : Fraction) :
    _root_.FiniteMeasure.Distribution
      (RobustSourceState certificate requestedScale count) :=
  let rate := criticalRate certificate requestedScale count
  { atoms :=
      [{ item := .critical
          (RFAP.CriticalBadWindowRun.criticalBadWindowRun
            certificate requestedScale count).source
          (exactSource_inside_robustRunBox certificate requestedScale count)
         weight := rate
         nonnegative :=
          (criticalRate_pos certificate requestedScale count).le },
       { item := .background background
         weight := 1 - rate
         nonnegative := RFAP.ConstructiveFraction.sub_nonneg_direct
          (criticalRate_le_one certificate requestedScale count) }]
    total_one := by
      simp only [_root_.FiniteMeasure.totalWeight_cons,
        _root_.FiniteMeasure.totalWeight_nil]
      ring1 }

theorem criticalAreaLaw_probability_criticalEvent
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (background : Fraction) :
    (criticalAreaLaw certificate requestedScale count background).probability
        RobustSourceState.criticalEvent =
      criticalRate certificate requestedScale count := by
  unfold criticalAreaLaw _root_.FiniteMeasure.Distribution.probability
    _root_.FiniteMeasure.eventWeight
  change criticalRate certificate requestedScale count + (0 + 0) =
    criticalRate certificate requestedScale count
  ring1

/-- The critical event in the area-calibrated law has strictly positive
rational probability. -/
theorem criticalAreaLaw_regionPositive
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (background : Fraction) :
    0 < (criticalAreaLaw certificate requestedScale count background).probability
      RobustSourceState.criticalEvent := by
  rw [criticalAreaLaw_probability_criticalEvent]
  exact criticalRate_pos certificate requestedScale count

/-- Fully instantiated finite dynamical Chevallier analogue: after any
supplied burn-in, independent area-calibrated resampling hits a sound bad
window region with the displayed geometric probability lower bound. -/
theorem criticalArea_resampling_pathHit_probability_lower
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count)
    (background : Fraction)
    (initial : _root_.FiniteMeasure.Distribution
      (RobustSourceState certificate requestedScale count))
    (burnIn blockCount : Nat) :
    let law := criticalAreaLaw certificate requestedScale count background
    let region := robustBadWindowRegionAtOffset
      certificate requestedScale count offset
    1 - (1 - criticalRate certificate requestedScale count) ^ blockCount ≤
      (_root_.FiniteMeasure.markovPaths
        (_root_.FiniteMeasure.Distribution.blockTransition
          (_root_.FiniteMeasure.Distribution.resamplingTransition law) 1)
        blockCount
        (_root_.FiniteMeasure.Distribution.iterate
          (_root_.FiniteMeasure.Distribution.resamplingTransition law)
          burnIn initial)).probability
        (_root_.FiniteMeasure.pathHits region.event) := by
  dsimp only
  have lower :=
    _root_.FiniteMeasure.Distribution.resampling_pathHit_probability_lower
      (criticalAreaLaw certificate requestedScale count background)
      (robustBadWindowRegionAtOffset
        certificate requestedScale count offset).event
      (criticalAreaLaw_regionPositive certificate requestedScale count
        background)
      initial burnIn blockCount
  rw [robustBadWindowRegionAtOffset_event,
    criticalAreaLaw_probability_criticalEvent] at lower
  exact lower

/-- Soundness of the probabilistic event remains constructive: a displayed
hit path returns the bad-window record itself. -/
def badWindow_of_criticalArea_pathHits
    {threshold : Coordinate}
    (certificate :
      RFAP.FiniteWindowSharpness.IsSharperWindowThreshold threshold)
    (requestedScale count : Nat) (offset : Fin count)
    (path : List (RobustSourceState certificate requestedScale count))
    (hits : _root_.FiniteMeasure.pathHits
      (robustBadWindowRegionAtOffset
        certificate requestedScale count offset).event path = true) :
    BadWindow threshold requestedScale :=
  (robustBadWindowRegionAtOffset certificate requestedScale count offset).badWindow_of_pathHits
    path hits

end RFAP.RobustDynamicalSharpness
