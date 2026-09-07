import mathlib.Tactic.QuotientFreeRing
import RFAP.Isolation.ShrinkingTrack
import RFAP.Measure.BoxContent
import FiniteMeasure.Operational

/-!
# Finite area observations of RFAP shrinking tracks

This is the Paper-I-side area interpretation of a winding-one track.  It uses
only RFAP rational boxes and no downstream encoding layer.  A request returns another
finite winding certificate whose enclosing rational area meets the supplied
budget.
-/

namespace RFAP.FiniteMeasure

abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack

/-- Positive rational box-radius request with square below the target area. -/
def trackAreaRadius (target : Coordinate) : Coordinate :=
  min 1 (target / 4)

theorem trackAreaRadius_pos {target : Coordinate} (positive : 0 < target) :
    0 < trackAreaRadius target := by
  exact lt_min (by decide)
    (RFAP.ConstructiveFraction.div_pos_direct positive (by decide))

theorem trackAreaRadius_sq_lt {target : Coordinate}
    (positive : 0 < target) : trackAreaRadius target ^ 2 < target := by
  let radius := trackAreaRadius target
  have radiusPositive : 0 < radius := trackAreaRadius_pos positive
  have radiusLeOne : radius ≤ 1 := min_le_left _ _
  have radiusLeQuarter : radius ≤ target / 4 := min_le_right _ _
  have radiusSquareLe : radius ^ 2 ≤ radius := by
    rw [pow_two]
    exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      radiusLeOne radiusPositive.le).trans_eq
        (RFAP.ConstructiveFraction.one_mul radius)
  have radiusLtFourRadius : radius < 4 * radius := by
    calc
      radius = 1 * radius :=
        (RFAP.ConstructiveFraction.one_mul radius).symm
      _ < 4 * radius :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
          (by decide) radiusPositive
  have fourRadiusLe : 4 * radius ≤ target := by
    have divided :=
      (RFAP.ConstructiveFraction.le_div_iff_pos
        (by decide : (0 : Coordinate) < 4)).mp radiusLeQuarter
    calc
      4 * radius = radius * 4 :=
        RFAP.ConstructiveFraction.mul_comm _ _
      _ ≤ target := divided
  exact radiusSquareLe.trans_lt (radiusLtFourRadius.trans_le fourRadiusLe)

/-- One area-requested state of an RFAP winding-one track. -/
def trackAreaState
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (target : Coordinate) (positive : 0 < target) :
    WindingOneState p ambient :=
  track.refine current (trackAreaRadius target)
    (trackAreaRadius_pos positive)

theorem trackAreaState_refines
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (target : Coordinate) (positive : 0 < target) :
    (trackAreaState track current target positive).box.Refines current.box :=
  track.nested current (trackAreaRadius target) (trackAreaRadius_pos positive)

/-- Every RFAP site admits a further finite winding-one box whose exact
rational area is below any supplied positive rational budget. -/
theorem trackAreaState_content_lt
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (current : WindingOneState p ambient)
    (target : Coordinate) (positive : 0 < target) :
    boxContent (trackAreaState track current target positive).box < target := by
  apply boxContent_lt_of_diagonalSq_lt
  exact (track.accurate current (trackAreaRadius target)
    (trackAreaRadius_pos positive)).trans_lt
      (trackAreaRadius_sq_lt positive)

/-- One displayed RFAP track state together with its finite refinement
certificate back to the track's distinguished initial box. -/
structure TrackAreaProcessState
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) where
  current : WindingOneState p ambient
  refines_initial : current.box.Refines track.initial.box

/-- Distinguished initial state of the finite area process. -/
def trackAreaProcessInitial
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) : TrackAreaProcessState track :=
  ⟨track.initial, RFAP.Boxes.Box.refines_refl _⟩

/-- Execute one finite rational area request while retaining reachability
from the initial RFAP track box. -/
def trackAreaProcessRequest
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient)
    (state : TrackAreaProcessState track)
    (target : Coordinate) (positive : 0 < target) :
    TrackAreaProcessState track :=
  let refined := trackAreaState track state.current target positive
  ⟨refined,
    (trackAreaState_refines track state.current target positive).trans
      state.refines_initial⟩

/-- Executable finite process for the shrinking rational area budget of one
RFAP winding track. -/
def trackAreaProcess
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) :
    _root_.FiniteMeasure.BoundProcess where
  State := TrackAreaProcessState track
  bound state := boxContentBound state.current.box
  initial := trackAreaProcessInitial track
  request := trackAreaProcessRequest track
  request_refines state target positive := by
    apply boxContentBound_refines
    exact trackAreaState_refines track state.current target positive
  accurate state target positive := by
    rw [boxContentBound_width]
    exact trackAreaState_content_lt track state.current target positive
  refinesInitial state :=
    boxContentBound_refines state.refines_initial

theorem trackAreaProcess_anchored
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) :
    (trackAreaProcess track).AnchoredAt 0 := by
  intro state
  exact ⟨le_rfl, boxContent_nonneg state.current.box⟩

/-- The RFAP shrinking-area controller is operationally equivalent to exact
rational zero, witnessed entirely by finite requests. -/
theorem trackAreaProcess_operationallyEquivalent_zero
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) :
    _root_.FiniteMeasure.OperationallyEquivalent (trackAreaProcess track)
      (_root_.FiniteMeasure.BoundProcess.exact 0) :=
  _root_.FiniteMeasure.operationallyEquivalent_exact_of_anchoredAt
    (trackAreaProcess track) 0 (trackAreaProcess_anchored track)

/-- Simultaneous finite area observations of a homogeneous finite RFAP track
family. -/
def trackFamilyStates
    {p : GaussianPolynomial} {ambient : Box} :
    (tracks : List (WindingOneTrack p ambient)) →
    (target : Coordinate) → 0 < target → List (WindingOneState p ambient)
  | [], _, _ => []
  | track :: remaining, target, positive =>
      let half := target / 2
      let halfPositive := RFAP.ConstructiveFraction.div_pos_direct positive
        (by decide : (0 : Coordinate) < 2)
      trackAreaState track track.initial half halfPositive ::
        trackFamilyStates remaining half halfPositive

/-- Total exact rational area of displayed winding states. -/
def trackFamilyContent
    {p : GaussianPolynomial} {ambient : Box}
    (states : List (WindingOneState p ambient)) : Coordinate :=
  (states.map fun state => boxContent state.box).sum

/-- A finite RFAP root-site family has simultaneous winding-certified box
observations inside every positive rational total area budget. -/
theorem trackFamilyStates_content_lt
    {p : GaussianPolynomial} {ambient : Box} :
    ∀ (tracks : List (WindingOneTrack p ambient))
      (target : Coordinate) (positive : 0 < target),
      trackFamilyContent (trackFamilyStates tracks target positive) < target
  | [], target, positive => by
      simpa only [trackFamilyStates, trackFamilyContent, List.map_nil,
        List.sum_nil] using positive
  | track :: remaining, target, positive => by
      let half := target / 2
      have halfPositive : (0 : Coordinate) < half :=
        RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
      have headSmall :=
        trackAreaState_content_lt track track.initial half halfPositive
      have tailSmall :=
        trackFamilyStates_content_lt remaining half halfPositive
      dsimp only [trackFamilyStates, trackFamilyContent]
      rw [List.map_cons, List.sum_cons]
      calc
        boxContent (trackAreaState track track.initial half halfPositive).box +
            trackFamilyContent
              (trackFamilyStates remaining half halfPositive) <
            half + half :=
          RFAP.ConstructiveFraction.add_lt_add_direct headSmall tailSmall
        _ = target := by
          dsimp only [half]
          calc
            target / 2 + target / 2 = (target / 2) * 2 := by ring1
            _ = target :=
              RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 2
                (by decide)

end RFAP.FiniteMeasure
