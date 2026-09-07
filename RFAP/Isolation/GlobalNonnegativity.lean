import RFAP.Geometry.CentralBandGrid
import RFAP.Isolation.FinitePacking

/-!
# Choice-free global winding nonnegativity

If a clear box had negative raw winding, one eliminant-safe Newton band of
raw winding four can be removed and a negative complement cell retained.
Finite iteration would then create one more pairwise-separated shrinking
track than the explicit rational grid can contain.
-/

namespace RFAP.GlobalNonnegativity

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance
abbrev AxisEliminationCertificate :=
  RFAP.AxisSafeCuts.AxisEliminationCertificate
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate
abbrev WindingOneState :=
  RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack :=
  RFAP.ShrinkingTrack.WindingOneTrack

open RFAP.Winding
open RFAP.CentralBandGrid
open RFAP.FinitePacking

theorem strictInterior_trans_refines
    {small middle outer : Box}
    (strict : small.StrictInterior middle)
    (refines : middle.Refines outer) : small.StrictInterior outer :=
  ⟨refines.1.trans_lt strict.left,
    strict.right.trans_le refines.2.1,
    refines.2.2.1.trans_lt strict.bottom,
    strict.top.trans_le refines.2.2.2⟩

/-- A clear negative-raw-winding region in one fixed finite ambient box. -/
structure NegativeState
    (p : GaussianPolynomial) (ambient : Box) where
  box : Box
  refinesAmbient : box.Refines ambient
  proper : box.Proper
  clearance : BoundaryClearance p box
  rawWinding_neg : quadrupledBoxWinding p box < 0

def NegativeState.raw
    {p : GaussianPolynomial} {ambient : Box}
    (state : NegativeState p ambient) :
    RFAP.RawSubdivision.RawWindingState p ambient where
  box := state.box
  refinesAmbient := state.refinesAmbient
  proper := state.proper
  clearance := state.clearance
  rawWinding_ne := ne_of_lt state.rawWinding_neg

/-- One band-removal step, retaining a deterministically selected negative
complement cell and the separation invariant needed by later steps. -/
structure StepOutput
    (p : GaussianPolynomial) (ambient : Box)
    (current : NegativeState p ambient) where
  track : WindingOneTrack p ambient
  next : NegativeState p ambient
  center_strict_current : track.initial.box.StrictInterior current.box
  next_refines_current : next.box.Refines current.box
  center_avoids_next : ∀ {small : Box},
    small.StrictInterior next.box → track.initial.box.Separated small

def extractStep
    {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : NegativeState p ambient) : StepOutput p ambient current := by
  have onePositive : (0 : Coordinate) < 1 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 1) (by decide)
  let extracted := RFAP.NewtonBand.extract degreeAtLeastTwo
    squarefree elimination current.raw onePositive
  let center := extracted.band.box
  let centerState : WindingOneState p ambient :=
    { box := center
      refinesAmbient := extracted.refinesAmbient
      proper := extracted.proper
      clearance := extracted.clearance
      rawWindingFour := extracted.rawWindingFour
      ambientLeftClearance := extracted.ambientLeftClearance
      ambientRightClearance := extracted.ambientRightClearance
      ambientBottomClearance := extracted.ambientBottomClearance
      ambientTopClearance := extracted.ambientTopClearance }
  let track := RFAP.ShrinkingTrack.ofInitial degreeAtLeastTwo
    squarefree elimination centerState
  let grid : RFAP.CentralBandGrid.Grid p current.box center :=
    build current.clearance extracted.proper extracted.strictCurrent
      extracted.leftLineClearance extracted.rightLineClearance
      extracted.bottomLineClearance extracted.topLineClearance
  let nextCell := grid.firstNegative
  have nextNegative : quadrupledBoxWinding p nextCell.box < 0 :=
    grid.firstNegative_rawWinding_neg current.rawWinding_neg
      extracted.rawWindingFour
  let next : NegativeState p ambient :=
    { box := nextCell.box
      refinesAmbient := nextCell.refines.trans current.refinesAmbient
      proper := nextCell.proper
      clearance := nextCell.clearance
      rawWinding_neg := nextNegative }
  exact
    { track := track
      next := next
      center_strict_current := by
        simpa only [track, RFAP.ShrinkingTrack.ofInitial,
          centerState, center, NegativeState.raw] using extracted.strictCurrent
      next_refines_current := nextCell.refines
      center_avoids_next := by
        intro small strict
        change center.Separated small
        exact nextCell.center_separated_from_strictInterior strict }

/-- After `count` removal steps, retain the current negative region and all
pairwise-separated tracks constructed so far. -/
structure Sequence
    (p : GaussianPolynomial) (ambient : Box) (count : Nat) where
  current : NegativeState p ambient
  tracks : Fin count → WindingOneTrack p ambient
  pairwise : ∀ i j, i ≠ j →
    (tracks i).initial.box.Separated (tracks j).initial.box
  avoidsCurrent : ∀ i {small : Box},
    small.StrictInterior current.box →
      (tracks i).initial.box.Separated small

def Sequence.nil
    {p : GaussianPolynomial} {ambient : Box}
    (current : NegativeState p ambient) : Sequence p ambient 0 where
  current := current
  tracks := Fin.elim0
  pairwise := fun i => Fin.elim0 i
  avoidsCurrent := fun i => Fin.elim0 i

private theorem fin_eq_zero_or_eq_succ {count : Nat}
    (index : Fin (count + 1)) :
    index = 0 ∨ ∃ previous : Fin count, index = previous.succ := by
  refine Fin.cases ?_ (fun previous => ?_) index
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

def Sequence.step
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (sequence : Sequence p ambient count) : Sequence p ambient (count + 1) := by
  let extracted := extractStep degreeAtLeastTwo squarefree elimination
    sequence.current
  let tracks : Fin (count + 1) → WindingOneTrack p ambient :=
    fun index => Fin.cases extracted.track sequence.tracks index
  exact
    { current := extracted.next
      tracks := tracks
      pairwise := by
        intro i j different
        obtain rfl | ⟨oldI, rfl⟩ := fin_eq_zero_or_eq_succ i
        · obtain rfl | ⟨oldJ, rfl⟩ := fin_eq_zero_or_eq_succ j
          · exact (different rfl).elim
          · simpa only [tracks, Fin.cases_zero, Fin.cases_succ] using
              RFAP.Boxes.Box.separated_symm
                (sequence.avoidsCurrent oldJ
                  extracted.center_strict_current)
        · obtain rfl | ⟨oldJ, rfl⟩ := fin_eq_zero_or_eq_succ j
          · simpa only [tracks, Fin.cases_zero, Fin.cases_succ] using
              sequence.avoidsCurrent oldI extracted.center_strict_current
          · have oldDifferent : oldI ≠ oldJ := by
              intro equal
              apply different
              exact congrArg Fin.succ equal
            simpa only [tracks, Fin.cases_succ] using
              sequence.pairwise oldI oldJ oldDifferent
      avoidsCurrent := by
        intro i small strict
        obtain rfl | ⟨oldI, rfl⟩ := fin_eq_zero_or_eq_succ i
        · simpa only [tracks, Fin.cases_zero] using
            extracted.center_avoids_next strict
        · have strictCurrent := strictInterior_trans_refines strict
            extracted.next_refines_current
          simpa only [tracks, Fin.cases_succ] using
            sequence.avoidsCurrent oldI strictCurrent }

/-- Execute exactly the requested finite number of negative-region removal
steps. -/
def iterate
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound) :
    (count : Nat) → NegativeState p ambient → Sequence p ambient count
  | 0, current => Sequence.nil current
  | count + 1, current =>
      (iterate degreeAtLeastTwo squarefree elimination count current).step
        degreeAtLeastTwo squarefree elimination

/-- Raw global nonnegativity in any supplied finite ambient box. -/
theorem quadrupledBoxWinding_nonnegative
    {p : GaussianPolynomial} {ambient box : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (refines : box.Refines ambient) (proper : box.Proper)
    (clearance : BoundaryClearance p box) :
    0 ≤ quadrupledBoxWinding p box := by
  by_cases nonnegative : 0 ≤ quadrupledBoxWinding p box
  · exact nonnegative
  · have negative : quadrupledBoxWinding p box < 0 :=
      lt_of_not_ge nonnegative
    let initial : NegativeState p ambient :=
      { box := box
        refinesAmbient := refines
        proper := proper
        clearance := clearance
        rawWinding_neg := negative }
    let bound := packingBound squarefree ambient
    let sequence := iterate degreeAtLeastTwo squarefree elimination
      (bound + 1) initial
    have packed := finite_family_card_le_packingBound
      ((show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo)
      squarefree sequence.tracks (fun i => (sequence.tracks i).initial)
      sequence.pairwise
    have impossible : Nat.succ bound ≤ bound := by
      simpa only [Nat.succ_eq_add_one] using packed
    exact (Nat.not_succ_le_self bound impossible).elim

end RFAP.GlobalNonnegativity
