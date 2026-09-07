import FTA.CentralBandGrid
import FTA.ConstructiveTrack
import FTA.FinitePacking
import FTA.RawLocalExtraction

/-!
# Global winding nonnegativity

This is Theorem 9.1.  The proof runs at the exact raw-winding normalization:
if a clear box had negative raw winding, local extraction removes a central
box of raw winding four and a deterministic choice retains a negative one of
the eight complement cells.  Iterating one step beyond the explicit packing
bound produces too many pairwise separated constructive tracks.
-/

namespace FTA.GlobalNonnegativity

open scoped BigOperators

open CCL
open FTA.AxisSafeCuts
open FTA.CentralBandGrid
open FTA.ConstructiveTrack
open FTA.FinitePacking
open FTA.GaussianDifferenceResultant
open FTA.LocalExtraction
open FTA.RawLocalExtraction
open FTA.RootTrackSeparation
open FTA.Winding

abbrev GaussianPolynomial := FTA.ComputablePolynomial.DensePolynomial QI

theorem strictInterior_trans_refines
    {small middle outer : CCL.RatBox}
    (hsmall : StrictInterior small middle)
    (hmiddle : middle.Refines outer) : StrictInterior small outer :=
  ⟨lt_of_le_of_lt hmiddle.1 hsmall.left,
    lt_of_lt_of_le hsmall.right hmiddle.2.1,
    lt_of_le_of_lt hmiddle.2.2.1 hsmall.bottom,
    lt_of_lt_of_le hsmall.top hmiddle.2.2.2⟩

/-- A clear negative-raw-winding region inside the fixed global square. -/
structure NegativeState
    (p : GaussianPolynomial) (ambient : CCL.RatBox) where
  box : CCL.RatBox
  refinesAmbient : box.Refines ambient
  proper : box.Proper
  clearance : BoxBoundaryClearanceCertificate p box
  rawWinding_neg : quadrupledBoxWinding p box < 0

/-- One removal step: a new winding-one track and a negative complement cell.
The separation field is phrased for every strict interior of the next cell,
which is exactly the invariant needed by later extraction steps. -/
structure StepOutput
    (p : GaussianPolynomial) (ambient : CCL.RatBox)
    (current : NegativeState p ambient) where
  track : WindingOneTrack p ambient
  next : NegativeState p ambient
  center_strict_current : StrictInterior track.initial.box current.box
  next_refines_current : next.box.Refines current.box
  center_avoids_next : ∀ {small : CCL.RatBox},
    StrictInterior small next.box → track.initial.box.Separated small

/-- The coefficient-computed extraction and `3 × 3` grid implement one
deterministic negative-region step. -/
def extractStep
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (current : NegativeState p ambient) : StepOutput p ambient current := by
  let extracted := RawLocalExtraction.extract squarefree current.clearance
    current.proper (ne_of_lt current.rawWinding_neg) (by norm_num : (0 : ℚ) < 1)
    elimination
  let center := extracted.band.band.box
  let centerState : WindingOneState p ambient :=
    { box := center
      refinesAmbient := extracted.band.refines.trans current.refinesAmbient
      proper := extracted.band.band.proper extracted.band.radius_positive
      rawWindingFour := extracted.band.raw_winding_four
      clearance := extracted.band.boundaryClearance
      ambientLeftClearance := extracted.band.leftLineClearanceIn ambient
      ambientRightClearance := extracted.band.rightLineClearanceIn ambient
      ambientBottomClearance := extracted.band.bottomLineClearanceIn ambient
      ambientTopClearance := extracted.band.topLineClearanceIn ambient }
  let track := ConstructiveTrack.ofInitial squarefree elimination centerState
  let interior : StrictInterior center current.box :=
    { left := extracted.band_strictly_inside.1
      right := extracted.band_strictly_inside.2.1
      bottom := extracted.band_strictly_inside.2.2.1
      top := extracted.band_strictly_inside.2.2.2 }
  let grid : Grid p current.box center := build current.clearance
    centerState.proper interior
    extracted.band.leftLineClearance extracted.band.rightLineClearance
    extracted.band.bottomLineClearance extracted.band.topLineClearance
  let nextCell := grid.firstNegative
  have hnextNegative : quadrupledBoxWinding p nextCell.box < 0 :=
    grid.firstNegative_rawWinding_neg current.rawWinding_neg
      extracted.band.raw_winding_four
  let next : NegativeState p ambient :=
    { box := nextCell.box
      refinesAmbient := nextCell.refines.trans current.refinesAmbient
      proper := nextCell.proper
      clearance := nextCell.clearance
      rawWinding_neg := hnextNegative }
  exact
    { track := track
      next := next
      center_strict_current := by
        simpa only [track, ConstructiveTrack.ofInitial, centerState] using interior
      next_refines_current := nextCell.refines
      center_avoids_next := by
        intro small hsmall
        change center.Separated small
        exact nextCell.center_separated_from_strictInterior hsmall }

/-- After `n` removal steps, retain the current negative region, all `n`
tracks, their pairwise separation, and the strict-interior avoidance invariant
needed by the next step. -/
structure Sequence
    (p : GaussianPolynomial) (ambient : CCL.RatBox) (n : ℕ) where
  current : NegativeState p ambient
  tracks : Fin n → WindingOneTrack p ambient
  pairwise : ∀ i j, i ≠ j →
    (tracks i).initial.box.Separated (tracks j).initial.box
  avoidsCurrent : ∀ i {small : CCL.RatBox},
    StrictInterior small current.box → (tracks i).initial.box.Separated small

def Sequence.nil
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (current : NegativeState p ambient) : Sequence p ambient 0 where
  current := current
  tracks := Fin.elim0
  pairwise := fun i => Fin.elim0 i
  avoidsCurrent := fun i => Fin.elim0 i

def Sequence.step
    {p : GaussianPolynomial} {ambient : CCL.RatBox} {n : ℕ}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (sequence : Sequence p ambient n) : Sequence p ambient (n + 1) := by
  let extracted := extractStep squarefree elimination sequence.current
  let tracks : Fin (n + 1) → WindingOneTrack p ambient :=
    Fin.cons extracted.track sequence.tracks
  exact
    { current := extracted.next
      tracks := tracks
      pairwise := by
        intro i j hij
        obtain rfl | ⟨oldI, rfl⟩ := Fin.eq_zero_or_eq_succ i
        · obtain rfl | ⟨oldJ, rfl⟩ := Fin.eq_zero_or_eq_succ j
          · exact False.elim (hij rfl)
          simpa only [tracks, Fin.cons_zero, Fin.cons_succ] using
            CCL.RatBox.separated_symm
              (sequence.avoidsCurrent oldJ extracted.center_strict_current)
        · obtain rfl | ⟨oldJ, rfl⟩ := Fin.eq_zero_or_eq_succ j
          · simpa only [tracks, Fin.cons_zero, Fin.cons_succ] using
              sequence.avoidsCurrent oldI extracted.center_strict_current
          · have hne : oldI ≠ oldJ := by
              intro hEq
              apply hij
              exact Fin.succ_inj.mpr hEq
            simpa only [tracks, Fin.cons_succ] using
              sequence.pairwise oldI oldJ hne
      avoidsCurrent := by
        intro i small hsmall
        obtain rfl | ⟨oldI, rfl⟩ := Fin.eq_zero_or_eq_succ i
        ·
          simpa only [tracks, Fin.cons_zero] using
            extracted.center_avoids_next hsmall
        ·
          have hsmallCurrent := strictInterior_trans_refines hsmall
            extracted.next_refines_current
          simpa only [tracks, Fin.cons_succ] using
            sequence.avoidsCurrent oldI hsmallCurrent }

/-- Execute exactly the requested finite number of negative-region removal
steps. -/
def iterate
    {p : GaussianPolynomial} {ambient : CCL.RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (n : ℕ) → NegativeState p ambient → Sequence p ambient n
  | 0, current => Sequence.nil current
  | n + 1, current =>
      (iterate squarefree elimination n current).step squarefree elimination

/-- Raw form of Theorem 9.1.  It is stronger than the normalized statement
and makes all grid additivity unconditional. -/
theorem quadrupledBoxWinding_nonnegative
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {B : CCL.RatBox} (hrefines : B.Refines (CCL.RatBox.symmetric R hR))
    (hproper : B.Proper)
    (clearance : BoxBoundaryClearanceCertificate p B) :
    0 ≤ quadrupledBoxWinding p B := by
  by_contra hnonneg
  have hnegative : quadrupledBoxWinding p B < 0 := lt_of_not_ge hnonneg
  let initial : NegativeState p (CCL.RatBox.symmetric R hR) :=
    { box := B
      refinesAmbient := hrefines
      proper := hproper
      clearance := clearance
      rawWinding_neg := hnegative }
  let bound := packingBound R
    (squarefreeSeparationRadius
      (sparseSquarefreeCertificate squarefree))
  let sequence := iterate squarefree elimination (bound + 1) initial
  have hpacking := finite_family_card_le_packingBound p R hR squarefree
    hdegree sequence.tracks (fun i => (sequence.tracks i).initial)
    sequence.pairwise
  dsimp only [bound] at hpacking
  omega

/-- Theorem 9.1 in the paper's ordinary integer normalization. -/
theorem boxWinding_nonnegative
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {B : CCL.RatBox} (hrefines : B.Refines (CCL.RatBox.symmetric R hR))
    (hproper : B.Proper)
    (clearance : BoxBoundaryClearanceCertificate p B) :
    0 ≤ boxWinding p B := by
  exact Int.ediv_nonneg
    (quadrupledBoxWinding_nonnegative p R hR squarefree hdegree
      elimination hrefines hproper clearance) (by norm_num)

/-- Finite-list form of Theorem 9.1. -/
theorem finite_total_boxWinding_nonnegative
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (squarefree : GaussianSquarefreeCertificate p)
    (hdegree : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {n : ℕ} (boxes : Fin n → CCL.RatBox)
    (hrefines : ∀ i, (boxes i).Refines (CCL.RatBox.symmetric R hR))
    (hproper : ∀ i, (boxes i).Proper)
    (clearance : ∀ i, BoxBoundaryClearanceCertificate p (boxes i)) :
    0 ≤ ∑ i, boxWinding p (boxes i) := by
  exact Finset.sum_nonneg fun i _ =>
    boxWinding_nonnegative p R hR squarefree hdegree elimination
      (hrefines i) (hproper i) (clearance i)

end FTA.GlobalNonnegativity
