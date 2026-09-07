import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Persistent.InteriorGap
import RFAP.Isolation.Maximality
import RFAP.Geometry.ProtectedBoundary
import RFAP.Winding.Residual

/-!
# Comparing complete CCL profile children with winding-one states

The complete profile refinement is parameterized by an arbitrary finite
pairwise-separated box family.  This module instantiates that interface with
the boxes carried by explicit finite winding-one states.  Every retained
profile child is then compared with the actual numerical states, not with an
unrelated list of boxes.

An owned result records only a displayed Gaussian-rational curve sample in
one state, together with its small polynomial residual and nonzero derivative.
The sample-owner comparison remains pointwise and is never promoted to root
existence.  A separate affine-family scan preserves the stronger semantics
already computed for each profile: either displayed rational factor zeros are
inside the dispatched box, or the complete rational non-pole event cylinder
is outside it.  Neither alternative asserts that a factor zero exists.
-/

namespace CCL.PersistentCCLWindingOwnership

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack
abbrev SquarefreeCertificate :=
  RFAP.LocalExtraction.SquarefreeCertificate
abbrev CurveBoundary := CCL.PersistentCCLDispatch.CurveBoundary

/-- The residual-localization layer needs only the protected geometry of a
winding-one state, not its winding count. -/
abbrev protectedAmbient
    {p : GaussianPolynomial} {ambient : Box}
    (state : WindingOneState p ambient) :
    RFAP.ResidualWinding.ProtectedAmbient p ambient :=
  RFAP.ResidualWinding.ProtectedAmbient.ofWindingOne state

/-- An explicitly finite family of numerical winding-one states whose boxes
are pairwise positively separated. -/
structure WindingFamily (p : GaussianPolynomial) (ambient : Box) where
  states : List (WindingOneState p ambient)
  pairwise : states.Pairwise fun left right =>
    left.box.Separated right.box

namespace WindingFamily

/-- Forget the winding certificates while retaining the aligned finite box
list used by profile ownership. -/
def boxes {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient) : List Box :=
  family.states.map fun state => state.box

@[simp] theorem boxes_length
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient) :
    family.boxes.length = family.states.length := by
  simp [boxes]

theorem boxes_pairwise
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient) :
    family.boxes.Pairwise fun left right => left.Separated right := by
  simpa only [boxes, QuotientFreeList.pairwise_map] using family.pairwise

/-- State aligned with one index of the mapped box list. -/
def stateAtBoxIndex
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient)
    (index : Fin family.boxes.length) : WindingOneState p ambient :=
  family.states.get
    ⟨index.val, by simpa only [boxes, List.length_map] using index.isLt⟩

theorem boxAt_eq
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient)
    (index : Fin family.boxes.length) :
    family.boxes.get index = (family.stateAtBoxIndex index).box := by
  simp only [boxes, stateAtBoxIndex, List.get_eq_getElem, List.getElem_map]

theorem boxAt_refinesAmbient
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient)
    (index : Fin family.boxes.length) :
    (family.boxes.get index).Refines ambient := by
  rw [family.boxAt_eq index]
  exact (family.stateAtBoxIndex index).refinesAmbient

/-- The finite list of positive boundary clearances carried by the numerical
states. -/
def clearanceBounds
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient) : List Coordinate :=
  family.states.map fun state => state.clearance.bound

theorem clearanceBounds_positive
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient) :
    ∀ bound ∈ family.clearanceBounds, 0 < bound := by
  intro bound member
  rw [clearanceBounds, QuotientFreeList.mem_map] at member
  rcases member with ⟨state, _stateMember, rfl⟩
  exact state.clearance.positive

/-- One positive rational target below every state boundary clearance.  The
empty family retains the harmless value `1`. -/
def clearanceTarget
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient) : Coordinate :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum
    family.clearanceBounds

theorem clearanceTarget_pos
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient) : 0 < family.clearanceTarget :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_pos _
    family.clearanceBounds_positive

theorem clearanceTarget_le_stateAt
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient)
    (index : Fin family.boxes.length) :
    family.clearanceTarget ≤
      (family.stateAtBoxIndex index).clearance.bound := by
  apply
    CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_le_of_mem
  rw [clearanceBounds, QuotientFreeList.mem_map]
  refine ⟨family.stateAtBoxIndex index, ?_, rfl⟩
  exact List.get_mem family.states
    ⟨index.val, by
      simpa only [boxes, List.length_map] using index.isLt⟩

theorem clearanceTarget_quarter_le_stateAt
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient)
    (index : Fin family.boxes.length) :
    family.clearanceTarget / 4 ≤
      (family.stateAtBoxIndex index).clearance.bound / 4 := by
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    (family.clearanceTarget_le_stateAt index)
    (RFAP.ConstructiveFraction.inv_pos_direct
      (show (0 : Coordinate) < 4 by decide)).le

/-- Projective complement gaps supplied by the uniform residual-interior
strip of every displayed winding state. -/
def interiorStripChordalGaps
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient) : List Coordinate :=
  family.states.map fun state =>
    CCL.PersistentCCLInteriorGap.interiorStripChordalGap state.box
      state.clearance.residualInteriorRadius

theorem interiorStripChordalGaps_positive
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient) :
    ∀ gap ∈ family.interiorStripChordalGaps, 0 < gap := by
  intro gap member
  rw [interiorStripChordalGaps, QuotientFreeList.mem_map] at member
  rcases member with ⟨state, _stateMember, rfl⟩
  exact
    CCL.PersistentCCLInteriorGap.interiorStripChordalGap_pos
      state.box state.clearance.residualInteriorRadius_pos

/-- One positive rational projective gap below the uniform interior gap of
every state in the finite family. -/
def interiorGapTarget
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient) : Coordinate :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum
    family.interiorStripChordalGaps

theorem interiorGapTarget_pos
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient) : 0 < family.interiorGapTarget :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_pos _
    family.interiorStripChordalGaps_positive

theorem interiorGapTarget_le_stateAt
    {p : GaussianPolynomial} {ambient : Box}
    (family : WindingFamily p ambient)
    (index : Fin family.boxes.length) :
    family.interiorGapTarget ≤
      CCL.PersistentCCLInteriorGap.interiorStripChordalGap
        (family.stateAtBoxIndex index).box
        (family.stateAtBoxIndex index).clearance.residualInteriorRadius := by
  apply
    CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_le_of_mem
  rw [interiorStripChordalGaps, QuotientFreeList.mem_map]
  refine ⟨family.stateAtBoxIndex index, ?_, rfl⟩
  exact List.get_mem family.states
    ⟨index.val, by
      simpa only [boxes, List.length_map] using index.isLt⟩

/-- One winding state as the complete local owner family for a controller
step on that track. -/
def singleton
    {p : GaussianPolynomial} {ambient : Box}
    (state : WindingOneState p ambient) : WindingFamily p ambient :=
  { states := [state]
    pairwise := QuotientFreeList.pairwise_singleton _ _ }

@[simp] theorem singleton_boxes
    {p : GaussianPolynomial} {ambient : Box}
    (state : WindingOneState p ambient) :
    (singleton state).boxes = [state.box] := rfl

def singletonIndex
    {p : GaussianPolynomial} {ambient : Box}
    (state : WindingOneState p ambient) :
    Fin (singleton state).boxes.length :=
  ⟨0, by simp⟩

@[simp] theorem singleton_stateAtBoxIndex
    {p : GaussianPolynomial} {ambient : Box}
    (state : WindingOneState p ambient) :
    (singleton state).stateAtBoxIndex (singletonIndex state) = state := rfl

/-- The initial states of pairwise-separated tracks form a winding family. -/
def ofTracks
    {p : GaussianPolynomial} {ambient : Box}
    (tracks : List (WindingOneTrack p ambient))
    (pairwise : tracks.Pairwise
      RFAP.ExactIsolation.trackSeparated) :
    WindingFamily p ambient :=
  { states := tracks.map fun track => track.initial
    pairwise := by
      change tracks.Pairwise (fun left right =>
        left.initial.box.Separated right.initial.box) at pairwise
      simpa only [QuotientFreeList.pairwise_map] using pairwise }

/-- The exact-isolation output supplies its complete initial winding family. -/
def ofIsolation
    {p : GaussianPolynomial} {ambient : Box} {count : Nat}
    (output : RFAP.ExactIsolation.Output p ambient count) :
    WindingFamily p ambient :=
  ofTracks output.tracks output.tracks_pairwise

end WindingFamily

/-! ## Finite winding and protected-interior geometry -/

/-- Two winding-one boxes strictly inside the same winding-one container
cannot be positively separated.  Otherwise finite winding additivity would
put winding at least eight in a box whose displayed winding is exactly four.
This compares only supplied finite numerical states. -/
theorem not_separated_inside_winding_one
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (container left right : WindingOneState p ambient)
    (leftInside : left.box.StrictInterior container.box)
    (rightInside : right.box.StrictInterior container.box) :
    ¬left.box.Separated right.box := by
  intro separated
  let region : RFAP.ExactIsolation.ClearRegion p ambient :=
    { box := container.box
      refinesAmbient := container.refinesAmbient
      proper := container.proper
      clearance := container.clearance }
  have atLeastEight :=
    RFAP.Maximality.region_rawWinding_ge_eight_of_separated
      degreeAtLeastTwo squarefree elimination region left right leftInside
        rightInside separated
  have exactlyFour := container.rawWindingFour
  dsimp only [region] at atLeastEight
  rw [exactlyFour] at atLeastEight
  exact (by decide : ¬(8 : Int) ≤ 4) atLeastEight

/-- Pure rational-box geometry used after the winding comparison.  If
`inner` stays more than `margin` from every side of `outer`, and a box lying
within `margin` of `sample` is not separated from `inner`, then the displayed
sample lies in `outer`.  No limiting point is introduced. -/
theorem contains_sample_of_not_separated_of_protected_margin
    {outer inner nearby : Box}
    {sample : RFAP.ConstructiveGaussian.Gaussian}
    {margin : Coordinate}
    (innerLeft : outer.xLower + margin < inner.xLower)
    (innerRight : inner.xUpper < outer.xUpper - margin)
    (innerBottom : outer.yLower + margin < inner.yLower)
    (innerTop : inner.yUpper < outer.yUpper - margin)
    (nearbyLeft : sample.re - margin ≤ nearby.xLower)
    (nearbyRight : nearby.xUpper ≤ sample.re + margin)
    (nearbyBottom : sample.im - margin ≤ nearby.yLower)
    (nearbyTop : nearby.yUpper ≤ sample.im + margin)
    (notSeparated : ¬nearby.Separated inner) :
    outer.Contains sample := by
  have notLeft : ¬nearby.xUpper < inner.xLower :=
    fun separated => notSeparated (Or.inl separated)
  have notRight : ¬inner.xUpper < nearby.xLower :=
    fun separated => notSeparated (Or.inr (Or.inl separated))
  have notBelow : ¬nearby.yUpper < inner.yLower :=
    fun separated => notSeparated (Or.inr (Or.inr (Or.inl separated)))
  have notAbove : ¬inner.yUpper < nearby.yLower :=
    fun separated => notSeparated (Or.inr (Or.inr (Or.inr separated)))
  have leftWithMargin : outer.xLower + margin < sample.re + margin :=
    innerLeft.trans_le ((le_of_not_gt notLeft).trans nearbyRight)
  have rightWithMargin : sample.re - margin < outer.xUpper - margin :=
    nearbyLeft.trans_lt ((le_of_not_gt notRight).trans_lt innerRight)
  have bottomWithMargin : outer.yLower + margin < sample.im + margin :=
    innerBottom.trans_le ((le_of_not_gt notBelow).trans nearbyTop)
  have topWithMargin : sample.im - margin < outer.yUpper - margin :=
    nearbyBottom.trans_lt ((le_of_not_gt notAbove).trans_lt innerTop)
  exact
    ⟨(RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct
        leftWithMargin).le,
      (RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct (by
        simpa only [sub_eq_add_neg] using rightWithMargin)).le,
      (RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct
        bottomWithMargin).le,
      (RFAP.ConstructiveFraction.lt_of_add_lt_add_right_direct (by
        simpa only [sub_eq_add_neg] using topWithMargin)).le⟩

/-- Refine one supplied winding state far enough that the finite protected-
boundary theorem gives a uniform four-radius margin inside it. -/
def protectedRefinement
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) : WindingOneState p ambient :=
  track.refine current
    (RFAP.ProtectedBoundary.protectedBoundaryRadius p current.box
      current.clearance)
    (RFAP.ProtectedBoundary.protectedBoundaryRadius_pos p
      current.clearance current.proper)

theorem protectedRefinement_refines
    {p : GaussianPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) :
    (protectedRefinement track current).box.Refines current.box := by
  exact track.nested current
    (RFAP.ProtectedBoundary.protectedBoundaryRadius p current.box
      current.clearance)
    (RFAP.ProtectedBoundary.protectedBoundaryRadius_pos p
      current.clearance current.proper)

/-- The protected refinement is uniformly away from all four sides of its
input box. -/
theorem protectedRefinement_margin
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient)
    (current : WindingOneState p ambient) :
    let rho :=
      RFAP.ProtectedBoundary.protectedBoundaryRadius p current.box
        current.clearance
    current.box.xLower + 4 * rho < (protectedRefinement track current).box.xLower ∧
      (protectedRefinement track current).box.xUpper < current.box.xUpper - 4 * rho ∧
      current.box.yLower + 4 * rho < (protectedRefinement track current).box.yLower ∧
      (protectedRefinement track current).box.yUpper < current.box.yUpper - 4 * rho := by
  let rho :=
    RFAP.ProtectedBoundary.protectedBoundaryRadius p current.box
      current.clearance
  let positive :=
    RFAP.ProtectedBoundary.protectedBoundaryRadius_pos p
      current.clearance current.proper
  let refined := protectedRefinement track current
  have diagonal : refined.box.diagonalSq ≤ rho ^ 2 := by
    simpa only [refined, protectedRefinement, rho, positive] using
      track.accurate current rho positive
  exact RFAP.ProtectedBoundary.strictly_inside_protectedBoundary
    degreePositive current.clearance current.proper refined.proper
      (protectedRefinement_refines track current) refined.raw.rawWinding_ne
      diagonal

/-- An auxiliary winding-one box close to a displayed rational sample forces
that sample into every supplied later state once both numerical boxes are
known to belong to the same winding-one container.  The later state is
refined only internally to obtain a protected margin; the returned point is
the original rational `sample`, not a limit of the refinements. -/
theorem sample_inside_later_of_auxiliary_winding
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (track : WindingOneTrack p ambient)
    (container later auxiliary : WindingOneState p ambient)
    (laterRefines : later.box.Refines container.box)
    (auxiliaryInside : auxiliary.box.StrictInterior container.box)
    (sample : RFAP.ConstructiveGaussian.Gaussian)
    (auxiliaryLeft :
      sample.re -
          4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
            later.box later.clearance ≤ auxiliary.box.xLower)
    (auxiliaryRight : auxiliary.box.xUpper ≤
      sample.re +
        4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
          later.box later.clearance)
    (auxiliaryBottom :
      sample.im -
          4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
            later.box later.clearance ≤ auxiliary.box.yLower)
    (auxiliaryTop : auxiliary.box.yUpper ≤
      sample.im +
        4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
          later.box later.clearance) :
    later.box.Contains sample := by
  let rho :=
    RFAP.ProtectedBoundary.protectedBoundaryRadius p later.box
      later.clearance
  let rhoPositive :=
    RFAP.ProtectedBoundary.protectedBoundaryRadius_pos p
      later.clearance later.proper
  let deep := protectedRefinement track later
  have deepInsideLater : deep.box.StrictInterior later.box := by
    simpa only [deep, protectedRefinement, rho, rhoPositive] using
      track.strict later rho rhoPositive
  have deepInsideContainer : deep.box.StrictInterior container.box :=
    deepInsideLater.trans_refines laterRefines
  have notSeparated : ¬auxiliary.box.Separated deep.box :=
    not_separated_inside_winding_one degreeAtLeastTwo squarefree elimination
      container auxiliary deep auxiliaryInside deepInsideContainer
  have margins := protectedRefinement_margin
    ((by decide : (0 : Nat) < 2).trans_le degreeAtLeastTwo) track later
  exact contains_sample_of_not_separated_of_protected_margin
    margins.1 margins.2.1 margins.2.2.1 margins.2.2.2
      (by simpa only [rho] using auxiliaryLeft)
      (by simpa only [rho] using auxiliaryRight)
      (by simpa only [rho] using auxiliaryBottom)
      (by simpa only [rho] using auxiliaryTop)
      (by simpa only [deep] using notSeparated)

/-- Concrete specialization for a winding band built from one displayed
rational residual.  If its finite Newton radius is below the later state's
protected margin, its original rational anchor is inside that later state.
This is the numerical persistence bridge; the anchor is never asserted to
be a polynomial root. -/
theorem residual_seed_anchor_inside_later
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (track : WindingOneTrack p ambient)
    (current later : WindingOneState p ambient)
    (laterRefines : later.box.Refines current.box)
    (seed : RFAP.ResidualWinding.Seed squarefree elimination
      (protectedAmbient current))
    (radiusSmall : 3 * seed.radius ≤
      4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
        later.box later.clearance) :
    later.box.Contains seed.source.anchor := by
  let auxiliary := seed.state degreeAtLeastTwo
  have bandBounds := seed.anchor_band_coordinate_bounds
  have left : seed.source.anchor.re -
        4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
          later.box later.clearance ≤ auxiliary.box.xLower := by
    calc
      seed.source.anchor.re -
          4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
            later.box later.clearance ≤
          seed.source.anchor.re - 3 * seed.radius :=
        RFAP.ConstructiveFraction.sub_le_sub_left_direct radiusSmall seed.source.anchor.re
      _ ≤ auxiliary.box.xLower := by
        simpa only [auxiliary, RFAP.ResidualWinding.Seed.state]
          using bandBounds.1
  have right : auxiliary.box.xUpper ≤ seed.source.anchor.re +
        4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
          later.box later.clearance := by
    calc
      auxiliary.box.xUpper ≤ seed.source.anchor.re + 3 * seed.radius := by
        simpa only [auxiliary, RFAP.ResidualWinding.Seed.state]
          using bandBounds.2.1
      _ = 3 * seed.radius + seed.source.anchor.re := by ring1
      _ ≤ 4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
          later.box later.clearance + seed.source.anchor.re :=
        RFAP.ConstructiveFraction.add_le_add_right_direct radiusSmall
          seed.source.anchor.re
      _ = seed.source.anchor.re +
          4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
            later.box later.clearance := by ring1
  have bottom : seed.source.anchor.im -
        4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
          later.box later.clearance ≤ auxiliary.box.yLower := by
    calc
      seed.source.anchor.im -
          4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
            later.box later.clearance ≤
          seed.source.anchor.im - 3 * seed.radius :=
        RFAP.ConstructiveFraction.sub_le_sub_left_direct radiusSmall seed.source.anchor.im
      _ ≤ auxiliary.box.yLower := by
        simpa only [auxiliary, RFAP.ResidualWinding.Seed.state]
          using bandBounds.2.2.1
  have top : auxiliary.box.yUpper ≤ seed.source.anchor.im +
        4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
          later.box later.clearance := by
    calc
      auxiliary.box.yUpper ≤ seed.source.anchor.im + 3 * seed.radius := by
        simpa only [auxiliary, RFAP.ResidualWinding.Seed.state]
          using bandBounds.2.2.2
      _ = 3 * seed.radius + seed.source.anchor.im := by ring1
      _ ≤ 4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
          later.box later.clearance + seed.source.anchor.im :=
        RFAP.ConstructiveFraction.add_le_add_right_direct radiusSmall
          seed.source.anchor.im
      _ = seed.source.anchor.im +
          4 * RFAP.ProtectedBoundary.protectedBoundaryRadius p
            later.box later.clearance := by ring1
  exact sample_inside_later_of_auxiliary_winding degreeAtLeastTwo squarefree
    elimination track current later auxiliary laterRefines
      (seed.state_strict_current degreeAtLeastTwo) seed.source.anchor left
      right bottom top

/-- End-to-end automatic specialization: a displayed rational point strictly
inside the selected container, with residual below the coefficient-computed
target capped by a later state's protected radius, lies in that later state.
All Newton, Taylor, and source-containment budgets are computed internally. -/
theorem strict_residual_sample_inside_later
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (track : WindingOneTrack p ambient)
    (current later : WindingOneState p ambient)
    (laterRefines : later.box.Refines current.box)
    (point : RFAP.ConstructiveGaussian.Gaussian)
    (strict : current.box.StrictContains point)
    (residual : RFAP.ConstructiveGaussian.Gaussian.normSq (p.eval point) <
      RFAP.ResidualWinding.anchoredResidualTarget squarefree
        (protectedAmbient current)
        point
        (RFAP.ProtectedBoundary.protectedBoundaryRadius p
          later.box later.clearance)) :
    later.box.Contains point := by
  let cap :=
    RFAP.ProtectedBoundary.protectedBoundaryRadius p later.box
      later.clearance
  let capPositive :=
    RFAP.ProtectedBoundary.protectedBoundaryRadius_pos p
      later.clearance later.proper
  let seed := RFAP.ResidualWinding.seedOfResidual squarefree
    elimination (protectedAmbient current) point strict capPositive residual
  have radiusLeCap : seed.radius ≤ cap := by
    simpa only [seed, cap, capPositive] using
      RFAP.ResidualWinding.seedOfResidual_radius_le_cap squarefree
        elimination (protectedAmbient current) point strict capPositive residual
  have threeLeFour : (3 : Coordinate) ≤ 4 := by decide
  have threeRadiusLeThreeCap : 3 * seed.radius ≤ 3 * cap :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct radiusLeCap
      (by decide)
  have threeCapLeFourCap : 3 * cap ≤ 4 * cap :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct threeLeFour
      capPositive.le
  have radiusSmall : 3 * seed.radius ≤ 4 * cap :=
    threeRadiusLeThreeCap.trans threeCapLeFourCap
  have contains := residual_seed_anchor_inside_later degreeAtLeastTwo
    squarefree elimination track current later laterRefines seed (by
      simpa only [cap] using radiusSmall)
  simpa only [seed, RFAP.ResidualWinding.seedOfResidual,
    RFAP.ResidualWinding.AnchoredInput.seed,
    RFAP.ResidualWinding.anchoredInputOfResidual,
    RFAP.ResidualWinding.anchoredSquare_anchor] using contains

/-- Point-independent automatic specialization.  Boundary clearance supplies
a uniform interior strip, so the residual target can be computed before the
displayed rational event sample is chosen. -/
theorem uniform_residual_sample_inside_later
    {p : GaussianPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (track : WindingOneTrack p ambient)
    (current later : WindingOneState p ambient)
    (laterRefines : later.box.Refines current.box)
    (point : RFAP.ConstructiveGaussian.Gaussian)
    (contains : current.box.Contains point)
    (residual : RFAP.ConstructiveGaussian.Gaussian.normSq (p.eval point) <
      RFAP.ResidualWinding.uniformAnchoredResidualTarget squarefree
        (protectedAmbient current)
        (RFAP.ProtectedBoundary.protectedBoundaryRadius p
          later.box later.clearance)) :
    later.box.Contains point := by
  let cap :=
    RFAP.ProtectedBoundary.protectedBoundaryRadius p later.box
      later.clearance
  have capPositive : 0 < cap := by
    simpa only [cap] using
      RFAP.ProtectedBoundary.protectedBoundaryRadius_pos p
        later.clearance later.proper
  have ready :=
    RFAP.ResidualWinding.uniform_residual_strict_and_anchored
      squarefree (protectedAmbient current) point contains capPositive (by
        simpa only [cap] using residual)
  exact strict_residual_sample_inside_later degreeAtLeastTwo squarefree
    elimination track current later laterRefines point ready.1 (by
      simpa only [cap] using ready.2)

section Boundary

variable {p : GaussianPolynomial} {ambient : Box}
variable {reference : Mat2} {current : Box}
variable {denominatorMargin : Coordinate}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : CCL.CCLFormula.Atom}
variable {boundary : CurveBoundary p reference current denominatorMargin
  marginPositive atom}

/-- Finite chart/box targets making a denominator-equality profile
projectively closer to `ω` than any point of the corresponding finite winding
box. -/
def poleExclusionTargets
    (family : WindingFamily p ambient) : List Coordinate :=
  (CCL.PersistentCCLProfileBoundaryEvents.boundaryProfileEventFamily
    boundary).flatMap fun parent =>
      (parent.parent.chart.parameterization.weightLower *
        CCL.PersistentCCLInteriorGap.infinityBoxGap current) ^ 2 ::
        family.boxes.map fun targetBox =>
          (parent.parent.chart.parameterization.weightLower *
            CCL.PersistentCCLInteriorGap.infinityBoxGap targetBox) ^ 2

theorem poleExclusionTargets_positive
    (family : WindingFamily p ambient) :
    ∀ target ∈ poleExclusionTargets (boundary := boundary) family,
      0 < target := by
  intro target member
  rw [poleExclusionTargets, QuotientFreeList.mem_flatMap] at member
  rcases member with ⟨parent, _parentMember, targetMember⟩
  rcases List.mem_cons.mp targetMember with rfl | targetMember
  · exact RFAP.ConstructiveFraction.pow_pos_direct
      (RFAP.ConstructiveFraction.mul_pos_direct
        parent.parent.chart.parameterization.weightLowerPositive
        (CCL.PersistentCCLInteriorGap.infinityBoxGap_pos current))
      2
  rw [QuotientFreeList.mem_map] at targetMember
  rcases targetMember with ⟨targetBox, _boxMember, rfl⟩
  exact RFAP.ConstructiveFraction.pow_pos_direct
    (RFAP.ConstructiveFraction.mul_pos_direct
      parent.parent.chart.parameterization.weightLowerPositive
      (CCL.PersistentCCLInteriorGap.infinityBoxGap_pos targetBox))
    2

/-- One positive rational target below every finite chart/box pole-exclusion
target. -/
def poleExclusionTarget
    (family : WindingFamily p ambient) : Coordinate :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum
    (poleExclusionTargets (boundary := boundary) family)

theorem poleExclusionTarget_pos
    (family : WindingFamily p ambient) :
    0 < poleExclusionTarget (boundary := boundary) family :=
  CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_pos _
    (poleExclusionTargets_positive (boundary := boundary) family)

theorem poleExclusionTarget_le
    (family : WindingFamily p ambient)
    (parent : CCL.PersistentCCLProfileBoundaryEvents.BoundaryProfileEventEntry
      boundary)
    (parentMember : parent ∈
      CCL.PersistentCCLProfileBoundaryEvents.boundaryProfileEventFamily
        boundary)
    (index : Fin family.boxes.length) :
    poleExclusionTarget (boundary := boundary) family ≤
      (parent.parent.chart.parameterization.weightLower *
        CCL.PersistentCCLInteriorGap.infinityBoxGap
          (family.boxes.get index)) ^ 2 := by
  apply
    CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_le_of_mem
  rw [poleExclusionTargets, QuotientFreeList.mem_flatMap]
  refine ⟨parent, parentMember, ?_⟩
  exact List.mem_cons_of_mem _ (QuotientFreeList.mem_map.mpr
    ⟨family.boxes.get index, List.get_mem family.boxes index, rfl⟩)

/-- The common pole-exclusion target also covers the boundary's dispatched
box itself, independently of the auxiliary winding family. -/
theorem poleExclusionTarget_le_current
    (family : WindingFamily p ambient)
    (parent : CCL.PersistentCCLProfileBoundaryEvents.BoundaryProfileEventEntry
      boundary)
    (parentMember : parent ∈
      CCL.PersistentCCLProfileBoundaryEvents.boundaryProfileEventFamily
        boundary) :
    poleExclusionTarget (boundary := boundary) family ≤
      (parent.parent.chart.parameterization.weightLower *
        CCL.PersistentCCLInteriorGap.infinityBoxGap current) ^ 2 := by
  apply
    CCL.PersistentCCLRegionOwnership.finitePositiveMinimum_le_of_mem
  rw [poleExclusionTargets, QuotientFreeList.mem_flatMap]
  exact ⟨parent, parentMember, List.mem_cons_self⟩

/-- One target simultaneously below the squarefree derivative threshold, one
quarter of every state clearance, every state's uniform projective interior
gap, and every chart/box pole-exclusion target. -/
def windingTarget
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) : Coordinate :=
  min (RFAP.LocalExtraction.derivativeThreshold squarefree ambient)
    (min (family.clearanceTarget / 4)
      (min family.interiorGapTarget
        (poleExclusionTarget (boundary := boundary) family)))

theorem windingTarget_pos
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    0 < windingTarget (boundary := boundary) squarefree family :=
  lt_min
    (RFAP.LocalExtraction.derivativeThreshold_pos squarefree ambient)
    (lt_min
      (RFAP.ConstructiveFraction.div_pos_direct family.clearanceTarget_pos
        (by decide))
      (lt_min family.interiorGapTarget_pos
        (poleExclusionTarget_pos (boundary := boundary) family)))

theorem windingTarget_le_derivativeThreshold
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    windingTarget (boundary := boundary) squarefree family ≤
      RFAP.LocalExtraction.derivativeThreshold squarefree ambient :=
  min_le_left _ _

theorem windingTarget_le_clearanceQuarter
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    windingTarget (boundary := boundary) squarefree family ≤
      family.clearanceTarget / 4 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem windingTarget_le_interiorGap
    (squarefree : SquarefreeCertificate p)
  (family : WindingFamily p ambient) :
    windingTarget (boundary := boundary) squarefree family ≤
      family.interiorGapTarget :=
  (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))

theorem windingTarget_le_poleExclusion
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    windingTarget (boundary := boundary) squarefree family ≤
      poleExclusionTarget (boundary := boundary) family :=
  (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))

/-- Shared request width specialized to all derivative, strict-interior,
projective-cylinder, and separated-family requirements. -/
def windingRequestWidth
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) : Coordinate :=
  CCL.PersistentCCLProfileRequestFamily.boundaryControlledRequestWidth
    boundary family.boxes family.boxes_pairwise
      (windingTarget (boundary := boundary) squarefree family)

theorem windingRequestWidth_pos
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    0 < windingRequestWidth (boundary := boundary) squarefree family :=
  CCL.PersistentCCLProfileRequestFamily.boundaryControlledRequestWidth_pos
    boundary family.boxes family.boxes_pairwise
      (windingTarget_pos (boundary := boundary) squarefree family)

/-- Complete sibling-preserving profile family at the winding comparison
width. -/
def windingRequestFamily
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    List (CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
      boundary
      (windingRequestWidth (boundary := boundary) squarefree family)) :=
  CCL.PersistentCCLProfileRequestFamily.controlledBoundaryCompleteRequestFamily
    boundary family.boxes family.boxes_pairwise
      (windingTarget (boundary := boundary) squarefree family)

/-- Fully classified complete children before translating box indices back to
winding states. -/
def classifiedWindingRequestFamily
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :=
  CCL.PersistentCCLProfileRequestFamily.classifiedControlledBoundaryFamily
    boundary family.boxes family.boxes_pairwise
      (windingTarget (boundary := boundary) squarefree family)
      (windingTarget_pos (boundary := boundary) squarefree family)

abbrev ClassifiedChild
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :=
  CCL.PersistentCCLProfileRequestFamily.ClassifiedControlledBoundaryChild
    boundary family.boxes family.boxes_pairwise
      (windingTarget (boundary := boundary) squarefree family)
      (windingTarget_pos (boundary := boundary) squarefree family)

/-- Once an initial rational sample selects a winding state with the common
target, every non-pole rational point in that complete retained child remains
inside the same state.  The proof combines the sample's clearance-quarter
residual margin with the child's direct projective diameter bound. -/
theorem controlledChild_inside_owner
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : ClassifiedChild (boundary := boundary) squarefree family)
    (owner :
      CCL.PersistentCCLProfileRequestFamily.ControlledCompleteRequestMeeting
        family.boxes family.boxes_pairwise
          (windingTarget (boundary := boundary) squarefree family)
          classified.entry)
    {parameter : Coordinate}
    (parameterInside :
      classified.entry.child.cell.interval.Contains parameter)
    (denominatorNonzero :
      classified.entry.parent.parent.chart.parameterization.curve.denominatorAt
        parameter ≠ 0) :
    (family.stateAtBoxIndex owner.index).box.Contains
      (classified.entry.parent.parent.chart.parameterization.curve.point
        parameter) := by
  let state := family.stateAtBoxIndex owner.index
  let point := classified.entry.parent.parent.chart.parameterization.curve.point
    owner.parameter
  have pointInside : state.box.Contains point := by
    rw [← family.boxAt_eq owner.index]
    exact owner.pointInside
  have residualSmall : RFAP.ConstructiveGaussian.Gaussian.normSq
      (p.eval point) < state.clearance.bound / 4 :=
    (owner.residual_lt
      (windingTarget_pos (boundary := boundary) squarefree family)).trans_le
      ((windingTarget_le_clearanceQuarter
          (boundary := boundary) squarefree family).trans
        (family.clearanceTarget_quarter_le_stateAt owner.index))
  have margins := state.clearance.residualInteriorMargins pointInside
    residualSmall
  exact
    CCL.PersistentCCLInteriorGap.controlled_event_contains_of_uniform_strip
      (windingTarget_pos (boundary := boundary) squarefree family)
      classified.entry state.box
      state.clearance.residualInteriorRadius_pos owner.parameter
      owner.parameterInside owner.denominatorNonzero pointInside margins.1
      margins.2.1 margins.2.2.1 margins.2.2.2
      ((windingTarget_le_interiorGap
          (boundary := boundary) squarefree family).trans
        (family.interiorGapTarget_le_stateAt owner.index))
      parameterInside denominatorNonzero

/-- If the finite denominator relation of a retained child is the equality
branch, every displayed rational non-pole parameter in that child lies
outside every finite winding box.  This uses only the explicit condition
factorization and a uniform rational residual bound; it does not assert that
the profile factor has a zero. -/
theorem pole_child_excludes_state
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : ClassifiedChild (boundary := boundary) squarefree family)
    (cofactor :
      CCL.CoordinateFactorization.Polynomial)
    (factorization :
      CCL.CoordinateFactorization.Factorization
        (CCL.CurveBoxConditions.denominatorNormSq
          classified.entry.parent.parent.chart.parameterization.curve)
        classified.entry.parent.event.1.profile.factor.polynomial cofactor)
    (relationEq :
      (CCL.PersistentCCLProfileRequestFamily.profileDenominatorRelation
        classified.entry.parent.event.1).relation =
          CCL.CoordinateFactorization.ConditionRelation.equality
            cofactor factorization)
    (index : Fin family.boxes.length)
    (parameter : Coordinate)
    (inside : classified.entry.child.cell.interval.Contains parameter)
    (denominatorNonzero :
      classified.entry.parent.parent.chart.parameterization.curve.denominatorAt
        parameter ≠ 0) :
    ¬(family.stateAtBoxIndex index).box.Contains
      (classified.entry.parent.parent.chart.parameterization.curve.point
        parameter) := by
  let denominatorRelation :=
    CCL.PersistentCCLProfileRequestFamily.profileDenominatorRelation
      classified.entry.parent.event.1
  have relationMember :
      (⟨CCL.CurveBoxConditions.denominatorNormSq
          classified.entry.parent.parent.chart.parameterization.curve,
        CCL.CoordinateFactorization.ConditionRelation.equality
          cofactor factorization⟩ :
        CCL.PersistentCCLConditionProfiles.ProfileRelation
          classified.entry.parent.event.1) ∈
        classified.entry.parent.event.1.profile.relations := by
    have member := denominatorRelation.member
    rw [relationEq] at member
    exact member
  have conditionSmall :=
    classified.entry.equality_condition_eval_sq_lt
      (windingTarget_pos (boundary := boundary) squarefree family)
      (CCL.CurveBoxConditions.denominatorNormSq
        classified.entry.parent.parent.chart.parameterization.curve)
      cofactor factorization relationMember parameter inside
  have poleSmall :
      (CCL.CurveBoxConditions.denominatorNormSq
          classified.entry.parent.parent.chart.parameterization.curve).eval
            parameter ^ 2 <
        (classified.entry.parent.parent.chart.parameterization.weightLower *
          CCL.PersistentCCLInteriorGap.infinityBoxGap
            (family.boxes.get index)) ^ 2 :=
    conditionSmall.trans_le
      ((windingTarget_le_poleExclusion
          (boundary := boundary) squarefree family).trans
        (poleExclusionTarget_le (boundary := boundary) family
          classified.entry.parent classified.entry.parentMember index))
  have excluded :=
    CCL.PersistentCCLInteriorGap.denominator_residual_excludes_box
      classified.entry.parent.parent.chart (family.boxes.get index) parameter
      denominatorNonzero poleSmall
  rw [family.boxAt_eq index] at excluded
  exact excluded

/-- The same finite pole classification excludes the whole dispatched
boundary box.  This is the form consumed by the complete affine resolver. -/
theorem pole_child_excludes_current
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : ClassifiedChild (boundary := boundary) squarefree family)
    (cofactor :
      CCL.CoordinateFactorization.Polynomial)
    (factorization :
      CCL.CoordinateFactorization.Factorization
        (CCL.CurveBoxConditions.denominatorNormSq
          classified.entry.parent.parent.chart.parameterization.curve)
        classified.entry.parent.event.1.profile.factor.polynomial cofactor)
    (relationEq :
      (CCL.PersistentCCLProfileRequestFamily.profileDenominatorRelation
        classified.entry.parent.event.1).relation =
          CCL.CoordinateFactorization.ConditionRelation.equality
            cofactor factorization)
    (parameter : Coordinate)
    (inside : classified.entry.child.cell.interval.Contains parameter)
    (denominatorNonzero :
      classified.entry.parent.parent.chart.parameterization.curve.denominatorAt
        parameter ≠ 0) :
    ¬current.Contains
      (classified.entry.parent.parent.chart.parameterization.curve.point
        parameter) := by
  let denominatorRelation :=
    CCL.PersistentCCLProfileRequestFamily.profileDenominatorRelation
      classified.entry.parent.event.1
  have relationMember :
      (⟨CCL.CurveBoxConditions.denominatorNormSq
          classified.entry.parent.parent.chart.parameterization.curve,
        CCL.CoordinateFactorization.ConditionRelation.equality
          cofactor factorization⟩ :
        CCL.PersistentCCLConditionProfiles.ProfileRelation
          classified.entry.parent.event.1) ∈
        classified.entry.parent.event.1.profile.relations := by
    have member := denominatorRelation.member
    rw [relationEq] at member
    exact member
  have conditionSmall :=
    classified.entry.equality_condition_eval_sq_lt
      (windingTarget_pos (boundary := boundary) squarefree family)
      (CCL.CurveBoxConditions.denominatorNormSq
        classified.entry.parent.parent.chart.parameterization.curve)
      cofactor factorization relationMember parameter inside
  have poleSmall :
      (CCL.CurveBoxConditions.denominatorNormSq
          classified.entry.parent.parent.chart.parameterization.curve).eval
            parameter ^ 2 <
        (classified.entry.parent.parent.chart.parameterization.weightLower *
          CCL.PersistentCCLInteriorGap.infinityBoxGap current) ^ 2 :=
    conditionSmall.trans_le
      ((windingTarget_le_poleExclusion
          (boundary := boundary) squarefree family).trans
        (poleExclusionTarget_le_current (boundary := boundary) family
          classified.entry.parent classified.entry.parentMember))
  exact
    CCL.PersistentCCLInteriorGap.denominator_residual_excludes_box
      classified.entry.parent.parent.chart current parameter
      denominatorNonzero poleSmall

/-! ## Total strict-owner/outside classification on one descendant -/

/-- Descendant width whose original-polynomial residual target is the
candidate winding state's own positive boundary clearance. -/
def strictDescendantRequestWidth
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (windingState : WindingOneState p ambient) : Coordinate :=
  CCL.PersistentCCLProfileRequestFamily.descendantResidualRequestWidth
    entry windingState.box windingState.clearance.bound

theorem strictDescendantRequestWidth_pos
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (windingState : WindingOneState p ambient) :
    0 < strictDescendantRequestWidth entry windingState :=
  CCL.PersistentCCLProfileRequestFamily.descendantResidualRequestWidth_pos
    entry windingState.box windingState.clearance.positive

/-- Executable non-pole sample on the selected descendant at the strict-owner
width. -/
def strictDescendantSample
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (windingState : WindingOneState p ambient) :=
  CCL.PersistentCCLProfileRequestFamily.nonpoleCompleteRequestDescendantSample
    entry (strictDescendantRequestWidth entry windingState)

/-- Total finite result for one retained event branch and one candidate
winding container.  The inside branch is genuinely strict and carries the
actual residual bound; the outside branch retains the failed rational box
membership test. -/
inductive StrictDescendantClassification
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (windingState : WindingOneState p ambient) where
  | inside
      (contains : windingState.box.Contains
        (entry.parent.parent.chart.parameterization.curve.point
          (strictDescendantSample entry windingState).parameter))
      (strict : windingState.box.StrictContains
        (entry.parent.parent.chart.parameterization.curve.point
          (strictDescendantSample entry windingState).parameter))
      (residual : RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (entry.parent.parent.chart.parameterization.curve.point
          (strictDescendantSample entry windingState).parameter)) <
            windingState.clearance.bound)
  | outside
      (proof : ¬windingState.box.Contains
        (entry.parent.parent.chart.parameterization.curve.point
          (strictDescendantSample entry windingState).parameter))

/-- Execute the membership split and use the candidate's finite boundary
clearance to strengthen every owned sample to strict containment. -/
def classifyStrictDescendant
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (windingState : WindingOneState p ambient) :
    StrictDescendantClassification entry windingState := by
  let sample := strictDescendantSample entry windingState
  let point := entry.parent.parent.chart.parameterization.curve.point
    sample.parameter
  by_cases contains : windingState.box.Contains point
  · have residual :=
      CCL.PersistentCCLProfileRequestFamily.descendant_sample_residual_lt
        entry windingState.box windingState.clearance.positive sample contains
    exact .inside contains
      (windingState.clearance.strictContains_of_residual_lt contains residual)
      residual
  · exact .outside contains

/-! ## One shared strict descendant across the finite winding family -/

/-- One descendant width below every state-box residual width for an
arbitrary supplied positive target. -/
def targetedFamilyDescendantRequestWidth
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (target : Coordinate) : Coordinate :=
  CCL.PersistentCCLProfileResidual.profileResidualFamilyRequestWidth
    entry.parent family.boxes target

theorem targetedFamilyDescendantRequestWidth_pos
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    {target : Coordinate} (targetPositive : 0 < target) :
    0 < targetedFamilyDescendantRequestWidth entry family target :=
  CCL.PersistentCCLProfileResidual.profileResidualFamilyRequestWidth_pos
    entry.parent family.boxes targetPositive

/-- The common non-pole rational sample at an arbitrary family-wide residual
target. -/
def targetedFamilyDescendantSample
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (target : Coordinate) :=
  CCL.PersistentCCLProfileRequestFamily.nonpoleCompleteRequestDescendantSample
    entry (targetedFamilyDescendantRequestWidth entry family target)

/-- If the targeted common sample meets a state, its exact original-
polynomial residual is below the caller's common target. -/
theorem targeted_family_descendant_sample_residual_lt
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (index : Fin family.boxes.length)
    {target : Coordinate} (targetPositive : 0 < target)
    (sample :
      CCL.PersistentCCLProfileRequestFamily.NonpoleCompleteRequestDescendantSample
        entry (targetedFamilyDescendantRequestWidth entry family target))
    (contains : (family.stateAtBoxIndex index).box.Contains
      (entry.parent.parent.chart.parameterization.curve.point
        sample.parameter)) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (entry.parent.parent.chart.parameterization.curve.point
          sample.parameter)) < target := by
  let coefficient :=
    CCL.PersistentCCLProfileResidual.BoundaryProfileEventEntry.affineResidualCoefficient
      entry.parent (family.stateAtBoxIndex index).box
  let commonWidth := targetedFamilyDescendantRequestWidth entry family target
  let boxWidth :=
    CCL.PersistentCCLProfileRequestFamily.descendantResidualRequestWidth
      entry (family.stateAtBoxIndex index).box target
  have commonLeBox : commonWidth ≤ boxWidth := by
    simpa only [commonWidth, boxWidth, targetedFamilyDescendantRequestWidth,
      CCL.PersistentCCLProfileRequestFamily.descendantResidualRequestWidth,
      CCL.PersistentCCLProfileResidual.boxResidualRequestWidth,
      CCL.PersistentCCLProfileResidual.BoundaryProfileEventEntry.affineResidualCoefficient,
      coefficient, family.boxAt_eq index] using
      CCL.PersistentCCLProfileResidual.profileResidualFamilyRequestWidth_le_box
        entry.parent family.boxes target index
  have squareOrder : commonWidth ^ 2 ≤ boxWidth ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (targetedFamilyDescendantRequestWidth_pos entry family
        targetPositive).le commonLeBox 2
  have coefficientNonnegative : 0 ≤ coefficient := by
    simpa only [coefficient] using
      CCL.PersistentCCLProfileResidual.BoundaryProfileEventEntry.affineResidualCoefficient_nonneg
        entry.parent (family.stateAtBoxIndex index).box
  have upper := sample.normSq_eval_point_le_of_inside
    (targetedFamilyDescendantRequestWidth_pos entry family targetPositive)
    (family.stateAtBoxIndex index).box contains
  have boxSmall : coefficient * boxWidth ^ 2 < target := by
    simpa only [boxWidth, coefficient,
      CCL.PersistentCCLProfileRequestFamily.descendantResidualRequestWidth,
      CCL.PersistentCCLProfileResidual.BoundaryProfileEventEntry.affineResidualCoefficient]
      using
        CCL.PersistentCCLRegionSeparation.coefficient_mul_shrinkingWidth_sq_lt
          coefficientNonnegative targetPositive
  have commonSmall : coefficient * commonWidth ^ 2 < target :=
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct squareOrder
      coefficientNonnegative).trans_lt boxSmall
  have upperScaled :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (p.eval (entry.parent.parent.chart.parameterization.curve.point
            sample.parameter)) ≤
        coefficient * commonWidth ^ 2 := by
    simpa only [coefficient, commonWidth,
      CCL.PersistentCCLProfileResidual.BoundaryProfileEventEntry.affineResidualCoefficient]
      using upper
  exact upperScaled.trans_lt commonSmall

/-- A single descendant width below every owner-specific residual width when
the common target is the finite minimum of the state boundary clearances. -/
def familyStrictDescendantRequestWidth
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient) : Coordinate :=
  targetedFamilyDescendantRequestWidth entry family family.clearanceTarget

theorem familyStrictDescendantRequestWidth_pos
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient) :
    0 < familyStrictDescendantRequestWidth entry family :=
  targetedFamilyDescendantRequestWidth_pos entry family
    family.clearanceTarget_pos

/-- The one executable non-pole rational sample used for the complete finite
state scan. -/
def familyStrictDescendantSample
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient) :=
  CCL.PersistentCCLProfileRequestFamily.nonpoleCompleteRequestDescendantSample
    entry (familyStrictDescendantRequestWidth entry family)

/-- If the common descendant sample meets one state, its original-polynomial
residual is strictly below that state's own boundary clearance. -/
theorem family_descendant_sample_residual_lt
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (index : Fin family.boxes.length)
    (sample :
      CCL.PersistentCCLProfileRequestFamily.NonpoleCompleteRequestDescendantSample
        entry (familyStrictDescendantRequestWidth entry family))
    (contains : (family.stateAtBoxIndex index).box.Contains
      (entry.parent.parent.chart.parameterization.curve.point
        sample.parameter)) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (entry.parent.parent.chart.parameterization.curve.point
          sample.parameter)) <
      (family.stateAtBoxIndex index).clearance.bound := by
  have belowTarget := targeted_family_descendant_sample_residual_lt entry
    family index family.clearanceTarget_pos sample contains
  exact belowTarget.trans_le (family.clearanceTarget_le_stateAt index)

/-- Total classification of one common rational descendant sample.  The
owned branch identifies one actual winding state and proves strict
containment there; the outside branch rejects the same sample from every
state. -/
inductive FamilyStrictDescendantClassification
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient) where
  | owned
      (index : Fin family.boxes.length)
      (contains : (family.stateAtBoxIndex index).box.Contains
        (entry.parent.parent.chart.parameterization.curve.point
          (familyStrictDescendantSample entry family).parameter))
      (strict : (family.stateAtBoxIndex index).box.StrictContains
        (entry.parent.parent.chart.parameterization.curve.point
          (familyStrictDescendantSample entry family).parameter))
      (residual : RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval (entry.parent.parent.chart.parameterization.curve.point
          (familyStrictDescendantSample entry family).parameter)) <
            (family.stateAtBoxIndex index).clearance.bound)
  | outside
      (proof : ∀ index : Fin family.boxes.length,
        ¬(family.stateAtBoxIndex index).box.Contains
          (entry.parent.parent.chart.parameterization.curve.point
            (familyStrictDescendantSample entry family).parameter))

/-- Execute one finite membership scan for the common descendant sample and
strengthen any owner meeting with its exact clearance comparison. -/
def classifyFamilyStrictDescendant
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient) :
    FamilyStrictDescendantClassification entry family := by
  let sample := familyStrictDescendantSample entry family
  let point := entry.parent.parent.chart.parameterization.curve.point
    sample.parameter
  match found :
      CCL.PersistentCCLRegionOwnership.findContainingBoxIndex
        family.boxes point with
  | some index =>
      have containsBox :=
        CCL.PersistentCCLRegionOwnership.findContainingBoxIndex_sound
          family.boxes point index found
      have contains : (family.stateAtBoxIndex index).box.Contains point := by
        rw [← family.boxAt_eq index]
        exact containsBox
      have residual := family_descendant_sample_residual_lt entry family index
        sample contains
      exact .owned index contains
        ((family.stateAtBoxIndex index).clearance.strictContains_of_residual_lt
          contains residual)
        residual
  | none =>
      have outsideBoxes :=
        CCL.PersistentCCLRegionOwnership.findContainingBoxIndex_none
          family.boxes point found
      exact .outside (by
        intro index contains
        apply outsideBoxes index
        rw [family.boxAt_eq index]
        exact contains)

/-! ## Persistence of an already selected finite owner index -/

/-- Once a displayed sample has selected an owner for one retained child, the
common strict descendant remains strictly in that same indexed state. -/
inductive OwnedChildDescendantResolution
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : ClassifiedChild (boundary := boundary) squarefree family)
    (owner :
      CCL.PersistentCCLProfileRequestFamily.ControlledCompleteRequestMeeting
        family.boxes family.boxes_pairwise
          (windingTarget (boundary := boundary) squarefree family)
          classified.entry) where
  | retained
      (strict : (family.stateAtBoxIndex owner.index).box.StrictContains
        (classified.entry.parent.parent.chart.parameterization.curve.point
          (familyStrictDescendantSample classified.entry family).parameter))
      (residual : RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval
          (classified.entry.parent.parent.chart.parameterization.curve.point
            (familyStrictDescendantSample classified.entry family).parameter)) <
          (family.stateAtBoxIndex owner.index).clearance.bound)

/-- Place the common strict descendant in its already selected owner using
whole-cylinder containment, then strengthen it with the descendant residual
request. -/
theorem resolveOwnedChildDescendant
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : ClassifiedChild (boundary := boundary) squarefree family)
    (owner :
      CCL.PersistentCCLProfileRequestFamily.ControlledCompleteRequestMeeting
        family.boxes family.boxes_pairwise
          (windingTarget (boundary := boundary) squarefree family)
          classified.entry) :
    OwnedChildDescendantResolution squarefree family classified owner := by
  let sample := familyStrictDescendantSample classified.entry family
  let point := classified.entry.parent.parent.chart.parameterization.curve.point
    sample.parameter
  have descendantInside :
      classified.entry.child.cell.interval.Contains sample.parameter :=
    ⟨(classified.entry.child.request_refines
        (familyStrictDescendantRequestWidth classified.entry family)).1.trans
        sample.parameterInside.1,
      sample.parameterInside.2.trans
        (classified.entry.child.request_refines
          (familyStrictDescendantRequestWidth classified.entry family)).2⟩
  have contains : (family.stateAtBoxIndex owner.index).box.Contains point :=
    controlledChild_inside_owner squarefree family classified owner
      descendantInside sample.denominatorNonzero
  have residual := family_descendant_sample_residual_lt classified.entry family
    owner.index sample contains
  exact .retained
    ((family.stateAtBoxIndex owner.index).clearance.strictContains_of_residual_lt
      contains residual)
    residual

/-! ## Uniform residual refinement into a supplied later state -/

/-- One positive target simultaneously below every family clearance and the
point-independent Newton budget for the selected owner and supplied later
state. -/
def persistentDescendantResidualTarget
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) : Coordinate :=
  min family.clearanceTarget
    (RFAP.ResidualWinding.uniformAnchoredResidualTarget squarefree
      (protectedAmbient (family.stateAtBoxIndex ownerIndex))
      (RFAP.ProtectedBoundary.protectedBoundaryRadius p later.box
        later.clearance))

theorem persistentDescendantResidualTarget_pos
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) :
    0 < persistentDescendantResidualTarget squarefree family ownerIndex later :=
  lt_min family.clearanceTarget_pos
    (RFAP.ResidualWinding.uniformAnchoredResidualTarget_pos
      squarefree (protectedAmbient (family.stateAtBoxIndex ownerIndex))
      (RFAP.ProtectedBoundary.protectedBoundaryRadius_pos p
        later.clearance later.proper))

/-- Family-wide descendant width at the selected owner's uniform later-state
Newton target. -/
def persistentDescendantRequestWidth
    {epsilon : Coordinate}
    (squarefree : SquarefreeCertificate p)
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) : Coordinate :=
  targetedFamilyDescendantRequestWidth entry family
    (persistentDescendantResidualTarget squarefree family ownerIndex later)

theorem persistentDescendantRequestWidth_pos
    {epsilon : Coordinate}
    (squarefree : SquarefreeCertificate p)
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) :
    0 < persistentDescendantRequestWidth squarefree entry family ownerIndex later :=
  targetedFamilyDescendantRequestWidth_pos entry family
    (persistentDescendantResidualTarget_pos squarefree family ownerIndex later)

/-- The one non-pole rational event sample at the uniform later-state target. -/
def persistentDescendantSample
    {epsilon : Coordinate}
    (squarefree : SquarefreeCertificate p)
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) :=
  CCL.PersistentCCLProfileRequestFamily.nonpoleCompleteRequestDescendantSample
    entry
      (persistentDescendantRequestWidth squarefree entry family ownerIndex later)

/-- The computed descendant is not merely close to the dispatched atom
boundary: its displayed rational point lies exactly on that boundary.  This
uses only the rational parametrization and its explicit non-pole witness. -/
theorem persistentDescendantSample_onBoundary
    {epsilon : Coordinate}
    (squarefree : SquarefreeCertificate p)
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) :
    atom.form.eval
        (entry.parent.parent.chart.parameterization.curve.point
          (persistentDescendantSample squarefree entry family ownerIndex later).parameter) =
      0 :=
  entry.parent.parent.chart.parameterization.onBoundary
    (persistentDescendantSample squarefree entry family ownerIndex later).parameter
    (persistentDescendantSample squarefree entry family ownerIndex later).denominatorNonzero

/-- Exact weak/strict equality ownership of the retained rational event
sample.  The result concerns the unresolved CCL atom only; it does not claim
that the sample is a zero of the polynomial. -/
inductive PersistentDescendantAtomClassification
    {epsilon : Coordinate}
    (squarefree : SquarefreeCertificate p)
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) where
  | owned
      (holds : atom.Holds
        (entry.parent.parent.chart.parameterization.curve.point
          (persistentDescendantSample squarefree entry family ownerIndex later).parameter))
  | excluded
      (fails : ¬atom.Holds
        (entry.parent.parent.chart.parameterization.curve.point
          (persistentDescendantSample squarefree entry family ownerIndex later).parameter))

/-- Execute the atom's six-way equality convention at the exact rational
boundary sample. -/
def classifyPersistentDescendantAtom
    {epsilon : Coordinate}
    (squarefree : SquarefreeCertificate p)
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) :
    PersistentDescendantAtomClassification squarefree entry family ownerIndex
      later := by
  let point := entry.parent.parent.chart.parameterization.curve.point
    (persistentDescendantSample squarefree entry family ownerIndex later).parameter
  have onBoundary : atom.form.eval point = 0 := by
    simpa only [point] using
      persistentDescendantSample_onBoundary squarefree entry family ownerIndex
        later
  match decision :
      CCL.CCLEqualityOwner.atomEqualityDecision atom with
  | .owned holds =>
      exact .owned
        (CCL.CCLEqualityOwner.atom_holds_of_boundary onBoundary
          holds decision)
  | .excluded fails =>
      exact .excluded
        (CCL.CCLEqualityOwner.atom_not_holds_of_boundary onBoundary
          fails decision)

/-- The selected event's uniform residual refinement supplies a rational
sample in the requested later numerical state, still strictly owned by the
original state. -/
inductive OwnedChildPersistentResolution
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : ClassifiedChild (boundary := boundary) squarefree family)
    (owner :
      CCL.PersistentCCLProfileRequestFamily.ControlledCompleteRequestMeeting
        family.boxes family.boxes_pairwise
          (windingTarget (boundary := boundary) squarefree family)
          classified.entry)
    (later : WindingOneState p ambient) where
  | retained
      (strict : (family.stateAtBoxIndex owner.index).box.StrictContains
        (classified.entry.parent.parent.chart.parameterization.curve.point
          (persistentDescendantSample squarefree classified.entry family
            owner.index later).parameter))
      (residual : RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval
          (classified.entry.parent.parent.chart.parameterization.curve.point
            (persistentDescendantSample squarefree classified.entry family
              owner.index later).parameter)) <
        RFAP.ResidualWinding.uniformAnchoredResidualTarget squarefree
          (protectedAmbient (family.stateAtBoxIndex owner.index))
          (RFAP.ProtectedBoundary.protectedBoundaryRadius p later.box
            later.clearance))
      (laterContains : later.box.Contains
        (classified.entry.parent.parent.chart.parameterization.curve.point
          (persistentDescendantSample squarefree classified.entry family
            owner.index later).parameter))

/-- Execute the uniform residual request inside the whole retained owner
cylinder; the uniform Newton theorem then places the displayed rational sample
in `later`. -/
theorem resolveOwnedChildPersistent
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (family : WindingFamily p ambient)
    (classified : ClassifiedChild (boundary := boundary) squarefree family)
    (owner :
      CCL.PersistentCCLProfileRequestFamily.ControlledCompleteRequestMeeting
        family.boxes family.boxes_pairwise
          (windingTarget (boundary := boundary) squarefree family)
          classified.entry)
    (track : WindingOneTrack p ambient)
    (later : WindingOneState p ambient)
    (laterRefines : later.box.Refines
      (family.stateAtBoxIndex owner.index).box) :
    OwnedChildPersistentResolution squarefree family classified owner later := by
  let target := persistentDescendantResidualTarget squarefree family
    owner.index later
  let sample := persistentDescendantSample squarefree classified.entry family
    owner.index later
  let point := classified.entry.parent.parent.chart.parameterization.curve.point
    sample.parameter
  have descendantInside :
      classified.entry.child.cell.interval.Contains sample.parameter :=
    ⟨(classified.entry.child.request_refines
        (persistentDescendantRequestWidth squarefree classified.entry family
          owner.index later)).1.trans sample.parameterInside.1,
      sample.parameterInside.2.trans
        (classified.entry.child.request_refines
          (persistentDescendantRequestWidth squarefree classified.entry family
            owner.index later)).2⟩
  have contains : (family.stateAtBoxIndex owner.index).box.Contains point :=
    controlledChild_inside_owner squarefree family classified owner
      descendantInside sample.denominatorNonzero
  have residualTarget := targeted_family_descendant_sample_residual_lt
    classified.entry family owner.index
      (persistentDescendantResidualTarget_pos squarefree family owner.index
        later)
      sample contains
  have residualClearance :
      RFAP.ConstructiveGaussian.Gaussian.normSq (p.eval point) <
        (family.stateAtBoxIndex owner.index).clearance.bound :=
    residualTarget.trans_le
      ((min_le_left _ _).trans
        (family.clearanceTarget_le_stateAt owner.index))
  have strict :=
    (family.stateAtBoxIndex owner.index).clearance.strictContains_of_residual_lt
      contains residualClearance
  have residualUniform :
      RFAP.ConstructiveGaussian.Gaussian.normSq (p.eval point) <
        RFAP.ResidualWinding.uniformAnchoredResidualTarget
          squarefree (protectedAmbient (family.stateAtBoxIndex owner.index))
          (RFAP.ProtectedBoundary.protectedBoundaryRadius p
            later.box later.clearance) :=
    residualTarget.trans_le (min_le_right _ _)
  have laterContains := uniform_residual_sample_inside_later degreeAtLeastTwo
    squarefree elimination track (family.stateAtBoxIndex owner.index) later
    laterRefines point contains residualUniform
  exact .retained strict residualUniform laterContains

/-! ## Whole-event affine resolution before rational sample ownership -/

/-- Strong semantic alternative for a finite list of classified children.
The retained branch identifies a profile whose every displayed rational
factor zero lies in the dispatched box.  The outside branch excludes every
rational non-pole parameter of every listed child from that box.  Neither
branch asserts that a factor zero exists. -/
inductive BoundaryAffineResolution
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    List (ClassifiedChild (boundary := boundary) squarefree family) → Type
  | inside
      {values : List
        (ClassifiedChild (boundary := boundary) squarefree family)}
      (child : ClassifiedChild (boundary := boundary) squarefree family)
      (member : child ∈ values)
      (denominatorCertificate :
        RFAP.PathClearance.CoprimeCertificate
          child.entry.parent.event.1.profile.factor.polynomial
          (CCL.CurveBoxConditions.denominatorNormSq
            child.entry.parent.parent.chart.parameterization.curve))
      (denominatorRelationEq :
        (CCL.PersistentCCLProfileRequestFamily.profileDenominatorRelation
          child.entry.parent.event.1).relation =
            CCL.CoordinateFactorization.ConditionRelation.apart
              denominatorCertificate)
      (denominatorLower : ∀ parameter : Coordinate,
        child.entry.child.cell.interval.Contains parameter →
        (CCL.PersistentCCLProfileRequestFamily.profileDenominatorRelation
          child.entry.parent.event.1).apartLower denominatorCertificate ≤
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (child.entry.parent.parent.chart.parameterization.curve.denominatorAt
              parameter))
      (relationsNonnegative : ∀ relation ∈
        child.entry.parent.event.1.profile.relations,
        CCL.PersistentCCLProfileRequestFamily.CompleteRequestLeaf.ConditionNonnegative
          child.entry.child relation)
      (contains : ∀ parameter : Coordinate,
        child.entry.child.cell.interval.Contains parameter →
        child.entry.parent.event.1.profile.factor.polynomial.eval parameter =
          0 →
        child.entry.parent.parent.chart.parameterization.curve.denominatorAt
          parameter ≠ 0 →
        current.Contains
          (child.entry.parent.parent.chart.parameterization.curve.point
            parameter)) :
      BoundaryAffineResolution squarefree family values
  | outside
      {values : List
        (ClassifiedChild (boundary := boundary) squarefree family)}
      (excludes : ∀ child ∈ values, ∀ parameter : Coordinate,
        child.entry.child.cell.interval.Contains parameter →
        child.entry.parent.parent.chart.parameterization.curve.denominatorAt
          parameter ≠ 0 →
        ¬current.Contains
          (child.entry.parent.parent.chart.parameterization.curve.point
            parameter)) :
      BoundaryAffineResolution squarefree family values

/-- Execute the finite first-inside/whole-event-outside scan using each
child's exact affine profile classification. -/
def resolveAffineChildren
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    (values : List
      (ClassifiedChild (boundary := boundary) squarefree family)) →
      BoundaryAffineResolution squarefree family values
  | [] => .outside (by intro child member; simp at member)
  | head :: tail =>
      match head.denominatorClassification with
      | .pole cofactor factorization relationEq =>
          let headExcludes := pole_child_excludes_current squarefree family
            head cofactor factorization relationEq
          match resolveAffineChildren squarefree family tail with
          | .inside child member denominatorCertificate denominatorRelationEq
              denominatorLower relationsNonnegative contains =>
              .inside child (List.mem_cons_of_mem head member)
                denominatorCertificate denominatorRelationEq denominatorLower
                relationsNonnegative contains
          | .outside tailExcludes =>
              .outside (by
                intro child member
                rcases List.mem_cons.mp member with rfl | tailMember
                · exact headExcludes
                · exact tailExcludes child tailMember)
      | .apart denominatorCertificate denominatorRelationEq denominatorLower =>
          match head.boxClassification with
          | .inside relationsNonnegative =>
              .inside head List.mem_cons_self denominatorCertificate
                denominatorRelationEq denominatorLower relationsNonnegative
                (head.entry.child.contains_of_relations_nonnegative
                  relationsNonnegative)
          | .outside relation member negative =>
              let headExcludes :=
                head.entry.child.excludes_of_relation_negative relation member
                  negative
              match resolveAffineChildren squarefree family tail with
              | .inside child member certificate relationEq lower
                  relationsNonnegative contains =>
                  .inside child (List.mem_cons_of_mem head member) certificate
                    relationEq lower relationsNonnegative contains
              | .outside tailExcludes =>
                  .outside (by
                    intro child member
                    rcases List.mem_cons.mp member with rfl | tailMember
                    · exact headExcludes
                    · exact tailExcludes child tailMember)

/-- Strong initial resolution of the complete winding request family.  Its
outside result concerns every rational non-pole point of every retained event
cylinder, rather than one arbitrarily chosen sample per child. -/
def resolveWindingAffineFamily
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    BoundaryAffineResolution squarefree family
      (classifiedWindingRequestFamily (boundary := boundary) squarefree
        family) :=
  resolveAffineChildren squarefree family
    (classifiedWindingRequestFamily (boundary := boundary) squarefree family)

/-! ## Explicit rational sample from the strong affine resolution -/

/-- Strengthening of the semantic affine resolution against a supplied outer
box.  An inside result carries one bounded-search rational sample in the
outer box; the outside result keeps whole-cylinder exclusion.  The inside
constructor does not assert that the profile factor, or `p`, vanishes at the
sample. -/
inductive BoundaryNearBoxResolution
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (outer : Box) (strict : current.StrictInterior outer) :
    List (ClassifiedChild (boundary := boundary) squarefree family) → Type
  | inside
      {values : List
        (ClassifiedChild (boundary := boundary) squarefree family)}
      (child : ClassifiedChild (boundary := boundary) squarefree family)
      (member : child ∈ values)
      (denominatorCertificate :
        RFAP.PathClearance.CoprimeCertificate
          child.entry.parent.event.1.profile.factor.polynomial
          (CCL.CurveBoxConditions.denominatorNormSq
            child.entry.parent.parent.chart.parameterization.curve))
      (denominatorRelationEq :
        (CCL.PersistentCCLProfileRequestFamily.profileDenominatorRelation
          child.entry.parent.event.1).relation =
            CCL.CoordinateFactorization.ConditionRelation.apart
              denominatorCertificate)
      (relationsNonnegative : ∀ relation ∈
        child.entry.parent.event.1.profile.relations,
        CCL.PersistentCCLProfileRequestFamily.CompleteRequestLeaf.ConditionNonnegative
          child.entry.child relation)
      (sampleInside : outer.Contains
        (child.entry.parent.parent.chart.parameterization.curve.point
          (CCL.PersistentCCLProfileRequestFamily.nearBoxDescendantSample
            child.entry
            (CCL.PersistentCCLProfileRequestFamily.profileDenominatorRelation
              child.entry.parent.event.1)
            denominatorCertificate
            (CCL.PersistentCCLInteriorGap.strictBoxGap current
              outer)).parameter)) :
      BoundaryNearBoxResolution squarefree family outer strict values
  | outside
      {values : List
        (ClassifiedChild (boundary := boundary) squarefree family)}
      (excludes : ∀ child ∈ values, ∀ parameter : Coordinate,
        child.entry.child.cell.interval.Contains parameter →
        child.entry.parent.parent.chart.parameterization.curve.denominatorAt
          parameter ≠ 0 →
        ¬current.Contains
          (child.entry.parent.parent.chart.parameterization.curve.point
            parameter)) :
      BoundaryNearBoxResolution squarefree family outer strict values

/-- Convert the strong finite affine scan into either its whole-cylinder
outside proof or an explicit rational sample in any supplied strict outer
box. -/
def BoundaryAffineResolution.toNearBox
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    {values : List
      (ClassifiedChild (boundary := boundary) squarefree family)}
    (resolution : BoundaryAffineResolution squarefree family values)
    (outer : Box) (strict : current.StrictInterior outer) :
    BoundaryNearBoxResolution squarefree family outer strict values := by
  cases resolution with
  | inside child member denominatorCertificate denominatorRelationEq
      denominatorLower relationsNonnegative _contains =>
      let denominator :=
        CCL.PersistentCCLProfileRequestFamily.profileDenominatorRelation
          child.entry.parent.event.1
      let radius :=
        CCL.PersistentCCLInteriorGap.strictBoxGap current outer
      have radiusPositive : 0 < radius := by
        simpa only [radius] using
          CCL.PersistentCCLInteriorGap.strictBoxGap_pos strict
      have near :=
        CCL.PersistentCCLProfileRequestFamily.nearBoxDescendantSample_within_radius
          child.entry denominator denominatorCertificate denominatorLower
            relationsNonnegative radiusPositive
      exact .inside child member denominatorCertificate denominatorRelationEq
        relationsNonnegative
        (CCL.PersistentCCLInteriorGap.contains_of_within_strictBoxGap
          (by simpa only [denominator, radius] using near))
  | outside excludes =>
      exact .outside excludes

/-- Execute the complete winding-family scan and, in its inside branch,
construct the displayed rational near-event sample in a supplied strict outer
box. -/
def resolveWindingNearBoxFamily
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (outer : Box) (strict : current.StrictInterior outer) :
    BoundaryNearBoxResolution squarefree family outer strict
      (classifiedWindingRequestFamily (boundary := boundary) squarefree
        family) :=
  (resolveWindingAffineFamily (boundary := boundary) squarefree family).toNearBox
    squarefree family outer strict

/-- The bounded-search near-box sample lies exactly on the dispatched
Hermitian boundary because every parameter of its rational chart does. -/
theorem nearBoxDescendantSample_onBoundary
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (denominator :
      CCL.PersistentCCLProfileRequestFamily.ProfileDenominatorRelation
        entry.parent.event.1)
    (apart : RFAP.PathClearance.CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (CCL.CurveBoxConditions.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    (radius : Coordinate) :
    atom.form.eval
        (entry.parent.parent.chart.parameterization.curve.point
          (CCL.PersistentCCLProfileRequestFamily.nearBoxDescendantSample
            entry denominator apart radius).parameter) = 0 :=
  entry.parent.parent.chart.parameterization.onBoundary
    (CCL.PersistentCCLProfileRequestFamily.nearBoxDescendantSample
      entry denominator apart radius).parameter
    (CCL.PersistentCCLProfileRequestFamily.nearBoxDescendantSample
      entry denominator apart radius).denominatorNonzero

/-- Exact weak/strict equality ownership of the explicit near-box sample.
This classifies the dispatched CCL atom only and does not classify the sample
as a polynomial root. -/
inductive NearBoxDescendantAtomClassification
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (denominator :
      CCL.PersistentCCLProfileRequestFamily.ProfileDenominatorRelation
        entry.parent.event.1)
    (apart : RFAP.PathClearance.CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (CCL.CurveBoxConditions.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    (radius : Coordinate) where
  | owned
      (holds : atom.Holds
        (entry.parent.parent.chart.parameterization.curve.point
          (CCL.PersistentCCLProfileRequestFamily.nearBoxDescendantSample
            entry denominator apart radius).parameter))
  | excluded
      (fails : ¬atom.Holds
        (entry.parent.parent.chart.parameterization.curve.point
          (CCL.PersistentCCLProfileRequestFamily.nearBoxDescendantSample
            entry denominator apart radius).parameter))

/-- Execute the atom's finite equality convention at the near-box sample. -/
def classifyNearBoxDescendantAtom
    {epsilon : Coordinate}
    (entry :
      CCL.PersistentCCLProfileRequestFamily.BoundaryCompleteRequestEntry
        boundary epsilon)
    (denominator :
      CCL.PersistentCCLProfileRequestFamily.ProfileDenominatorRelation
        entry.parent.event.1)
    (apart : RFAP.PathClearance.CoprimeCertificate
      entry.parent.event.1.profile.factor.polynomial
        (CCL.CurveBoxConditions.denominatorNormSq
          entry.parent.parent.chart.parameterization.curve))
    (radius : Coordinate) :
    NearBoxDescendantAtomClassification entry denominator apart radius := by
  let point := entry.parent.parent.chart.parameterization.curve.point
    (CCL.PersistentCCLProfileRequestFamily.nearBoxDescendantSample
      entry denominator apart radius).parameter
  have onBoundary : atom.form.eval point = 0 := by
    simpa only [point] using
      nearBoxDescendantSample_onBoundary entry denominator apart radius
  match decision :
      CCL.CCLEqualityOwner.atomEqualityDecision atom with
  | .owned holds =>
      exact .owned
        (CCL.CCLEqualityOwner.atom_holds_of_boundary onBoundary
          holds decision)
  | .excluded fails =>
      exact .excluded
        (CCL.CCLEqualityOwner.atom_not_holds_of_boundary onBoundary
          fails decision)

/-- Safe finite comparison of one complete child with the actual winding
states.  The owner branch concerns its displayed rational sample only. -/
inductive ChildComparison
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : ClassifiedChild (boundary := boundary) squarefree family)
    where
  | owned
      (owner :
        CCL.PersistentCCLProfileRequestFamily.ControlledCompleteRequestMeeting
          family.boxes family.boxes_pairwise
            (windingTarget (boundary := boundary) squarefree family)
            classified.entry)
      (residual : RFAP.ConstructiveGaussian.Gaussian.normSq
          (p.eval
            (classified.entry.parent.parent.chart.parameterization.curve.point
              owner.parameter)) <
        RFAP.LocalExtraction.derivativeThreshold squarefree ambient)
      (derivativeNonzero :
        (RFAP.ConstructiveGCD.derivative p).eval
          (classified.entry.parent.parent.chart.parameterization.curve.point
            owner.parameter) ≠ 0)
  | outside (proof : ∀ index : Fin family.boxes.length,
      ¬(family.stateAtBoxIndex index).box.Contains
        (classified.entry.parent.parent.chart.parameterization.curve.point
          classified.sample.parameter))

/-- Translate the computed box classifier to its aligned winding state and
attach the derivative-threshold consequences in the owner branch. -/
def compareChild
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : ClassifiedChild (boundary := boundary) squarefree family) :
    ChildComparison squarefree family classified := by
  cases classified.sampleClassification with
  | meeting owner =>
      exact .owned owner
        ((owner.residual_lt
            (windingTarget_pos (boundary := boundary) squarefree family)).trans_le
          (windingTarget_le_derivativeThreshold
            (boundary := boundary) squarefree family))
        (owner.derivative_ne_zero squarefree
          family.boxAt_refinesAmbient
          (windingTarget_pos (boundary := boundary) squarefree family)
          (windingTarget_le_derivativeThreshold
            (boundary := boundary) squarefree family))
  | outside proof =>
      exact .outside (by
        intro index contained
        apply proof index
        rw [family.boxAt_eq index]
        exact contained)

/-- One classified child together with its safe winding-state comparison. -/
structure ComparedChild
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) where
  classified : ClassifiedChild (boundary := boundary) squarefree family
  comparison : ChildComparison squarefree family classified

/-- Compare every complete retained boundary child with the complete finite
winding family. -/
def compareWindingRequestFamily
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    List (ComparedChild (boundary := boundary) squarefree family) :=
  (classifiedWindingRequestFamily (boundary := boundary) squarefree family).map
    fun classified =>
      { classified := classified
        comparison := compareChild squarefree family classified }

/-- The displayed rational sample of one classified child is outside every
state in the winding family. -/
def SampleOutsideAllStates
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : ClassifiedChild (boundary := boundary) squarefree family) :
    Prop :=
  ∀ index : Fin family.boxes.length,
    ¬(family.stateAtBoxIndex index).box.Contains
      (classified.entry.parent.parent.chart.parameterization.curve.point
        classified.sample.parameter)

/-- Result of a complete finite scan of the child samples.  The first branch
retains a displayed sample owned by one state; the second proves that every
displayed sample in the list is outside every state. -/
inductive FamilySampleResolution
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    List (ComparedChild (boundary := boundary) squarefree family) → Type
  | owned
      {values : List (ComparedChild (boundary := boundary) squarefree family)}
      (child : ComparedChild (boundary := boundary) squarefree family)
      (member : child ∈ values)
      (owner :
        CCL.PersistentCCLProfileRequestFamily.ControlledCompleteRequestMeeting
          family.boxes family.boxes_pairwise
            (windingTarget (boundary := boundary) squarefree family)
            child.classified.entry)
      (residual : RFAP.ConstructiveGaussian.Gaussian.normSq
          (p.eval
            (child.classified.entry.parent.parent.chart.parameterization.curve.point
              owner.parameter)) <
        RFAP.LocalExtraction.derivativeThreshold squarefree ambient)
      (derivativeNonzero :
        (RFAP.ConstructiveGCD.derivative p).eval
          (child.classified.entry.parent.parent.chart.parameterization.curve.point
            owner.parameter) ≠ 0) :
      FamilySampleResolution squarefree family values
  | outside
      {values : List (ComparedChild (boundary := boundary) squarefree family)}
      (proof : ∀ child ∈ values,
        SampleOutsideAllStates squarefree family child.classified) :
      FamilySampleResolution squarefree family values

/-- Execute the finite first-owned/outside-all scan over already compared
children. -/
def resolveComparedChildren
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    (values : List (ComparedChild (boundary := boundary) squarefree family)) →
      FamilySampleResolution squarefree family values
  | [] => .outside (by intro child member; simp at member)
  | head :: tail =>
      match head.comparison with
      | .owned owner residual derivativeNonzero =>
          .owned head List.mem_cons_self owner residual derivativeNonzero
      | .outside headOutside =>
          match resolveComparedChildren squarefree family tail with
          | .owned child member owner residual derivativeNonzero =>
              .owned child (List.mem_cons_of_mem head member) owner residual
                derivativeNonzero
          | .outside tailOutside =>
              .outside (by
                intro child member
                rcases List.mem_cons.mp member with rfl | tailMember
                · exact headOutside
                · exact tailOutside child tailMember)

/-- Complete executable winding-state comparison for one dispatched curve
boundary at the squarefree derivative threshold. -/
def resolveWindingRequestFamily
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    FamilySampleResolution squarefree family
      (compareWindingRequestFamily (boundary := boundary) squarefree family) :=
  resolveComparedChildren squarefree family
    (compareWindingRequestFamily (boundary := boundary) squarefree family)

/-! ## Boundary-family owner/descendant resolution -/

/-- Complete finite result after selecting the first initially owned child
and following that very child to the one common strict descendant.  `retained`
keeps the original owner index; `initiallyOutside` records that no initial
sample selected an owner. -/
inductive FamilyDescendantResolution
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) where
  | retained
      (child : ComparedChild (boundary := boundary) squarefree family)
      (member : child ∈
        compareWindingRequestFamily (boundary := boundary) squarefree family)
      (owner :
        CCL.PersistentCCLProfileRequestFamily.ControlledCompleteRequestMeeting
          family.boxes family.boxes_pairwise
            (windingTarget (boundary := boundary) squarefree family)
            child.classified.entry)
      (initialResidual : RFAP.ConstructiveGaussian.Gaussian.normSq
          (p.eval
            (child.classified.entry.parent.parent.chart.parameterization.curve.point
              owner.parameter)) <
        RFAP.LocalExtraction.derivativeThreshold squarefree ambient)
      (derivativeNonzero :
        (RFAP.ConstructiveGCD.derivative p).eval
          (child.classified.entry.parent.parent.chart.parameterization.curve.point
            owner.parameter) ≠ 0)
      (strict : (family.stateAtBoxIndex owner.index).box.StrictContains
        (child.classified.entry.parent.parent.chart.parameterization.curve.point
          (familyStrictDescendantSample child.classified.entry family).parameter))
      (descendantResidual : RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval
          (child.classified.entry.parent.parent.chart.parameterization.curve.point
            (familyStrictDescendantSample child.classified.entry family).parameter)) <
          (family.stateAtBoxIndex owner.index).clearance.bound)
  | initiallyOutside
      (proof : ∀ child ∈
        compareWindingRequestFamily (boundary := boundary) squarefree family,
          SampleOutsideAllStates squarefree family child.classified)

/-- Execute the initial first-owner scan and, only when it finds an owner,
follow the same retained child through the shared strict-descendant scan. -/
def resolveFamilyDescendant
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    FamilyDescendantResolution (boundary := boundary) squarefree family := by
  match resolveWindingRequestFamily (boundary := boundary) squarefree family with
  | .outside proof => exact .initiallyOutside proof
  | .owned child member owner initialResidual derivativeNonzero =>
      match resolveOwnedChildDescendant squarefree family child.classified owner with
      | .retained strict descendantResidual =>
          exact .retained child member owner initialResidual derivativeNonzero
            strict descendantResidual

/-! ## Persistent later-state provider -/

/-- Finite numerical data supplying one later refinement and one executable
track interface for every state in the winding family. -/
structure LaterStateProvider
    (family : WindingFamily p ambient) where
  trackAt : (index : Fin family.boxes.length) → WindingOneTrack p ambient
  laterAt : (index : Fin family.boxes.length) → WindingOneState p ambient
  laterRefines : ∀ index,
    (laterAt index).box.Refines (family.stateAtBoxIndex index).box

/-- Boundary-wide result at the selected owner's point-independent Newton
target.  The retained branch contains the computed rational sample in the
provider's actual later state; the other branch records that the initial
finite scan selected no owner. -/
inductive FamilyPersistentResolution
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (provider : LaterStateProvider family) where
  | retained
      (child : ComparedChild (boundary := boundary) squarefree family)
      (member : child ∈
        compareWindingRequestFamily (boundary := boundary) squarefree family)
      (owner :
        CCL.PersistentCCLProfileRequestFamily.ControlledCompleteRequestMeeting
          family.boxes family.boxes_pairwise
            (windingTarget (boundary := boundary) squarefree family)
            child.classified.entry)
      (initialResidual : RFAP.ConstructiveGaussian.Gaussian.normSq
          (p.eval
            (child.classified.entry.parent.parent.chart.parameterization.curve.point
              owner.parameter)) <
        RFAP.LocalExtraction.derivativeThreshold squarefree ambient)
      (derivativeNonzero :
        (RFAP.ConstructiveGCD.derivative p).eval
          (child.classified.entry.parent.parent.chart.parameterization.curve.point
            owner.parameter) ≠ 0)
      (strict : (family.stateAtBoxIndex owner.index).box.StrictContains
        (child.classified.entry.parent.parent.chart.parameterization.curve.point
          (persistentDescendantSample squarefree child.classified.entry family
            owner.index (provider.laterAt owner.index)).parameter))
      (residual : RFAP.ConstructiveGaussian.Gaussian.normSq
        (p.eval
          (child.classified.entry.parent.parent.chart.parameterization.curve.point
            (persistentDescendantSample squarefree child.classified.entry family
              owner.index (provider.laterAt owner.index)).parameter)) <
        RFAP.ResidualWinding.uniformAnchoredResidualTarget squarefree
          (protectedAmbient (family.stateAtBoxIndex owner.index))
          (RFAP.ProtectedBoundary.protectedBoundaryRadius p
            (provider.laterAt owner.index).box
            (provider.laterAt owner.index).clearance))
      (laterContains : (provider.laterAt owner.index).box.Contains
        (child.classified.entry.parent.parent.chart.parameterization.curve.point
          (persistentDescendantSample squarefree child.classified.entry family
            owner.index (provider.laterAt owner.index)).parameter))
  | initiallyOutside
      (proof : ∀ child ∈
        compareWindingRequestFamily (boundary := boundary) squarefree family,
          SampleOutsideAllStates squarefree family child.classified)

/-- Execute the first-owner scan and request the selected child's residual at
the later state supplied for that exact owner index. -/
def resolveFamilyPersistent
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (family : WindingFamily p ambient)
    (provider : LaterStateProvider family) :
    FamilyPersistentResolution (boundary := boundary) squarefree family
      provider := by
  match resolveWindingRequestFamily (boundary := boundary) squarefree family with
  | .outside proof => exact .initiallyOutside proof
  | .owned child member owner initialResidual derivativeNonzero =>
      match resolveOwnedChildPersistent degreeAtLeastTwo squarefree elimination
          family child.classified owner (provider.trackAt owner.index)
          (provider.laterAt owner.index) (provider.laterRefines owner.index) with
      | .retained strict residual laterContains =>
          exact .retained child member owner initialResidual derivativeNonzero
            strict residual laterContains

end Boundary

end CCL.PersistentCCLWindingOwnership
