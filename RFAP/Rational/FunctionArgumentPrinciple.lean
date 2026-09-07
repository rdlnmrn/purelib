import mathlib.Tactic.QuotientFreeOmega
import RFAP.Isolation.BoxFTA
import RFAP.Polynomial.CoprimeBounds
import RFAP.Rational.OuterWinding
import RFAP.Rational.SignedMultiplicity

/-!
# Finite constructive rational-function argument principle

This paper-facing addendum combines executable gcd cancellation, the
polynomial box theorem, quantitative coprime separation, and the quotient
winding law.  The first public result below is the higher-degree squarefree
core.  It returns the numerator and denominator track families without
copying the polynomial isolation algorithm.
-/

namespace RFAP.RationalFunctionArgumentPrinciple

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev SquarefreeCertificate :=
  RFAP.Squarefree.SquarefreeCertificate
abbrev WindingOneState :=
  RFAP.ShrinkingTrack.WindingOneState
abbrev WindingOneTrack :=
  RFAP.ShrinkingTrack.WindingOneTrack

open RFAP.Winding

/-- Input for the non-linear squarefree core after executable cancellation.
The linear and constant branches are kept separate in the total result. -/
structure HigherSquarefreeInput
    (numerator denominator : GaussianPolynomial) where
  reduction : ReducedPair numerator denominator
  numeratorSquarefree : SquarefreeCertificate reduction.numeratorReduced
  denominatorSquarefree : SquarefreeCertificate reduction.denominatorReduced
  numeratorDegreeAtLeastTwo : 2 ≤ reduction.numeratorReduced.natDegree
  denominatorDegreeAtLeastTwo : 2 ≤ reduction.denominatorReduced.natDegree

namespace HigherSquarefreeInput

theorem numeratorDegreePositive
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator) :
    0 < input.reduction.numeratorReduced.natDegree :=
  (show (0 : Nat) < 2 by decide).trans_le
    input.numeratorDegreeAtLeastTwo

theorem denominatorDegreePositive
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator) :
    0 < input.reduction.denominatorReduced.natDegree :=
  (show (0 : Nat) < 2 by decide).trans_le
    input.denominatorDegreeAtLeastTwo

def numeratorBoxes
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator) :
    RFAP.BoxFTA.Result input.reduction.numeratorReduced :=
  RFAP.BoxFTA.prove
    { squarefree := input.numeratorSquarefree
      degreeAtLeastTwo := input.numeratorDegreeAtLeastTwo }

def denominatorBoxes
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator) :
    RFAP.BoxFTA.Result input.reduction.denominatorReduced :=
  RFAP.BoxFTA.prove
    { squarefree := input.denominatorSquarefree
      degreeAtLeastTwo := input.denominatorDegreeAtLeastTwo }

def numeratorTrack
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.numeratorReduced.natDegree) :
    WindingOneTrack input.reduction.numeratorReduced
      (RFAP.GlobalWinding.largeSquareBox
        input.reduction.numeratorReduced) :=
  input.numeratorBoxes.isolation.trackAt index

def denominatorTrack
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.denominatorReduced.natDegree) :
    WindingOneTrack input.reduction.denominatorReduced
      (RFAP.GlobalWinding.largeSquareBox
        input.reduction.denominatorReduced) :=
  input.denominatorBoxes.isolation.trackAt index

/-- Forget only the squarefree and degree-at-least-two data when invoking the
general nonzero outer-square theorem. -/
def nonzeroInput
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator) :
    NonzeroReducedInput numerator denominator where
  reduction := input.reduction
  numeratorReducedNonzero :=
    RFAP.GlobalWinding.isZero_false_of_natDegree_pos
      input.numeratorDegreePositive

abbrev commonOuterRadius
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator) : Coordinate :=
  input.nonzeroInput.outerRadius

abbrev commonOuterBox
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator) : Box :=
  input.nonzeroInput.outerBox

/-- Higher squarefree specialization of the general outer degree-difference
law. -/
theorem commonOuter_rationalWinding_eq_degreeDifference
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator) :
    RFAP.RationalWinding.rationalQuadrupledWinding
        input.reduction.numeratorReduced input.reduction.denominatorReduced
        input.commonOuterBox =
      (4 : Int) * input.reduction.numeratorReduced.natDegree -
        (4 : Int) * input.reduction.denominatorReduced.natDegree :=
  input.nonzeroInput.outer_rationalWinding_eq_degreeDifference

def numeratorState
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.numeratorReduced.natDegree) :
    WindingOneState input.reduction.numeratorReduced
      (RFAP.GlobalWinding.largeSquareBox
        input.reduction.numeratorReduced) :=
  let track := input.numeratorTrack index
  RFAP.CoprimeBounds.protectedState input.reduction.coprime
    track track.initial

def denominatorState
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.denominatorReduced.natDegree) :
    WindingOneState input.reduction.denominatorReduced
      (RFAP.GlobalWinding.largeSquareBox
        input.reduction.denominatorReduced) :=
  let track := input.denominatorTrack index
  let symmetric :=
    RFAP.SquarefreeFactors.CoprimeCertificate.symm
      input.reduction.coprime
  RFAP.CoprimeBounds.protectedState symmetric track track.initial

def numeratorState_denominatorClearance
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.numeratorReduced.natDegree) :
    RFAP.BoxClearance.BoundaryClearance
      input.reduction.denominatorReduced (input.numeratorState index).box := by
  let track := input.numeratorTrack index
  exact RFAP.CoprimeBounds.protectedState_rightBoundaryClearance
    input.numeratorDegreePositive input.reduction.coprime
    track track.initial

def denominatorState_numeratorClearance
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.denominatorReduced.natDegree) :
    RFAP.BoxClearance.BoundaryClearance
      input.reduction.numeratorReduced (input.denominatorState index).box := by
  let track := input.denominatorTrack index
  let symmetric :=
    RFAP.SquarefreeFactors.CoprimeCertificate.symm
      input.reduction.coprime
  exact RFAP.CoprimeBounds.protectedState_rightBoundaryClearance
    input.denominatorDegreePositive symmetric track track.initial

/-- Every numerator track has rational winding `+1`, represented in the
repository's raw normalization as `+4`. -/
theorem numeratorState_rationalWinding
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.numeratorReduced.natDegree) :
    RFAP.RationalWinding.rationalQuadrupledWinding
      input.reduction.numeratorReduced input.reduction.denominatorReduced
      (input.numeratorState index).box = 4 := by
  let track := input.numeratorTrack index
  let state := input.numeratorState index
  have denominatorZero :=
    RFAP.CoprimeBounds.protectedState_rightWinding_zero
      input.numeratorDegreePositive
      input.denominatorDegreePositive input.reduction.coprime
      track track.initial
  have quotient :=
    RFAP.RationalWinding.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      input.reduction.numeratorReduced input.reduction.denominatorReduced
      state.box state.proper state.clearance
      (input.numeratorState_denominatorClearance index)
  have denominatorZero' :
      quadrupledBoxWinding input.reduction.denominatorReduced state.box = 0 := by
    simpa only [state, numeratorState] using denominatorZero
  rw [quotient, state.rawWindingFour, denominatorZero']
  ring1

/-- Every denominator track has rational winding `-1`, represented as raw
winding `-4`. -/
theorem denominatorState_rationalWinding
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator)
    (index : Fin input.reduction.denominatorReduced.natDegree) :
    RFAP.RationalWinding.rationalQuadrupledWinding
      input.reduction.numeratorReduced input.reduction.denominatorReduced
      (input.denominatorState index).box = -4 := by
  let track := input.denominatorTrack index
  let state := input.denominatorState index
  let symmetric :=
    RFAP.SquarefreeFactors.CoprimeCertificate.symm
      input.reduction.coprime
  have numeratorZero :=
    RFAP.CoprimeBounds.protectedState_rightWinding_zero
      input.denominatorDegreePositive
      input.numeratorDegreePositive symmetric track track.initial
  have quotient :=
    RFAP.RationalWinding.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      input.reduction.numeratorReduced input.reduction.denominatorReduced
      state.box state.proper
      (input.denominatorState_numeratorClearance index) state.clearance
  have numeratorZero' :
      quadrupledBoxWinding input.reduction.numeratorReduced state.box = 0 := by
    simpa only [state, denominatorState] using numeratorZero
  rw [quotient, numeratorZero', state.rawWindingFour]
  ring1

/-- A denominator observation refined below the explicit margin carried by
one numerator state.  Pair-dependent observations are sufficient to witness
separation of finite tracks; subsequent refinements preserve the gap. -/
def denominatorCrossState
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator)
    (_numeratorIndex : Fin input.reduction.numeratorReduced.natDegree)
    (denominatorIndex : Fin input.reduction.denominatorReduced.natDegree) :
    WindingOneState input.reduction.denominatorReduced
      (RFAP.GlobalWinding.largeSquareBox
        input.reduction.denominatorReduced) :=
  let track := input.denominatorTrack denominatorIndex
  let margin := RFAP.CoprimeBounds.rightMargin
    input.reduction.coprime
    (RFAP.GlobalWinding.largeSquareBox
      input.reduction.numeratorReduced)
  track.refine track.initial
    (RFAP.CoprimeBounds.uniformResidualRadius
      input.reduction.denominatorReduced
      (RFAP.GlobalWinding.largeSquareBox
        input.reduction.denominatorReduced) margin)
    (RFAP.CoprimeBounds.uniformResidualRadius_pos
      input.reduction.denominatorReduced
      (RFAP.GlobalWinding.largeSquareBox
        input.reduction.denominatorReduced)
      (RFAP.CoprimeBounds.rightMargin_pos input.reduction.coprime
        (RFAP.GlobalWinding.largeSquareBox
          input.reduction.numeratorReduced)))

/-- Numerator and denominator tracks are constructively cross-separated by
explicit finite refinements derived from their reduced Bézout certificate. -/
theorem crossSeparated
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator)
    (numeratorIndex : Fin input.reduction.numeratorReduced.natDegree)
    (denominatorIndex : Fin input.reduction.denominatorReduced.natDegree) :
    (input.numeratorState numeratorIndex).box.Separated
      (input.denominatorCrossState numeratorIndex denominatorIndex).box := by
  let numeratorTrack := input.numeratorTrack numeratorIndex
  let denominatorTrack := input.denominatorTrack denominatorIndex
  exact
    RFAP.CoprimeBounds.protectedState_separated_uniformlySmallState
      input.numeratorDegreePositive
      input.denominatorDegreePositive input.reduction.coprime
      numeratorTrack numeratorTrack.initial denominatorTrack
      denominatorTrack.initial

end HigherSquarefreeInput

/-- Paper-facing higher-degree squarefree RFAP result.  All fields are
computed from the one input record; no second isolation implementation is
introduced. -/
structure HigherSquarefreeResult
    (numerator denominator : GaussianPolynomial) where
  input : HigherSquarefreeInput numerator denominator

def proveHigherSquarefree
    {numerator denominator : GaussianPolynomial}
    (input : HigherSquarefreeInput numerator denominator) :
    HigherSquarefreeResult numerator denominator :=
  ⟨input⟩

/-! ## Total squarefree specialization -/

/-- One orientation of a nonzero squarefree reduced cofactor against its
coprime opposite cofactor. -/
structure SquarefreeSideInput
    (source opposite : GaussianPolynomial) where
  sourceSquarefree : SquarefreeCertificate source
  sourceNonzero : source.isZero = false
  oppositeNonzero : opposite.isZero = false
  sourceOppositeCoprime :
    RFAP.Squarefree.CoprimeCertificate source opposite

/-- A squarefree side has no sites when constant, one exact displayed
Gaussian-rational site when linear, or a degree-indexed shrinking family in
higher degree. -/
inductive SquarefreeObservation
    {source opposite : GaussianPolynomial}
    (input : SquarefreeSideInput source opposite) : Type where
  | constant (degreeZero : source.natDegree = 0)
  | exact
      (root : RFAP.BoxFTA.ExactRoot source)
      (degreeOne : source.natDegree = 1)
      (oppositeAtRoot : opposite.eval root.point ≠ 0)
  | higher
      (boxes : RFAP.BoxFTA.Result source)
      (degreeAtLeastTwo : 2 ≤ source.natDegree)

namespace SquarefreeSideInput

def observe
    {source opposite : GaussianPolynomial}
    (input : SquarefreeSideInput source opposite) :
    SquarefreeObservation input := by
  by_cases degreeZero : source.natDegree = 0
  · exact .constant degreeZero
  · have degreePositive : 0 < source.natDegree :=
      Nat.pos_of_ne_zero degreeZero
    cases RFAP.BoxFTA.provePositive
        { squarefree := input.sourceSquarefree
          degreePositive := degreePositive } with
    | linear root degreeOne =>
        have alternative := input.sourceOppositeCoprime.eval_ne_zero
          root.point
        have oppositeAtRoot : opposite.eval root.point ≠ 0 := by
          rcases alternative with sourceNonzero | oppositeNonzero
          · exact (sourceNonzero root.root).elim
          · exact oppositeNonzero
        exact .exact root degreeOne oppositeAtRoot
    | higher boxes degreeAtLeastTwo =>
        exact .higher boxes degreeAtLeastTwo

def trackState
    {source opposite : GaussianPolynomial}
    (input : SquarefreeSideInput source opposite)
    (boxes : RFAP.BoxFTA.Result source)
    (index : Fin source.natDegree) :
    WindingOneState source
      (RFAP.GlobalWinding.largeSquareBox source) :=
  let track := boxes.isolation.trackAt index
  RFAP.CoprimeBounds.protectedState
    input.sourceOppositeCoprime track track.initial

def trackOppositeClearance
    {source opposite : GaussianPolynomial}
    (input : SquarefreeSideInput source opposite)
    (boxes : RFAP.BoxFTA.Result source)
    (index : Fin source.natDegree) :
    RFAP.BoxClearance.BoundaryClearance opposite
      (input.trackState boxes index).box := by
  let track := boxes.isolation.trackAt index
  exact RFAP.CoprimeBounds.protectedState_rightBoundaryClearance
    index.pos
    input.sourceOppositeCoprime track track.initial

theorem trackOppositeWinding_zero
    {source opposite : GaussianPolynomial}
    (input : SquarefreeSideInput source opposite)
    (boxes : RFAP.BoxFTA.Result source)
    (index : Fin source.natDegree) :
    quadrupledBoxWinding opposite (input.trackState boxes index).box = 0 := by
  let track := boxes.isolation.trackAt index
  have zero :=
    RFAP.CoprimeBounds.protectedStateAt_rightWinding_zero_of_nonzero
      index.pos
      input.oppositeNonzero input.sourceOppositeCoprime track track.initial
      (RFAP.CoprimeBounds.protectionRadius_pos
        input.sourceOppositeCoprime
        (RFAP.GlobalWinding.largeSquareBox source)) le_rfl
  simpa only [trackState,
    RFAP.CoprimeBounds.protectedState,
    RFAP.CoprimeBounds.protectedStateAt] using zero

/-- Every higher squarefree source site has ordinary quotient winding `+1`. -/
theorem trackBoxWinding
    {source opposite : GaussianPolynomial}
    (input : SquarefreeSideInput source opposite)
    (boxes : RFAP.BoxFTA.Result source)
    (index : Fin source.natDegree) :
    RFAP.RationalWinding.rationalBoxWinding source opposite
      (input.trackState boxes index).box = 1 := by
  apply RFAP.RationalWinding.rationalBoxWinding_eq_of_quadrupled_eq_four_mul
  let state := input.trackState boxes index
  have quotient :=
    RFAP.RationalWinding.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      source opposite state.box state.proper state.clearance
      (input.trackOppositeClearance boxes index)
  have oppositeZero : quadrupledBoxWinding opposite state.box = 0 := by
    simpa only [state] using input.trackOppositeWinding_zero boxes index
  rw [quotient, state.rawWindingFour, oppositeZero]
  ring1

/-- Reversing the quotient makes every higher squarefree source site a pole
of ordinary winding `-1`. -/
theorem trackPoleBoxWinding
    {source opposite : GaussianPolynomial}
    (input : SquarefreeSideInput source opposite)
    (boxes : RFAP.BoxFTA.Result source)
    (index : Fin source.natDegree) :
    RFAP.RationalWinding.rationalBoxWinding opposite source
      (input.trackState boxes index).box = -1 := by
  apply RFAP.RationalWinding.rationalBoxWinding_eq_of_quadrupled_eq_four_mul
  let state := input.trackState boxes index
  have quotient :=
    RFAP.RationalWinding.rationalQuadrupledWinding_eq_sub_of_boundaryClearances
      opposite source state.box state.proper
      (input.trackOppositeClearance boxes index) state.clearance
  have oppositeZero : quadrupledBoxWinding opposite state.box = 0 := by
    simpa only [state] using input.trackOppositeWinding_zero boxes index
  rw [quotient, oppositeZero, state.rawWindingFour]
  ring1

end SquarefreeSideInput

namespace SquarefreeObservation

/-- Number of distinct squarefree sites represented by one side. -/
def siteCount
    {source opposite : GaussianPolynomial}
    {input : SquarefreeSideInput source opposite} :
    SquarefreeObservation input → Nat
  | .constant _ => 0
  | .exact _ _ _ => 1
  | .higher boxes _ => boxes.isolation.tracks.length

theorem siteCount_eq_natDegree
    {source opposite : GaussianPolynomial}
    {input : SquarefreeSideInput source opposite}
    (observation : SquarefreeObservation input) :
    observation.siteCount = source.natDegree := by
  cases observation with
  | constant degreeZero => exact degreeZero.symm
  | exact _ degreeOne _ => exact degreeOne.symm
  | higher boxes _ => exact boxes.isolation.tracks_length

/-- Pairwise separation within one squarefree side. -/
def InternallySeparated
    {source opposite : GaussianPolynomial}
    {input : SquarefreeSideInput source opposite}
    (observation : SquarefreeObservation input) : Type :=
  match observation with
  | .constant _ => PUnit
  | .exact _ _ _ => PUnit
  | .higher boxes _ =>
      PLift (∀ left right : Fin source.natDegree, left ≠ right →
        (boxes.isolation.trackAt left).initial.box.Separated
          (boxes.isolation.trackAt right).initial.box)

def internallySeparated
    {source opposite : GaussianPolynomial}
    {input : SquarefreeSideInput source opposite}
    (observation : SquarefreeObservation input) :
    observation.InternallySeparated := by
  cases observation with
  | constant => exact PUnit.unit
  | exact => exact PUnit.unit
  | higher boxes => exact ⟨boxes.isolation.trackAt_pairwiseSeparated⟩

/-- Atomic completeness mirrors the general multiplicity result: constants
have no site, linear factors retain an exact rational evaluation, and every
alternative higher winding-one track receives a deterministic output owner. -/
def AtomicMaximality
    {source opposite : GaussianPolynomial}
    {input : SquarefreeSideInput source opposite}
    (observation : SquarefreeObservation input) : Type :=
  match observation with
  | .constant _ => PUnit
  | .exact root _ _ => PLift (source.eval root.point = 0)
  | .higher boxes _ =>
      ∀ (track : WindingOneTrack source
          (RFAP.GlobalWinding.largeSquareBox source)),
        track.initial.box.Refines boxes.isolation.support →
          RFAP.Maximality.OwnerSelection boxes.isolation track

def atomicMaximality
    {source opposite : GaussianPolynomial}
    {input : SquarefreeSideInput source opposite}
    (observation : SquarefreeObservation input) :
    observation.AtomicMaximality := by
  cases observation with
  | constant => exact PUnit.unit
  | exact root => exact ⟨root.root⟩
  | higher boxes => exact boxes.ownership

end SquarefreeObservation

/-- All cross-side combinations are separated using finite Bézout margins;
no selected or completed irrational root is introduced. -/
def SquarefreeObservationsSeparated
    {leftSource leftOpposite rightSource rightOpposite : GaussianPolynomial}
    {leftInput : SquarefreeSideInput leftSource leftOpposite}
    {rightInput : SquarefreeSideInput rightSource rightOpposite}
    (left : SquarefreeObservation leftInput)
    (right : SquarefreeObservation rightInput) : Type :=
  match left, right with
  | .constant _, _ => PUnit
  | _, .constant _ => PUnit
  | .exact leftRoot _ _, .exact rightRoot _ _ =>
      PLift (leftRoot.point ≠ rightRoot.point)
  | .exact leftRoot _ _, .higher rightBoxes _ =>
      ∀ index : Fin rightSource.natDegree,
        RFAP.SignedMultiplicity.ExactTrackSeparation
          (exactPolynomial := leftSource)
          (rightBoxes.isolation.trackAt index)
          (rightBoxes.isolation.trackAt index).initial leftRoot.point
  | .higher leftBoxes _, .exact rightRoot _ _ =>
      ∀ index : Fin leftSource.natDegree,
        RFAP.SignedMultiplicity.ExactTrackSeparation
          (exactPolynomial := rightSource)
          (leftBoxes.isolation.trackAt index)
          (leftBoxes.isolation.trackAt index).initial rightRoot.point
  | .higher leftBoxes _, .higher rightBoxes _ =>
      ∀ (leftIndex : Fin leftSource.natDegree)
        (rightIndex : Fin rightSource.natDegree),
        RFAP.SignedMultiplicity.TrackPairSeparation
          (leftBoxes.isolation.trackAt leftIndex)
          (leftBoxes.isolation.trackAt leftIndex).initial
          (rightBoxes.isolation.trackAt rightIndex)
          (rightBoxes.isolation.trackAt rightIndex).initial

def separateSquarefreeObservations
    {leftSource leftOpposite rightSource rightOpposite : GaussianPolynomial}
    {leftInput : SquarefreeSideInput leftSource leftOpposite}
    {rightInput : SquarefreeSideInput rightSource rightOpposite}
    (left : SquarefreeObservation leftInput)
    (right : SquarefreeObservation rightInput)
    (coprime : RFAP.Squarefree.CoprimeCertificate
      leftSource rightSource) :
    SquarefreeObservationsSeparated left right := by
  cases left with
  | constant => exact PUnit.unit
  | exact leftRoot =>
      cases right with
      | constant => exact PUnit.unit
      | exact rightRoot =>
          exact ⟨RFAP.SignedMultiplicity.exactPoints_ne coprime
            leftRoot.root rightRoot.root⟩
      | higher rightBoxes rightDegree =>
          intro index
          exact RFAP.SignedMultiplicity.separateExactFromTrack
            ((show (0 : Nat) < 2 by decide).trans_le rightDegree)
            (RFAP.SquarefreeFactors.CoprimeCertificate.symm coprime)
            (rightBoxes.isolation.trackAt index)
            (rightBoxes.isolation.trackAt index).initial leftRoot.point
            leftRoot.root
  | higher leftBoxes leftDegree =>
      cases right with
      | constant => exact PUnit.unit
      | exact rightRoot =>
          intro index
          exact RFAP.SignedMultiplicity.separateExactFromTrack
            ((show (0 : Nat) < 2 by decide).trans_le leftDegree) coprime
            (leftBoxes.isolation.trackAt index)
            (leftBoxes.isolation.trackAt index).initial rightRoot.point
            rightRoot.root
      | higher rightBoxes rightDegree =>
          intro leftIndex rightIndex
          exact RFAP.SignedMultiplicity.separateTracks
            ((show (0 : Nat) < 2 by decide).trans_le leftDegree)
            ((show (0 : Nat) < 2 by decide).trans_le rightDegree) coprime
            (leftBoxes.isolation.trackAt leftIndex)
            (leftBoxes.isolation.trackAt leftIndex).initial
            (rightBoxes.isolation.trackAt rightIndex)
            (rightBoxes.isolation.trackAt rightIndex).initial

/-- Complete result for one squarefree side, with degree count, internal
separation, and atomic maximality retained as fields. -/
structure SquarefreeSideResult
    {source opposite : GaussianPolynomial}
    (input : SquarefreeSideInput source opposite) where
  observation : SquarefreeObservation input
  siteCount : observation.siteCount = source.natDegree
  internalSeparation : observation.InternallySeparated
  atomicMaximality : observation.AtomicMaximality

def proveSquarefreeSide
    {source opposite : GaussianPolynomial}
    (input : SquarefreeSideInput source opposite) :
    SquarefreeSideResult input :=
  let observation := input.observe
  { observation := observation
    siteCount := observation.siteCount_eq_natDegree
    internalSeparation := observation.internallySeparated
    atomicMaximality := observation.atomicMaximality }

/-- Total squarefree input after executable cancellation. -/
structure SquarefreeInput
    (numerator denominator : GaussianPolynomial) where
  nonzero : NonzeroReducedInput numerator denominator
  numeratorSquarefree :
    SquarefreeCertificate nonzero.reduction.numeratorReduced
  denominatorSquarefree :
    SquarefreeCertificate nonzero.reduction.denominatorReduced

namespace SquarefreeInput

def numeratorSide
    {numerator denominator : GaussianPolynomial}
    (input : SquarefreeInput numerator denominator) :
    SquarefreeSideInput input.nonzero.reduction.numeratorReduced
      input.nonzero.reduction.denominatorReduced where
  sourceSquarefree := input.numeratorSquarefree
  sourceNonzero := input.nonzero.numeratorReducedNonzero
  oppositeNonzero := input.nonzero.denominatorReducedNonzero
  sourceOppositeCoprime := input.nonzero.reduction.coprime

def denominatorSide
    {numerator denominator : GaussianPolynomial}
    (input : SquarefreeInput numerator denominator) :
    SquarefreeSideInput input.nonzero.reduction.denominatorReduced
      input.nonzero.reduction.numeratorReduced where
  sourceSquarefree := input.denominatorSquarefree
  sourceNonzero := input.nonzero.denominatorReducedNonzero
  oppositeNonzero := input.nonzero.numeratorReducedNonzero
  sourceOppositeCoprime :=
    RFAP.SquarefreeFactors.CoprimeCertificate.symm
      input.nonzero.reduction.coprime

end SquarefreeInput

/-- Degree-sharp squarefree RFAP result in every finite degree.  The two
site counts are exactly the reduced degrees, all internal and cross-side
separations are explicit, and the one finite outer square has the signed
degree-difference winding. -/
structure SquarefreeResult
    (numerator denominator : GaussianPolynomial) where
  input : SquarefreeInput numerator denominator
  numeratorSites : SquarefreeSideResult input.numeratorSide
  denominatorSites : SquarefreeSideResult input.denominatorSide
  jointSeparation : SquarefreeObservationsSeparated
    numeratorSites.observation denominatorSites.observation
  outerWinding :
    RFAP.RationalWinding.rationalQuadrupledWinding
        input.nonzero.reduction.numeratorReduced
        input.nonzero.reduction.denominatorReduced input.nonzero.outerBox =
      (4 : Int) * input.nonzero.reduction.numeratorReduced.natDegree -
        (4 : Int) * input.nonzero.reduction.denominatorReduced.natDegree
  outerBoxWinding :
    RFAP.RationalWinding.rationalBoxWinding
        input.nonzero.reduction.numeratorReduced
        input.nonzero.reduction.denominatorReduced input.nonzero.outerBox =
      (input.nonzero.reduction.numeratorReduced.natDegree : Int) -
        input.nonzero.reduction.denominatorReduced.natDegree

def proveSquarefree
    {numerator denominator : GaussianPolynomial}
    (input : SquarefreeInput numerator denominator) :
    SquarefreeResult numerator denominator :=
  let numeratorSites := proveSquarefreeSide input.numeratorSide
  let denominatorSites := proveSquarefreeSide input.denominatorSide
  { input := input
    numeratorSites := numeratorSites
    denominatorSites := denominatorSites
    jointSeparation := separateSquarefreeObservations
      numeratorSites.observation denominatorSites.observation
      input.nonzero.reduction.coprime
    outerWinding := input.nonzero.outer_rationalWinding_eq_degreeDifference
    outerBoxWinding := input.nonzero.outer_boxWinding_eq_degreeDifference }

end RFAP.RationalFunctionArgumentPrinciple
