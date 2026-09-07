import mathlib.Data.ConstructiveList
import CCL.Bridge.Box
import RFAP.Rational.Sites

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace CCL.RationalRFAPBridge

abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial

/-- CCL data attached to one already-proved RFAP factor observation. -/
def ObservationCCL
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries} :
    RFAP.RationalSites.PositiveSideInput.FactorObservation input context → Type
  | .exact _ _ _ =>
      CCL.BoxRFAPBridge.Terminal context.focus.part.polynomial
  | .higher _ _ =>
      CCL.BoxRFAPBridge.Result context.focus.part.polynomial

/-- Construct the CCL attachment by reusing the exact terminal constructor or
the exact same higher-degree box result stored by RFAP. -/
def observationCCL
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context) :
    ObservationCCL observation := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      exact CCL.BoxRFAPBridge.terminalOfExactRoot root
  | higher boxes degree =>
      exact ⟨boxes⟩

/-- Finite site index inside one factor observation.  A linear observation
has its single displayed rational site; a higher observation retains the
degree-indexed family of independently shrinking tracks. -/
def ObservationIndex
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries} :
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context) →
      Type
  | .exact _ _ _ => Unit
  | .higher _ _ => Fin context.focus.part.polynomial.natDegree

/-- Displayed finite enumeration of every site inside one exact or
higher-degree factor observation. -/
def observationIndices
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context) :
    List (ObservationIndex observation) := by
  cases observation with
  | exact root degree oppositeAtRoot => exact [Unit.unit]
  | higher boxes degree => exact List.ofFn id

/-- The displayed observation index list contains every exact or higher
site. -/
theorem mem_observationIndices
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (index : ObservationIndex observation) :
    index ∈ observationIndices observation := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      cases index
      simp only [observationIndices, List.mem_singleton]
  | higher boxes degree =>
      simp only [observationIndices, List.mem_ofFn]
      exact ⟨index, rfl⟩

/-- Turn either an exact rational site or one higher shrinking track into the
same productive arithmetic-name interface.  Exact sites use their displayed
rational point; no completed value is extracted from a higher track. -/
def observationArithmeticName
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation) :
    ObservationIndex observation →
      CCL.ProgressiveTransducer.Named := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      intro _site
      exact CCL.ProgressiveTransducer.Named.exact root.point
  | higher boxes degree =>
      intro index
      exact data.arithmeticNameAt index

theorem observationArithmeticName_productive
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation) (count : Nat) :
    (observationArithmeticName observation data index).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (observationArithmeticName observation data index).machine
          count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        (observationArithmeticName observation data index).machine
        count).emitted.length = count :=
  (observationArithmeticName observation data index).productive count

theorem observationArithmeticName_exact
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation) (count : Nat) :
    let name := observationArithmeticName observation data index
    CCL.ProgressiveMachineSemantics.ExactCursor
      name.process name.state
      (CCL.ProgressiveTransducer.advance name.machine count) :=
  CCL.ProgressiveMachineSemantics.Named.advance_exact
    (observationArithmeticName observation data index) count

/-! ## Persistent per-observation requests -/

/-- Numerical component paired with one persistent arithmetic cursor.  Exact
rational sites need no shrinking box; higher sites retain the actual Paper-I
winding state. -/
def ObservationNumericalState
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation) :
    ObservationIndex observation → Type := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      intro _index
      exact Unit
  | higher boxes degree =>
      intro index
      exact RFAP.ShrinkingTrack.WindingOneState
        context.focus.part.polynomial
        (RFAP.GlobalWinding.largeSquareBox context.focus.part.polynomial)

def observationNumericalInitial
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation) :
    ObservationNumericalState observation data index := by
  cases observation with
  | exact root degree oppositeAtRoot => exact Unit.unit
  | higher boxes degree => exact (data.trackAt index).initial

/-- The optional current box.  `none` means that the observation is already
an exact displayed rational site. -/
def observationNumericalBox?
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation) :
    ObservationNumericalState observation data index → Option RFAP.Boxes.Box := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      intro _state
      exact none
  | higher boxes degree =>
      intro state
      exact some state.box

/-- Proof that a higher numerical component remains below its initial
isolating box.  The exact branch has no numerical obligation. -/
def ObservationNumericalValid
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation)
    (state : ObservationNumericalState observation data index) : Prop := by
  cases observation with
  | exact root degree oppositeAtRoot => exact True
  | higher boxes degree =>
      exact state.box.Refines (data.trackAt index).initial.box

/-- Uniform persistent site state.  Its cursor is never restarted. -/
structure ObservationPersistentState
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation) where
  numerical : ObservationNumericalState observation data index
  numericalValid : ObservationNumericalValid observation data index numerical
  cursor : CCL.PersistentProgressive.Cursor
    (observationArithmeticName observation data index).process
    (observationArithmeticName observation data index).state

def observationPersistentInitial
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation) :
    ObservationPersistentState observation data index := by
  refine
    { numerical := observationNumericalInitial observation data index
      numericalValid := ?_
      cursor := CCL.PersistentProgressive.Cursor.initial
        (observationArithmeticName observation data index).process
        (observationArithmeticName observation data index).state }
  cases observation with
  | exact root degree oppositeAtRoot => exact True.intro
  | higher boxes degree => exact RFAP.Boxes.Box.refines_refl _

/-- One persistent zero/pole-site request. -/
def observationPersistentRequest
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation)
    (current : ObservationPersistentState observation data index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    ObservationPersistentState observation data index := by
  let epsilonSqPositive :=
    RFAP.ConstructiveFraction.pow_pos_direct positive 2
  refine
    { numerical := ?_
      numericalValid := ?_
      cursor := current.cursor.request (epsilon ^ 2) epsilonSqPositive count }
  · cases observation with
    | exact root degree oppositeAtRoot => exact Unit.unit
    | higher boxes degree =>
        exact (data.trackAt index).refine current.numerical epsilon positive
  · cases observation with
    | exact root degree oppositeAtRoot => exact True.intro
    | higher boxes degree =>
        exact ((data.trackAt index).nested current.numerical epsilon positive).trans
          current.numericalValid

theorem observationPersistentRequest_word_extends
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation)
    (current : ObservationPersistentState observation data index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    current.cursor.machine.emitted.IsPrefix
      (observationPersistentRequest observation data index current epsilon
        positive count).cursor.machine.emitted := by
  exact current.cursor.request_extends (epsilon ^ 2)
    (RFAP.ConstructiveFraction.pow_pos_direct positive 2) count

theorem observationPersistentRequest_word_length
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation)
    (current : ObservationPersistentState observation data index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    (observationPersistentRequest observation data index current epsilon
      positive count).cursor.machine.emitted.length =
        current.cursor.machine.emitted.length + count := by
  exact current.cursor.request_length (epsilon ^ 2)
    (RFAP.ConstructiveFraction.pow_pos_direct positive 2) count

/-- Uniform optional-box contract: exact rational sites remain exact, while
higher sites return a box nested in the preceding displayed box. -/
theorem observationPersistentRequest_box_refines
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation)
    (current : ObservationPersistentState observation data index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    match observationNumericalBox? observation data index
        (observationPersistentRequest observation data index current epsilon
          positive count).numerical,
      observationNumericalBox? observation data index current.numerical with
    | none, none => True
    | some inner, some outer => inner.Refines outer
    | _, _ => False := by
  cases observation with
  | exact root degree oppositeAtRoot => exact True.intro
  | higher boxes degree =>
      exact (data.trackAt index).nested current.numerical epsilon positive

/-- Uniform optional-box accuracy contract. -/
theorem observationPersistentRequest_box_accurate
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation)
    (current : ObservationPersistentState observation data index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    match observationNumericalBox? observation data index
      (observationPersistentRequest observation data index current epsilon
        positive count).numerical with
    | none => True
    | some box => box.diagonalSq ≤ epsilon ^ 2 := by
  cases observation with
  | exact root degree oppositeAtRoot => exact True.intro
  | higher boxes degree =>
      exact (data.trackAt index).accurate current.numerical epsilon positive

theorem observationPersistentRequest_cylinder_accurate
    {source opposite : GaussianPolynomial}
    {input : RFAP.RationalSites.PositiveSideInput source opposite}
    {context : RFAP.MultiplicityWinding.PositiveContext input.entries}
    (observation :
      RFAP.RationalSites.PositiveSideInput.FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation)
    (current : ObservationPersistentState observation data index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat)
    {left right : RFAP.ConstructiveGaussian.Gaussian}
    (leftPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (observationPersistentRequest observation data index current epsilon
          positive count).cursor.machine.mode left)
    (rightPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (observationPersistentRequest observation data index current epsilon
          positive count).cursor.machine.mode right) :
    CCL.Chordal.chordalSq
        (CCL.PersistentProgressive.Machine.image
          (observationPersistentRequest observation data index current epsilon
            positive count).cursor.machine left)
        (CCL.PersistentProgressive.Machine.image
          (observationPersistentRequest observation data index current epsilon
            positive count).cursor.machine right) ≤ epsilon ^ 2 := by
  exact current.cursor.request_pair_chordalSq_le (epsilon ^ 2)
    (RFAP.ConstructiveFraction.pow_pos_direct positive 2) count
      leftPossible rightPossible

/-- CCL attachments for every factor group on one reduced cofactor side.
Constants contribute no site and therefore need no encoding data. -/
def SideCCL
    {source opposite : GaussianPolynomial} :
    RFAP.RationalSites.SideResult source opposite → Type
  | .constant _ _ _ => Unit
  | .positive input family =>
      (index : Fin input.contexts.length) →
        ObservationCCL (family.observationAt index)

def sideCCL
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite) :
    SideCCL side := by
  cases side with
  | constant => exact Unit.unit
  | positive input family =>
      exact fun index => observationCCL (family.observationAt index)

/-- Finite dependent index of every exact or higher-track site on one reduced
cofactor side.  A constant side has no sites. -/
def SideIndex
    {source opposite : GaussianPolynomial} :
    (side : RFAP.RationalSites.SideResult source opposite) → Type
  | .constant _ _ _ => Empty
  | .positive input family =>
      Sigma fun index : Fin input.contexts.length =>
        ObservationIndex (family.observationAt index)

/-- Displayed finite enumeration of every exact or higher-track site on one
reduced cofactor side. -/
def sideIndices
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite) :
    List (SideIndex side) := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact []
  | positive input family =>
      exact (List.ofFn id).flatMap fun index =>
        (observationIndices (family.observationAt index)).map fun site =>
          ⟨index, site⟩

/-- The displayed side index list contains every site on that side. -/
theorem mem_sideIndices
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (index : SideIndex side) : index ∈ sideIndices side := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      rcases index with ⟨factor, site⟩
      rw [sideIndices, QuotientFreeList.mem_flatMap]
      refine ⟨factor, ?_, ?_⟩
      · simp only [List.mem_ofFn]
        exact ⟨factor, rfl⟩
      · exact QuotientFreeList.mem_map.mpr
          ⟨site, mem_observationIndices (family.observationAt factor) site,
            rfl⟩

/-- Multiplicity attached to a displayed exact or higher-track site.  Every
site inside one squarefree basis factor carries that factor's multiplicity. -/
def sideMultiplicity
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite) :
    SideIndex side → Nat := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero =>
      intro index
      exact nomatch index
  | positive input family =>
      intro index
      exact (input.contexts.get index.1).focus.multiplicity

/-- Persistent state at any exact or higher site on one reduced cofactor
side. -/
def SidePersistentState
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side) : Type 1 := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact ObservationPersistentState (family.observationAt index.1)
        (data index.1) index.2

def sidePersistentInitial
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side) :
    SidePersistentState side data index := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact observationPersistentInitial (family.observationAt index.1)
        (data index.1) index.2

def sidePersistentRequest
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side)
    (current : SidePersistentState side data index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    SidePersistentState side data index := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact observationPersistentRequest (family.observationAt index.1)
        (data index.1) index.2 current epsilon positive count

def sidePersistentMachine
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side)
    (state : SidePersistentState side data index) :
    CCL.ProgressiveTransducer.Machine := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family => exact state.cursor.machine

def sidePersistentBox?
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side)
    (state : SidePersistentState side data index) : Option RFAP.Boxes.Box := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact observationNumericalBox? (family.observationAt index.1)
        (data index.1) index.2 state.numerical

theorem sidePersistentRequest_word_extends
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side)
    (current : SidePersistentState side data index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    (sidePersistentMachine side data index current).emitted.IsPrefix
      (sidePersistentMachine side data index
        (sidePersistentRequest side data index current epsilon positive count)).emitted := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact observationPersistentRequest_word_extends
        (family.observationAt index.1) (data index.1) index.2 current
          epsilon positive count

theorem sidePersistentRequest_word_length
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side)
    (current : SidePersistentState side data index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    (sidePersistentMachine side data index
      (sidePersistentRequest side data index current epsilon positive count)).emitted.length =
        (sidePersistentMachine side data index current).emitted.length + count := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact observationPersistentRequest_word_length
        (family.observationAt index.1) (data index.1) index.2 current
          epsilon positive count

theorem sidePersistentRequest_box_refines
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side)
    (current : SidePersistentState side data index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    match sidePersistentBox? side data index
        (sidePersistentRequest side data index current epsilon positive count),
      sidePersistentBox? side data index current with
    | none, none => True
    | some inner, some outer => inner.Refines outer
    | _, _ => False := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact observationPersistentRequest_box_refines
        (family.observationAt index.1) (data index.1) index.2 current
          epsilon positive count

theorem sidePersistentRequest_box_accurate
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side)
    (current : SidePersistentState side data index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    match sidePersistentBox? side data index
      (sidePersistentRequest side data index current epsilon positive count) with
    | none => True
    | some box => box.diagonalSq ≤ epsilon ^ 2 := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact observationPersistentRequest_box_accurate
        (family.observationAt index.1) (data index.1) index.2 current
          epsilon positive count

theorem sidePersistentRequest_cylinder_accurate
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side)
    (current : SidePersistentState side data index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat)
    {left right : RFAP.ConstructiveGaussian.Gaussian}
    (leftPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (sidePersistentMachine side data index
          (sidePersistentRequest side data index current epsilon positive count)).mode
        left)
    (rightPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (sidePersistentMachine side data index
          (sidePersistentRequest side data index current epsilon positive count)).mode
        right) :
    CCL.Chordal.chordalSq
        (CCL.PersistentProgressive.Machine.image
          (sidePersistentMachine side data index
            (sidePersistentRequest side data index current epsilon positive count))
          left)
        (CCL.PersistentProgressive.Machine.image
          (sidePersistentMachine side data index
            (sidePersistentRequest side data index current epsilon positive count))
          right) ≤ epsilon ^ 2 := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      exact observationPersistentRequest_cylinder_accurate
        (family.observationAt index.1) (data index.1) index.2 current
          epsilon positive count leftPossible rightPossible

/-- Arithmetic name at any zero-side or pole-side site. -/
def sideArithmeticName
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) : SideIndex side →
      CCL.ProgressiveTransducer.Named := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero =>
      intro index
      exact nomatch index
  | positive input family =>
      intro index
      exact observationArithmeticName (family.observationAt index.1)
        (data index.1) index.2

/-- Exact raw-parser semantics retained by any persistent site state. -/
theorem sidePersistentExact
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side)
    (state : SidePersistentState side data index) :
    CCL.ProgressiveMachineSemantics.ExactCursor
      (sideArithmeticName side data index).process
      (sideArithmeticName side data index).state
      (sidePersistentMachine side data index state) := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family => exact state.cursor.exact

theorem sideArithmeticName_productive
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side) (count : Nat) :
    (sideArithmeticName side data index).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (sideArithmeticName side data index).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        (sideArithmeticName side data index).machine count).emitted.length =
          count :=
  (sideArithmeticName side data index).productive count

theorem sideArithmeticName_exact
    {source opposite : GaussianPolynomial}
    (side : RFAP.RationalSites.SideResult source opposite)
    (data : SideCCL side) (index : SideIndex side) (count : Nat) :
    let name := sideArithmeticName side data index
    CCL.ProgressiveMachineSemantics.ExactCursor
      name.process name.state
      (CCL.ProgressiveTransducer.advance name.machine count) :=
  CCL.ProgressiveMachineSemantics.Named.advance_exact
    (sideArithmeticName side data index) count

/-- The complete RFAP result together with CCL data for every zero and pole
site.  All signed winding, multiplicity, separation, maximality, and outer
degree-difference fields remain those of the original Paper-I result. -/
structure NonzeroResult
    (numerator denominator : GaussianPolynomial) where
  rfap : RFAP.RationalSites.NonzeroResult numerator denominator
  numeratorCCL : SideCCL rfap.numeratorSites
  denominatorCCL : SideCCL rfap.denominatorSites

namespace NonzeroResult

theorem outerBoxWinding
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator) :
    RFAP.RationalWinding.rationalBoxWinding
        result.rfap.input.reduction.numeratorReduced
        result.rfap.input.reduction.denominatorReduced
        result.rfap.input.outerBox =
      (result.rfap.input.reduction.numeratorReduced.natDegree : Int) -
        result.rfap.input.reduction.denominatorReduced.natDegree :=
  result.rfap.outerBoxWinding

/-- Every exact or shrinking-track zero site after cancellation. -/
def ZeroIndex
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator) : Type :=
  SideIndex result.rfap.numeratorSites

/-- Every exact or shrinking-track pole site after cancellation. -/
def PoleIndex
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator) : Type :=
  SideIndex result.rfap.denominatorSites

/-- Productive arithmetic CCL name of one reduced zero site. -/
def zeroArithmeticName
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.ZeroIndex) :
    CCL.ProgressiveTransducer.Named :=
  sideArithmeticName result.rfap.numeratorSites result.numeratorCCL index

/-- Productive arithmetic CCL name of one reduced pole site. -/
def poleArithmeticName
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.PoleIndex) :
    CCL.ProgressiveTransducer.Named :=
  sideArithmeticName result.rfap.denominatorSites result.denominatorCCL index

/-- Stateful persistent CCL observation of one reduced zero site. -/
abbrev ZeroPersistentState
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.ZeroIndex) :=
  SidePersistentState result.rfap.numeratorSites result.numeratorCCL index

/-- Stateful persistent CCL observation of one reduced pole site. -/
abbrev PolePersistentState
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.PoleIndex) :=
  SidePersistentState result.rfap.denominatorSites result.denominatorCCL index

def zeroPersistentInitial
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.ZeroIndex) : result.ZeroPersistentState index :=
  sidePersistentInitial result.rfap.numeratorSites result.numeratorCCL index

def polePersistentInitial
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.PoleIndex) : result.PolePersistentState index :=
  sidePersistentInitial result.rfap.denominatorSites result.denominatorCCL index

def zeroPersistentRequest
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.ZeroIndex) (current : result.ZeroPersistentState index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    result.ZeroPersistentState index :=
  sidePersistentRequest result.rfap.numeratorSites result.numeratorCCL index
    current epsilon positive count

def polePersistentRequest
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.PoleIndex) (current : result.PolePersistentState index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    result.PolePersistentState index :=
  sidePersistentRequest result.rfap.denominatorSites result.denominatorCCL index
    current epsilon positive count

theorem zeroPersistentRequest_word_extends
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.ZeroIndex) (current : result.ZeroPersistentState index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    (sidePersistentMachine result.rfap.numeratorSites result.numeratorCCL index
      current).emitted.IsPrefix
      (sidePersistentMachine result.rfap.numeratorSites result.numeratorCCL index
        (result.zeroPersistentRequest index current epsilon positive count)).emitted :=
  sidePersistentRequest_word_extends result.rfap.numeratorSites
    result.numeratorCCL index current epsilon positive count

theorem polePersistentRequest_word_extends
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.PoleIndex) (current : result.PolePersistentState index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    (sidePersistentMachine result.rfap.denominatorSites result.denominatorCCL index
      current).emitted.IsPrefix
      (sidePersistentMachine result.rfap.denominatorSites result.denominatorCCL index
        (result.polePersistentRequest index current epsilon positive count)).emitted :=
  sidePersistentRequest_word_extends result.rfap.denominatorSites
    result.denominatorCCL index current epsilon positive count

theorem zeroPersistentRequest_box_accurate
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.ZeroIndex) (current : result.ZeroPersistentState index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    match sidePersistentBox? result.rfap.numeratorSites result.numeratorCCL index
      (result.zeroPersistentRequest index current epsilon positive count) with
    | none => True
    | some box => box.diagonalSq ≤ epsilon ^ 2 :=
  sidePersistentRequest_box_accurate result.rfap.numeratorSites
    result.numeratorCCL index current epsilon positive count

theorem polePersistentRequest_box_accurate
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.PoleIndex) (current : result.PolePersistentState index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat) :
    match sidePersistentBox? result.rfap.denominatorSites result.denominatorCCL
      index (result.polePersistentRequest index current epsilon positive count) with
    | none => True
    | some box => box.diagonalSq ≤ epsilon ^ 2 :=
  sidePersistentRequest_box_accurate result.rfap.denominatorSites
    result.denominatorCCL index current epsilon positive count

theorem zeroPersistentRequest_cylinder_accurate
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.ZeroIndex) (current : result.ZeroPersistentState index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat)
    {left right : RFAP.ConstructiveGaussian.Gaussian}
    (leftPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (sidePersistentMachine result.rfap.numeratorSites result.numeratorCCL index
          (result.zeroPersistentRequest index current epsilon positive count)).mode
        left)
    (rightPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (sidePersistentMachine result.rfap.numeratorSites result.numeratorCCL index
          (result.zeroPersistentRequest index current epsilon positive count)).mode
        right) :
    CCL.Chordal.chordalSq
        (CCL.PersistentProgressive.Machine.image
          (sidePersistentMachine result.rfap.numeratorSites result.numeratorCCL
            index (result.zeroPersistentRequest index current epsilon positive count))
          left)
        (CCL.PersistentProgressive.Machine.image
          (sidePersistentMachine result.rfap.numeratorSites result.numeratorCCL
            index (result.zeroPersistentRequest index current epsilon positive count))
          right) ≤ epsilon ^ 2 :=
  sidePersistentRequest_cylinder_accurate result.rfap.numeratorSites
    result.numeratorCCL index current epsilon positive count
      leftPossible rightPossible

theorem polePersistentRequest_cylinder_accurate
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.PoleIndex) (current : result.PolePersistentState index)
    (epsilon : CCL.PersistentProgressive.Coordinate)
    (positive : 0 < epsilon) (count : Nat)
    {left right : RFAP.ConstructiveGaussian.Gaussian}
    (leftPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (sidePersistentMachine result.rfap.denominatorSites result.denominatorCCL
          index (result.polePersistentRequest index current epsilon positive count)).mode
        left)
    (rightPossible :
      CCL.ProgressiveMachineSemantics.SemanticMode.possible
        (sidePersistentMachine result.rfap.denominatorSites result.denominatorCCL
          index (result.polePersistentRequest index current epsilon positive count)).mode
        right) :
    CCL.Chordal.chordalSq
        (CCL.PersistentProgressive.Machine.image
          (sidePersistentMachine result.rfap.denominatorSites result.denominatorCCL
            index (result.polePersistentRequest index current epsilon positive count))
          left)
        (CCL.PersistentProgressive.Machine.image
          (sidePersistentMachine result.rfap.denominatorSites result.denominatorCCL
            index (result.polePersistentRequest index current epsilon positive count))
          right) ≤ epsilon ^ 2 :=
  sidePersistentRequest_cylinder_accurate result.rfap.denominatorSites
    result.denominatorCCL index current epsilon positive count
      leftPossible rightPossible

theorem zeroArithmeticName_productive
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.ZeroIndex) (count : Nat) :
    (result.zeroArithmeticName index).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (result.zeroArithmeticName index).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        (result.zeroArithmeticName index).machine count).emitted.length =
          count :=
  sideArithmeticName_productive result.rfap.numeratorSites
    result.numeratorCCL index count

theorem poleArithmeticName_productive
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.PoleIndex) (count : Nat) :
    (result.poleArithmeticName index).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (result.poleArithmeticName index).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        (result.poleArithmeticName index).machine count).emitted.length =
          count :=
  sideArithmeticName_productive result.rfap.denominatorSites
    result.denominatorCCL index count

theorem zeroArithmeticName_exact
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.ZeroIndex) (count : Nat) :
    let name := result.zeroArithmeticName index
    CCL.ProgressiveMachineSemantics.ExactCursor
      name.process name.state
      (CCL.ProgressiveTransducer.advance name.machine count) :=
  sideArithmeticName_exact result.rfap.numeratorSites
    result.numeratorCCL index count

theorem poleArithmeticName_exact
    {numerator denominator : GaussianPolynomial}
    (result : NonzeroResult numerator denominator)
    (index : result.PoleIndex) (count : Nat) :
    let name := result.poleArithmeticName index
    CCL.ProgressiveMachineSemantics.ExactCursor
      name.process name.state
      (CCL.ProgressiveTransducer.advance name.machine count) :=
  sideArithmeticName_exact result.rfap.denominatorSites
    result.denominatorCCL index count

end NonzeroResult

/-- Total CCL-coupled RFAP result.  The identically-zero numerator remains an
explicit Paper-I outcome rather than being assigned spurious zero cylinders. -/
inductive Result (numerator denominator : GaussianPolynomial) where
  | zeroNumerator
      (numeratorZero : numerator.isZero = true)
      (denominatorNonzero : denominator.isZero = false)
  | nonzero (result : NonzeroResult numerator denominator)

/-- Execute Paper I once, then attach CCL data to its finite exact/shrinking
observations. -/
def prove
    (numerator denominator : GaussianPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    Result numerator denominator := by
  match RFAP.RationalSites.prove numerator denominator denominatorNonzero with
  | .zeroNumerator numeratorZero denominatorNonzero =>
      exact .zeroNumerator numeratorZero denominatorNonzero
  | .nonzero rfap =>
      exact .nonzero
        { rfap := rfap
          numeratorCCL := sideCCL rfap.numeratorSites
          denominatorCCL := sideCCL rfap.denominatorSites }

end CCL.RationalRFAPBridge
