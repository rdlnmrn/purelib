import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Progressive.MachineSemantics
import CCL.Encoding.TerminalPadding

/-!
# Optional contraction accounting for progressive arithmetic cursors

The canonical encoder, raw parser, and progressive `List Bool` cursor do not
carry an error symbol.  This module is a separate proof sidecar.  It packages
neutral chart changes and normalized sector emissions into finite traces of
projectively coherent redundant blocks, then combines their dyadic
contraction with the explicit coefficient of any already committed decoder
prefix.
-/

namespace CCL.ProgressiveMachineContraction

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Proj := CCL.GaussianProjective.Proj
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev Mode := CCL.ProgressiveTransducer.Mode
abbrev LoopState := CCL.ProgressiveTransducer.LoopState
abbrev ResidualState := CCL.ProgressiveTransducer.ResidualState
abbrev Block := CCL.RedundantBlockContraction.Block
abbrev Tail := CCL.RedundantBlockContraction.Tail
abbrev ProjectiveRealizes :=
  CCL.RedundantBlockContraction.ProjectiveRealizes

open RFAP.ConstructiveGaussian.Gaussian
open CCL.ProgressiveCharts
open CCL.ProgressiveTransducer
open CCL.ProgressiveMachineSemantics

/-- A sidecar transition which changes no completed contracting block. -/
def NeutralTransition (before after : Mode) : Prop :=
  ∀ {tail : Gaussian}, SemanticMode.possible after tail →
    ∃ previous : Gaussian,
      SemanticMode.possible before previous ∧
        (SemanticMode.parserTail before previous).Equivalent
          (SemanticMode.parserTail after tail)

/-- A sidecar transition which contributes one normalized redundant block. -/
def ContractingTransition (before after : Mode) (entry : Block) : Prop :=
  ∀ {tail : Gaussian}, SemanticMode.possible after tail →
    ∃ previous : Gaussian,
      SemanticMode.possible before previous ∧
        ∃ blockTail : Tail entry.sector,
          (SemanticMode.parserTail before previous).Equivalent
              (CCL.Mat2.act entry.matrix blockTail.point) ∧
            blockTail.point.Equivalent
              (SemanticMode.parserTail after tail)

namespace NeutralTransition

theorem trans {before middle after : Mode}
    (first : NeutralTransition before middle)
    (second : NeutralTransition middle after) :
    NeutralTransition before after := by
  intro tail possible
  rcases second possible with
    ⟨middleValue, middlePossible, secondEquivalent⟩
  rcases first middlePossible with
    ⟨previous, previousPossible, firstEquivalent⟩
  exact ⟨previous, previousPossible,
    CCL.Chordal.Proj.equivalent_trans
      firstEquivalent secondEquivalent
      (SemanticMode.parserTail_valid middle middleValue)
      (SemanticMode.parserTail_valid after tail)⟩

theorem thenContracting {before middle after : Mode} {entry : Block}
    (first : NeutralTransition before middle)
    (second : ContractingTransition middle after entry) :
    ContractingTransition before after entry := by
  intro tail possible
  rcases second possible with
    ⟨middleValue, middlePossible, blockTail, outputEquivalent,
      tailEquivalent⟩
  rcases first middlePossible with
    ⟨previous, previousPossible, firstEquivalent⟩
  have imageValid :=
    CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      entry.matrix_det_ne blockTail.point_valid
  exact ⟨previous, previousPossible, blockTail,
    CCL.Chordal.Proj.equivalent_trans
      firstEquivalent outputEquivalent
      (SemanticMode.parserTail_valid middle middleValue) imageValid,
    tailEquivalent⟩

end NeutralTransition

/-- One controller chunk is either chart-neutral for contraction accounting,
or contributes one certified normalized block. -/
def AccountedStep (before after : Mode) : Prop :=
  NeutralTransition before after ∨
    ∃ entry : Block, ContractingTransition before after entry

/-- A finite semantic trace.  Neutral transitions leave the block list
unchanged; normalized sector transitions prepend the ordinary block which was
actually emitted. -/
inductive Trace : Mode → Mode → List Block → Prop where
  | done (mode : Mode) : Trace mode mode []
  | neutral {before middle after : Mode} {blocks : List Block}
      (transition : NeutralTransition before middle)
      (rest : Trace middle after blocks) :
      Trace before after blocks
  | sector {before middle after : Mode} {blocks : List Block}
      (entry : Block)
      (transition : ContractingTransition before middle entry)
      (rest : Trace middle after blocks) :
      Trace before after (entry :: blocks)

namespace Trace

/-- Reading a finite trace backwards turns every admitted final candidate
into a projectively coherent realization of all counted ordinary blocks. -/
theorem realizes {before after : Mode} {blocks : List Block}
    (trace : Trace before after blocks) {tail : Gaussian}
    (possible : SemanticMode.possible after tail) :
    ∃ previous : Gaussian,
      SemanticMode.possible before previous ∧
        ProjectiveRealizes blocks
          (SemanticMode.parserTail before previous) := by
  induction trace with
  | done mode =>
      exact ⟨tail, possible,
        .done _ (SemanticMode.parserTail_valid mode tail)⟩
  | @neutral before middle after blocks transition rest inductionHypothesis =>
      rcases inductionHypothesis possible with
        ⟨middleValue, middlePossible, middleRealizes⟩
      rcases transition middlePossible with
        ⟨previous, previousPossible, equivalent⟩
      exact ⟨previous, previousPossible,
        CCL.RedundantBlockContraction.ProjectiveRealizes.ofEquivalent
          (SemanticMode.parserTail_valid before previous)
          equivalent middleRealizes⟩
  | @sector before middle after blocks entry transition rest
      inductionHypothesis =>
      rcases inductionHypothesis possible with
        ⟨middleValue, middlePossible, middleRealizes⟩
      rcases transition middlePossible with
        ⟨previous, previousPossible, blockTail, outputEquivalent,
          tailEquivalent⟩
      exact ⟨previous, previousPossible,
        .step entry blockTail
          (SemanticMode.parserTail_valid before previous)
          outputEquivalent tailEquivalent middleRealizes⟩

/-- Pairwise dyadic diameter of every finite error-certified trace. -/
theorem pair_chordalSq_le_half_pow
    {before after : Mode} {blocks : List Block}
    (trace : Trace before after blocks)
    {leftTail rightTail : Gaussian}
    (leftPossible : SemanticMode.possible after leftTail)
    (rightPossible : SemanticMode.possible after rightTail) :
    ∃ leftPrevious : Gaussian,
      SemanticMode.possible before leftPrevious ∧
        ∃ rightPrevious : Gaussian,
          SemanticMode.possible before rightPrevious ∧
            CCL.Chordal.chordalSq
                (SemanticMode.parserTail before leftPrevious)
                (SemanticMode.parserTail before rightPrevious) ≤
              (1 / 2 : Coordinate) ^ blocks.length := by
  rcases trace.realizes leftPossible with
    ⟨leftPrevious, leftPreviousPossible, leftRealizes⟩
  rcases trace.realizes rightPossible with
    ⟨rightPrevious, rightPreviousPossible, rightRealizes⟩
  exact ⟨leftPrevious, leftPreviousPossible,
    rightPrevious, rightPreviousPossible,
    CCL.RedundantBlockContraction.ProjectiveRealizes.chordalSq_le_half_pow
      leftRealizes rightRealizes⟩

/-- An arbitrary fixed invertible decoder outside a certified trace changes
only its explicit finite coefficient. -/
theorem pair_chordalSq_act_le_transportCoefficient_half_pow
    {before after : Mode} {blocks : List Block}
    (trace : Trace before after blocks)
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    {leftTail rightTail : Gaussian}
    (leftPossible : SemanticMode.possible after leftTail)
    (rightPossible : SemanticMode.possible after rightTail) :
    ∃ leftPrevious : Gaussian,
      SemanticMode.possible before leftPrevious ∧
        ∃ rightPrevious : Gaussian,
          SemanticMode.possible before rightPrevious ∧
            CCL.Chordal.chordalSq
                (CCL.Mat2.act matrix
                  (SemanticMode.parserTail before leftPrevious))
                (CCL.Mat2.act matrix
                  (SemanticMode.parserTail before rightPrevious)) ≤
              CCL.TerminalPadding.transportCoefficient matrix *
                (1 / 2 : Coordinate) ^ blocks.length := by
  rcases trace.realizes leftPossible with
    ⟨leftPrevious, leftPreviousPossible, leftRealizes⟩
  rcases trace.realizes rightPossible with
    ⟨rightPrevious, rightPreviousPossible, rightRealizes⟩
  exact ⟨leftPrevious, leftPreviousPossible,
    rightPrevious, rightPreviousPossible,
    CCL.TerminalPadding.chordalSq_act_projectiveRealizes_le_transportCoefficient_half_pow
        matrix determinantNonzero leftRealizes rightRealizes⟩

end Trace

/-! ## The actual normalized-loop sector transition -/

/-- The redundant block contributed by a live normalized-loop sector. -/
def loopSectorBlock (current : LoopState)
    (sector : CCL.Sectors.Sector) : Block :=
  CCL.ProgressiveTransducerSemantics.redundantBlock
    (regularBlockKind current.kind) current.count sector

@[simp] theorem loopSectorBlock_matrix (current : LoopState)
    (sector : CCL.Sectors.Sector) :
    (loopSectorBlock current sector).matrix =
      CCL.RawParser.blockMatrix
        (regularBlockKind current.kind) current.count sector :=
  CCL.ProgressiveTransducerSemantics.redundantBlock_matrix
    (regularBlockKind current.kind) current.count sector

/-- Semantic half-contracting transition supplied by the precise safe-sector
certificate used in the live normalized loop. -/
theorem loopSector_contractingTransition
    (current : LoopState) (sector : CCL.Sectors.Sector)
    (certificate : CCL.RedundantOutput.SafeBall sector
      (current.process.ball
        (current.domain.refinedState current.state))) :
    ContractingTransition (.loop current)
      (.residual (loopSectorResidualState current sector certificate))
      (loopSectorBlock current sector) := by
  intro residual possible
  change (residualProcess current.process
      (current.domain.refinedState current.state) sector).Possible
    (residualInitial current.process
      (current.domain.refinedState current.state) sector) residual at possible
  rcases possible with ⟨sourceValue, sourcePossible, residualEqual⟩
  have previousPossible :
      current.process.Possible current.state sourceValue :=
    current.process.refine_persists current.state _ _ sourcePossible
  let rawValue := natPow gamma current.count * sourceValue
  have normalizedIdentity :
      CCL.RawParser.normalizedValue
          (regularBlockKind current.kind) current.count rawValue =
        sourceValue :=
    regularNormalized_scaled current.kind current.count sourceValue
  have sourceNorm : 1 ≤ normSq sourceValue :=
    loop_candidate_norm_lower current
      (current.domain.refinedState current.state) sourcePossible
  have sourceSafe : CCL.RedundantSectors.Safe sector sourceValue :=
    CCL.RedundantOutput.safe_of_contains certificate
      (current.process.possible_inside sourcePossible)
  have rawNorm :
      1 ≤ normSq (CCL.RawParser.normalizedValue
        (regularBlockKind current.kind) current.count rawValue) := by
    rw [normalizedIdentity]
    exact sourceNorm
  have rawSafe : CCL.RedundantSectors.Safe sector
      (CCL.RawParser.normalizedValue
        (regularBlockKind current.kind) current.count rawValue) := by
    rw [normalizedIdentity]
    exact sourceSafe
  let blockTail :=
    CCL.ProgressiveTransducerSemantics.safeBlockTail
      (regularBlockKind current.kind) current.count sector rawValue
        rawNorm rawSafe
  refine ⟨sourceValue, previousPossible, blockTail, ?_, ?_⟩
  · change (CCL.Proj.affine rawValue).Equivalent
      (CCL.Mat2.act (loopSectorBlock current sector).matrix blockTail.point)
    rw [loopSectorBlock_matrix]
    exact
      (CCL.ProgressiveTransducerSemantics.safeBlockTail_exact
        (regularBlockKind current.kind) current.count sector rawValue
          rawNorm rawSafe).symm
  · change blockTail.point.Equivalent ⟨1, gamma * residual⟩
    rw [residualEqual, ← normalizedIdentity]
    exact
      CCL.RedundantBlockContraction.Tail.ofSafe_point_equivalent_homogeneous sector
          (CCL.RawParser.normalizedValue
            (regularBlockKind current.kind) current.count rawValue)
          rawNorm rawSafe

/-- Every actual normalized-loop chunk is fully accounted: unary output is a
neutral normalization step, while sector output contributes the certified
ordinary redundant block above. -/
theorem loopStep_accounted (current : LoopState) :
    AccountedStep (.loop current) (loopStep current).next := by
  unfold AccountedStep loopStep
  split
  · apply Or.inl
    intro tail possible
    simp only [SemanticMode.possible] at possible
    rcases unaryScaled_candidate_semantics current.process
        (current.domain.refinedState current.state) possible with
      ⟨sourceValue, sourcePossible, tailEqual⟩
    have previousPossible :
        current.process.Possible current.state sourceValue :=
      current.process.refine_persists current.state _ _ sourcePossible
    refine ⟨sourceValue, previousPossible, ?_⟩
    simp only [SemanticMode.parserTail]
    rw [tailEqual, regularUnary_value]
    exact CCL.Proj.Equivalent.refl _
  · rename_i sector certificate selected
    apply Or.inr
    exact ⟨loopSectorBlock current sector,
      loopSector_contractingTransition current sector certificate⟩

/-- The silent residual-apartness chart change is projectively neutral.  It
is separated here from the immediately following emitted loop chunk so its
accounting can compose without adding a symbol or a completed block. -/
theorem residualApart_neutralTransition
    (current : ResidualState)
    (certificate : CCL.ArithmeticEnclosures.Ball.Apart
      (current.process.ball
        (CCL.ArithmeticController.residualState
          current.process current.state (current.count + 1)))) :
    NeutralTransition (.residual current)
      (.loop (residualApartLoopState current certificate)) := by
  intro tail possible
  simp only [SemanticMode.possible] at possible
  let refined := CCL.ArithmeticController.residualState
    current.process current.state (current.count + 1)
  have inversePossible :
      (normalizedInverseProcess current.process refined certificate
        current.count).Possible
          (normalizedInverseInitial current.process refined certificate
            current.count) tail := by
    exact possible
  rcases normalizedInverse_tail_equivalent current.process refined
      certificate current.count inversePossible with
    ⟨residual, residualAtRefined, chartEquivalent⟩
  have residualAtCurrent :
      current.process.Possible current.state residual :=
    current.process.refine_persists current.state _ _ residualAtRefined
  refine ⟨residual, residualAtCurrent, ?_⟩
  have chartEquivalent' :
      (SemanticMode.parserTail
        (.loop (residualApartLoopState current certificate)) tail).Equivalent
        (SemanticMode.parserTail (.residual current) residual) := by
    simpa only [SemanticMode.parserTail, residualApartLoopState] using
      chartEquivalent
  exact chartEquivalent'.symm

/-- Every residual chunk is accounted as well: small-residual unary padding
is neutral, while an apartness chart change composes with the accounted live
loop chunk which is emitted immediately. -/
theorem residualStep_accounted (current : ResidualState) :
    AccountedStep (.residual current) (step (.residual current)).next := by
  change AccountedStep (.residual current) (residualStep current).next
  generalize hStep : residualStep current = emission
  unfold AccountedStep
  unfold residualStep at hStep
  simp only at hStep
  split at hStep
  · cases hStep
    apply Or.inl
    intro residual possible
    simp only [SemanticMode.possible] at possible
    have previousPossible :
        current.process.Possible current.state residual :=
      current.process.refine_persists current.state _ _ possible
    exact ⟨residual, previousPossible, CCL.Proj.Equivalent.refl _⟩
  · rename_i certificate selected
    cases hStep
    let next := residualApartLoopState current certificate
    have bridge : NeutralTransition (.residual current) (.loop next) := by
      exact residualApart_neutralTransition current certificate
    rcases loopStep_accounted next with neutral | ⟨entry, contracting⟩
    · exact Or.inl (NeutralTransition.trans bridge neutral)
    · exact Or.inr
        ⟨entry, NeutralTransition.thenContracting bridge contracting⟩

/-- Modes after the optional one-time initial/low chart prefix.  Every later
sector is normalized and therefore belongs in the dyadic suffix trace. -/
inductive SuffixMode : Mode → Prop where
  | loop (current : LoopState) : SuffixMode (.loop current)
  | residual (current : ResidualState) : SuffixMode (.residual current)

theorem loopStep_next_suffix (current : LoopState) :
    SuffixMode (loopStep current).next := by
  unfold loopStep
  split
  · exact .loop _
  · exact .residual _

theorem residualStep_next_suffix (current : ResidualState) :
    SuffixMode (step (.residual current)).next := by
  change SuffixMode (residualStep current).next
  simp only [residualStep]
  split
  · exact .residual _
  · exact loopStep_next_suffix (residualApartLoopState current _)

theorem suffixStep_accounted {mode : Mode} (suffix : SuffixMode mode) :
    AccountedStep mode (step mode).next := by
  cases suffix with
  | loop current => exact loopStep_accounted current
  | residual current => exact residualStep_accounted current

theorem suffixStep_next {mode : Mode} (suffix : SuffixMode mode) :
    SuffixMode (step mode).next := by
  cases suffix with
  | loop current => exact loopStep_next_suffix current
  | residual current => exact residualStep_next_suffix current

/-- Every finite number of whole controller chunks after chart entry has a
finite trace of exactly its normalized sector blocks.  This theorem is about
the optional proof sidecar; bit-by-bit productivity remains the independent
`Machine.productive` theorem. -/
theorem exists_trace (mode : Mode) (suffix : SuffixMode mode) :
    ∀ _count : Nat,
      ∃ after : Mode, ∃ blocks : List Block,
        SuffixMode after ∧ Trace mode after blocks
  | 0 => ⟨mode, [], suffix, .done mode⟩
  | count + 1 => by
      let middle := (step mode).next
      have middleSuffix : SuffixMode middle := suffixStep_next suffix
      rcases exists_trace middle middleSuffix count with
        ⟨after, blocks, afterSuffix, rest⟩
      rcases suffixStep_accounted suffix with
        neutral | ⟨entry, contracting⟩
      · exact ⟨after, blocks, afterSuffix, .neutral neutral rest⟩
      · exact ⟨after, entry :: blocks, afterSuffix,
          .sector entry contracting rest⟩

/-! ## Terminal unary accuracy -/

/-- The residual decision's affine-or-`omega` witness is exactly the
homogeneous residual tail used by the machine. -/
theorem loopTailOfSmall_point_equivalent_homogeneous
    {count : Nat} {ball : CCL.ArithmeticEnclosures.Ball}
    (small : CCL.ResidualDecision.SmallBall ball
      (CCL.ResidualDecision.paddingTarget count))
    (residual : Gaussian) (inside : ball.Contains residual) :
    (CCL.ResidualDecision.loopTailOfSmall
      small residual inside).point.Equivalent ⟨1, gamma * residual⟩ := by
  unfold CCL.ResidualDecision.loopTailOfSmall
  split
  · rename_i residualZero
    simp only [CCL.TerminalPadding.LoopTail.point,
      CCL.Proj.omega, CCL.Proj.Equivalent]
    rw [residualZero, RFAP.ConstructiveGaussian.Gaussian.mul_zero]
  · rename_i residualNonzero
    let product := gamma * residual
    have productNonzero : product ≠ 0 :=
      mul_ne_zero_direct (by decide) residualNonzero
    simp only [CCL.TerminalPadding.LoopTail.point,
      CCL.Proj.affine, CCL.Proj.Equivalent]
    change product⁻¹ * product = 1 * 1
    rw [RFAP.ConstructiveGaussian.Gaussian.mul_one]
    exact RFAP.CanonicalGaussian.Gaussian.inv_mul_cancel
      product productNonzero

/-- Pairwise transported diameter of a small residual chart.  This is the
productive exact-result case: even if no later sector ever occurs, increasing
unary padding count drives the explicit rational bound to zero. -/
theorem residualSmall_pair_chordalSq_act_le
    (count : Nat) (ball : CCL.ArithmeticEnclosures.Ball)
    (small : CCL.ResidualDecision.SmallBall ball
      (CCL.ResidualDecision.paddingTarget count))
    (matrix : Mat2)
    (determinantNonzero :
      CCL.CCLPullback.determinant matrix ≠ 0)
    {left right : Gaussian}
    (leftInside : ball.Contains left) (rightInside : ball.Contains right) :
    CCL.Chordal.chordalSq
        (CCL.Mat2.act matrix ⟨1, gamma * left⟩)
        (CCL.Mat2.act matrix ⟨1, gamma * right⟩) ≤
      4 * (CCL.TerminalPadding.terminalCoefficient matrix /
        (1 + (2 : Coordinate) ^ count)) := by
  let leftTail := CCL.ResidualDecision.loopTailOfSmall
    small left leftInside
  let rightTail := CCL.ResidualDecision.loopTailOfSmall
    small right rightInside
  let leftHomogeneous : Proj := ⟨1, gamma * left⟩
  let rightHomogeneous : Proj := ⟨1, gamma * right⟩
  let omegaImage := CCL.Mat2.act matrix (CCL.Proj.omega : Proj)
  let bound := CCL.TerminalPadding.terminalCoefficient matrix /
    (1 + (2 : Coordinate) ^ count)
  have leftEquivalent : leftTail.point.Equivalent leftHomogeneous :=
    loopTailOfSmall_point_equivalent_homogeneous small left leftInside
  have rightEquivalent : rightTail.point.Equivalent rightHomogeneous :=
    loopTailOfSmall_point_equivalent_homogeneous small right rightInside
  have leftTailValid := leftTail.valid
  have rightTailValid := rightTail.valid
  have leftHomogeneousValid :
      CCL.Chordal.Proj.HasNonzeroCoordinate leftHomogeneous := by
    change (1 : Gaussian) ≠ 0 ∨ _
    exact Or.inl one_ne_zero
  have rightHomogeneousValid :
      CCL.Chordal.Proj.HasNonzeroCoordinate rightHomogeneous := by
    change (1 : Gaussian) ≠ 0 ∨ _
    exact Or.inl one_ne_zero
  have omegaValid := CCL.Chordal.Proj.omega_hasNonzeroCoordinate
  have leftTailImageValid :=
    CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      determinantNonzero leftTailValid
  have rightTailImageValid :=
    CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      determinantNonzero rightTailValid
  have leftImageValid :=
    CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      determinantNonzero leftHomogeneousValid
  have rightImageValid :=
    CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      determinantNonzero rightHomogeneousValid
  have omegaImageValid :=
    CCL.Chordal.Mat2.act_hasNonzeroCoordinate
      determinantNonzero omegaValid
  have leftImageEquivalent :=
    CCL.Mat2.act_respects_equivalent matrix leftEquivalent
  have rightImageEquivalent :=
    CCL.Mat2.act_respects_equivalent matrix rightEquivalent
  have leftDistance :
      CCL.Chordal.chordalSq
          (CCL.Mat2.act matrix leftHomogeneous) omegaImage ≤ bound := by
    calc
      CCL.Chordal.chordalSq
          (CCL.Mat2.act matrix leftHomogeneous) omegaImage =
          CCL.Chordal.chordalSq
            (CCL.Mat2.act matrix leftTail.point) omegaImage :=
        (CCL.Chordal.chordalSq_eq_of_equivalent_left
          leftTailImageValid leftImageValid leftImageEquivalent omegaImage).symm
      _ ≤ bound :=
        CCL.TerminalPadding.chordalSq_act_loopTail_le
          matrix determinantNonzero leftTail
  have rightDistance :
      CCL.Chordal.chordalSq omegaImage
          (CCL.Mat2.act matrix rightHomogeneous) ≤ bound := by
    calc
      CCL.Chordal.chordalSq omegaImage
          (CCL.Mat2.act matrix rightHomogeneous) =
          CCL.Chordal.chordalSq
            (CCL.Mat2.act matrix rightHomogeneous) omegaImage :=
        CCL.Chordal.chordalSq_comm _ _
      _ = CCL.Chordal.chordalSq
          (CCL.Mat2.act matrix rightTail.point) omegaImage :=
        (CCL.Chordal.chordalSq_eq_of_equivalent_left
          rightTailImageValid rightImageValid rightImageEquivalent
            omegaImage).symm
      _ ≤ bound :=
        CCL.TerminalPadding.chordalSq_act_loopTail_le
          matrix determinantNonzero rightTail
  calc
    CCL.Chordal.chordalSq
        (CCL.Mat2.act matrix leftHomogeneous)
        (CCL.Mat2.act matrix rightHomogeneous) ≤
        2 * (CCL.Chordal.chordalSq
              (CCL.Mat2.act matrix leftHomogeneous) omegaImage +
            CCL.Chordal.chordalSq omegaImage
              (CCL.Mat2.act matrix rightHomogeneous)) :=
      CCL.Chordal.chordalSq_triangle_two
        leftImageValid omegaImageValid rightImageValid
    _ ≤ 2 * (bound + bound) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add leftDistance rightDistance) (by decide)
    _ = 4 * (CCL.TerminalPadding.terminalCoefficient matrix /
        (1 + (2 : Coordinate) ^ count)) := by
      dsimp only [bound]
      ring1

/-- The certificate above is attached to the sector branch actually returned
by `loopStep`; it is not a hypothetical alternate decoder. -/
theorem loopStep_next_of_sector
    (current : LoopState) (sector : CCL.Sectors.Sector)
    (certificate : CCL.RedundantOutput.SafeBall sector
      (current.process.ball
        (current.domain.refinedState current.state)))
    (selected : current.domain.decide current.state =
      .sector sector certificate) :
    (loopStep current).next =
      .residual (loopSectorResidualState current sector certificate) := by
  unfold loopStep
  rw [selected]

end CCL.ProgressiveMachineContraction
