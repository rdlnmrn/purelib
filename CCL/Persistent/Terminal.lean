import CCL.Persistent.Strict
import CCL.Boundary.TerminalCandidates
import CCL.Boundary.WindingPointExclusion

/-!
# Resolving rational terminal samples on a persistent CCL track

Every displayed Gaussian-rational sample has a finite CCL terminal.  Reaching
that terminal while constructing a persistent prefix therefore does not by
itself mean that the polynomial root is rational.  This module makes the
necessary distinction executable: evaluate the polynomial at the displayed
terminal point; return an exact root when it vanishes, otherwise perform one
coefficient-computed winding-one refinement that excludes that point.
-/

namespace CCL.PersistentCCLTerminal

abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev State := CCL.PersistentCCL.State
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack

open CCL.PersistentCCL

/-- A same-prefix refinement that proves the previously terminal displayed
sample is no longer in the numerical box. -/
structure Escaped
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) where
  state : State p ambient
  refines : StateRefines state current
  excluded : ¬state.numerical.box.Contains current.currentSample.point

/-- Result of inspecting a local affine-terminal decision. -/
inductive Resolution
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) where
  | exact (root : ExactRootIn p current.numerical.box)
  | escaped (result : Escaped current)

/-- If the current compatible sample is locally terminal, decide whether it
is an exact polynomial root.  A nonroot is removed by one explicit shrinking
track request while the existing persistent prefix is retained. -/
def resolve?
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) :
    Option (Resolution current) :=
  let sample := current.currentSample
  match sample.nextDecision.decision with
  | .next _ _ _ => none
  | .terminal _ =>
      if root : p.eval sample.point = 0 then
        some (.exact ⟨sample.point, root, sample.inside⟩)
      else
        let numerical :=
          CCL.WindingPointExclusion.refinePastPoint
            track current.numerical sample.point root
        let boxRefines :=
          CCL.WindingPointExclusion.refinePastPoint_refines
            track current.numerical sample.point root
        let state := current.refine numerical boxRefines
        some (.escaped
          { state := state
            refines := ⟨boxRefines, List.prefix_refl current.word⟩
            excluded := by
              exact CCL.WindingPointExclusion.refinePastPoint_excludes
                degreePositive track current.numerical sample.point root })

/-- Result of resolving one fixed affine point against a winding-one state.
An exact root is returned only when the point is in the current box;
otherwise the returned state finitely certifies that the point is outside. -/
inductive PointResolution
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) (point : Gaussian) where
  | exact (root : ExactRootIn p current.numerical.box)
  | excluded (state : State p ambient)
      (boxRefines : state.numerical.box.Refines current.numerical.box)
      (word_eq : state.word = current.word)
      (outside : ¬state.numerical.box.Contains point)

/-- Decide a fixed candidate.  A nonroot is excluded by one
coefficient-computed track refinement; an already-outside exact root needs no
refinement. -/
def resolvePoint
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (point : Gaussian) : PointResolution current point := by
  if root : p.eval point = 0 then
    if inside : current.numerical.box.Contains point then
      exact .exact ⟨point, root, inside⟩
    else
      exact .excluded current
        (RFAP.Boxes.Box.refines_refl current.numerical.box) rfl
        inside
  else
    let numerical :=
      CCL.WindingPointExclusion.refinePastPoint
        track current.numerical point root
    let boxRefines :=
      CCL.WindingPointExclusion.refinePastPoint_refines
        track current.numerical point root
    let state := current.refine numerical boxRefines
    exact .excluded state boxRefines rfl
      (CCL.WindingPointExclusion.refinePastPoint_excludes
        degreePositive track current.numerical point root)

/-- Bounded outcome after resolving both possible terminals of a two-bit
sector phase. -/
inductive PairResolution
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) (left right : Gaussian) where
  | exact (root : ExactRootIn p current.numerical.box)
  | excluded (state : State p ambient)
      (boxRefines : state.numerical.box.Refines current.numerical.box)
      (word_eq : state.word = current.word)
      (leftOutside : ¬state.numerical.box.Contains left)
      (rightOutside : ¬state.numerical.box.Contains right)

/-- Resolve the two phase-computable terminal candidates in at most two
winding-track refinements. -/
def resolvePair
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (left right : Gaussian) : PairResolution current left right := by
  match resolvePoint degreePositive track current left with
  | .exact root => exact .exact root
  | .excluded leftState leftRefines leftWord leftOutside =>
      match resolvePoint degreePositive track leftState right with
      | .exact root =>
          exact .exact
            { point := root.point
              root := root.root
              inside := leftRefines.contains root.inside }
      | .excluded rightState rightRefines rightWord rightOutside =>
          exact .excluded rightState (rightRefines.trans leftRefines)
            (rightWord.trans leftWord) (by
              intro inside
              exact leftOutside (rightRefines.contains inside)) rightOutside

/-- Bounded outcome after resolving an arbitrary displayed finite boundary
list. -/
inductive PointsResolution
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) (points : List RFAP.ConstructiveGaussian.Gaussian) where
  | exact (root : ExactRootIn p current.numerical.box)
  | excluded (state : State p ambient)
      (boxRefines : state.numerical.box.Refines current.numerical.box)
      (word_eq : state.word = current.word)
      (outside : ∀ point, point ∈ points →
        ¬state.numerical.box.Contains point)

/-- Resolve every member of one explicit finite zero set.  The first
displayed polynomial root is returned; otherwise the final same-prefix
winding state excludes the whole list. -/
def resolvePoints
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) :
    (points : List RFAP.ConstructiveGaussian.Gaussian) →
      PointsResolution current points
  | [] => .excluded current
      (RFAP.Boxes.Box.refines_refl current.numerical.box) rfl
      (by intro point member; simp at member)
  | point :: points =>
      match resolvePoint degreePositive track current point with
      | .exact root => .exact root
      | .excluded next nextRefines nextWord pointOutside =>
          match resolvePoints degreePositive track next points with
          | .exact root => .exact
              { point := root.point
                root := root.root
                inside := nextRefines.contains root.inside }
          | .excluded final finalRefines finalWord remainingOutside =>
              .excluded final (finalRefines.trans nextRefines)
                (finalWord.trans nextWord) (by
                  intro target member inside
                  rcases List.mem_cons.mp member with equal | tailMember
                  · subst target
                    exact pointOutside (finalRefines.contains inside)
                  · exact remainingOutside target tailMember inside)

/-- A prepared state has removed every possible local rational terminal.
Consequently every compatible sample in its box admits a next raw bit. -/
structure Prepared
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) where
  state : State p ambient
  boxRefines : state.numerical.box.Refines current.numerical.box
  word_eq : state.word = current.word
  canContinue :
    ∀ sample : CompatibleSample state.word state.numerical.box,
      ∃ bit, CCL.RawParserSemantics.CanStep
        (CCL.RawParser.parse state.word) sample.point bit

/-- Total bounded preparation outcome. -/
inductive Preparation
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) where
  | exact (root : ExactRootIn p current.numerical.box)
  | ready (result : Prepared current)

private theorem canContinue_of_no_terminal_phase
    {word : List Bool} {box : Box}
    (sample : CompatibleSample word box)
    (notTerminalPhase : ¬∃ kind exponent first second,
      (CCL.RawParser.parse word).phase =
        .sector kind exponent (.two first second)) :
    ∃ bit, CCL.RawParserSemantics.CanStep
      (CCL.RawParser.parse word) sample.point bit := by
  rcases sample.represented with ⟨before, represents⟩
  let parser := CCL.RawParser.parse word
  cases CCL.ParserStep.decideLocal parser sample.point before
      (CCL.RawParser.parse_det_ne word) represents with
  | next bit possible _ => exact ⟨bit, possible⟩
  | terminal none =>
      have noAdvance : ∀ bit,
          ¬CCL.ParserStep.CanAdvanceAt parser bit before := by
        intro bit advance
        exact none bit
          ((CCL.ParserStep.canStep_iff_canAdvanceAt parser
            sample.point before (CCL.RawParser.parse_det_ne word)
            represents bit).2 advance)
      exact (notTerminalPhase
        (CCL.CCLTerminalCandidates.phase_eq_sectorTwo_of_no_advance
          parser sample.point before represents noAdvance)).elim

private theorem canContinue_of_candidates_outside
    {word : List Bool} {box : Box}
    (sample : CompatibleSample word box)
    (kind : CCL.RawParser.BlockKind) (exponent : Nat)
    (first second : Bool)
    (phase : (CCL.RawParser.parse word).phase =
      .sector kind exponent (.two first second))
    (leftOutside : ¬box.Contains
      (CCL.CCLTerminalCandidates.candidateInput
        (CCL.RawParser.parse word) kind exponent first second false))
    (rightOutside : ¬box.Contains
      (CCL.CCLTerminalCandidates.candidateInput
        (CCL.RawParser.parse word) kind exponent first second true)) :
    ∃ bit, CCL.RawParserSemantics.CanStep
      (CCL.RawParser.parse word) sample.point bit := by
  rcases sample.represented with ⟨before, represents⟩
  let parser := CCL.RawParser.parse word
  cases CCL.ParserStep.decideLocal parser sample.point before
      (CCL.RawParser.parse_det_ne word) represents with
  | next bit possible _ => exact ⟨bit, possible⟩
  | terminal none =>
      have noAdvance : ∀ bit,
          ¬CCL.ParserStep.CanAdvanceAt parser bit before := by
        intro bit advance
        exact none bit
          ((CCL.ParserStep.canStep_iff_canAdvanceAt parser
            sample.point before (CCL.RawParser.parse_det_ne word)
            represents bit).2 advance)
      rcases
          CCL.CCLTerminalCandidates.input_eq_candidate_of_sectorTwo_terminal
            parser sample.point before kind exponent first second phase
            represents noAdvance with left | right
      · exact (leftOutside (left ▸ sample.inside)).elim
      · exact (rightOutside (right ▸ sample.inside)).elim

/-- Before choosing a persistent child, remove the complete finite set of
local rational terminals.  Non-sector-two phases require no refinement;
sector-two phases inspect exactly two candidate points. -/
def prepare
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) :
    Preparation current := by
  let parser := CCL.RawParser.parse current.word
  cases phase : parser.phase with
  | initial =>
      exact .ready
        { state := current
          boxRefines := RFAP.Boxes.Box.refines_refl _
          word_eq := rfl
          canContinue := fun sample =>
            canContinue_of_no_terminal_phase sample (by
              rintro ⟨kind, exponent, first, second, equal⟩
              rw [phase] at equal
              contradiction) }
  | highUnary count =>
      exact .ready
        { state := current
          boxRefines := RFAP.Boxes.Box.refines_refl _
          word_eq := rfl
          canContinue := fun sample =>
            canContinue_of_no_terminal_phase sample (by
              rintro ⟨kind, exponent, first, second, equal⟩
              rw [phase] at equal
              contradiction) }
  | lowUnary count =>
      exact .ready
        { state := current
          boxRefines := RFAP.Boxes.Box.refines_refl _
          word_eq := rfl
          canContinue := fun sample =>
            canContinue_of_no_terminal_phase sample (by
              rintro ⟨kind, exponent, first, second, equal⟩
              rw [phase] at equal
              contradiction) }
  | loopUnary count =>
      exact .ready
        { state := current
          boxRefines := RFAP.Boxes.Box.refines_refl _
          word_eq := rfl
          canContinue := fun sample =>
            canContinue_of_no_terminal_phase sample (by
              rintro ⟨kind, exponent, first, second, equal⟩
              rw [phase] at equal
              contradiction) }
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          exact .ready
            { state := current
              boxRefines := RFAP.Boxes.Box.refines_refl _
              word_eq := rfl
              canContinue := fun sample =>
                canContinue_of_no_terminal_phase sample (by
                  rintro ⟨otherKind, otherExponent, first, second, equal⟩
                  rw [phase] at equal
                  cases equal) }
      | one first =>
          exact .ready
            { state := current
              boxRefines := RFAP.Boxes.Box.refines_refl _
              word_eq := rfl
              canContinue := fun sample =>
                canContinue_of_no_terminal_phase sample (by
                  rintro ⟨otherKind, otherExponent, otherFirst, second, equal⟩
                  rw [phase] at equal
                  cases equal) }
      | two first second =>
          let left :=
            CCL.CCLTerminalCandidates.candidateInput parser kind
              exponent first second false
          let right :=
            CCL.CCLTerminalCandidates.candidateInput parser kind
              exponent first second true
          match resolvePair degreePositive track current left right with
          | .exact root => exact .exact root
          | .excluded state boxRefines wordEq leftOutside rightOutside =>
              exact .ready
                { state := state
                  boxRefines := boxRefines
                  word_eq := wordEq
                  canContinue := fun sample => by
                    have stateWord : state.word = current.word := wordEq
                    have parserPhase :
                        (CCL.RawParser.parse state.word).phase =
                          .sector kind exponent (.two first second) := by
                      rw [stateWord]
                      exact phase
                    apply canContinue_of_candidates_outside sample kind exponent
                      first second parserPhase
                    · simpa only [stateWord, parser, left] using leftOutside
                    · simpa only [stateWord, parser, right] using rightOutside }

end CCL.PersistentCCLTerminal
