import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import CCL.Persistent.Terminal
import CCL.Boundary.Denominator
import CCL.Boundary.EqualityOwner

/-!
# Finite dispatch through initial CCL boundary ownership

One persistent controller step first separates the current box from the
single affine pole of its decoder matrix, then removes the bounded set of
rational terminals, and finally inspects the current nonterminal child
formula.  It either executes a box-stable strict-sign/equality-owned step or
retains the first genuinely parameterized Hermitian boundary with its
analysis and a uniform positive decoder-denominator margin.  Universal zero
boundaries are discharged structurally, and finite zero sets are exhausted
by a bounded form-cache loop.  Coupling the remaining curve events to the
persistent sample provider remains.
-/

namespace CCL.PersistentCCLDispatch

abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev State := CCL.PersistentCCL.State
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack
abbrev StepResult
    {p : GaussianPolynomial} {ambient : Box} (current : State p ambient) :=
  CCL.PersistentCCL.StepResult current
abbrev Prepared
    {p : GaussianPolynomial} {ambient : Box} (current : State p ambient) :=
  CCL.PersistentCCLTerminal.Prepared current
abbrev BoundaryNext
    {p : GaussianPolynomial} {ambient : Box} (current : State p ambient) :=
  CCL.PersistentCCLStrict.BoundaryNext current
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev FormOverride := CCL.CCLFormulaBoxSign.FormOverride

/-- Positive denominator separation restricted to the fully prepared state.
This is the quantitative input needed to bound affine line parameters in the
subsequent boundary-owner calculation. -/
structure DenominatorCertificate
    {p : GaussianPolynomial} {ambient : Box}
    {current : State p ambient} (prepared : Prepared current) where
  margin : RFAP.ConstructiveFraction.Rational
  margin_pos : 0 < margin
  lower : ∀ {value : RFAP.ConstructiveGaussian.Gaussian},
    prepared.state.numerical.box.Contains value →
      margin ≤ RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.RawParser.denominator
          (CCL.CCLPullback.adjugate
            (CCL.RawParser.parse prepared.state.word).matrix)
          value)

/-- A genuinely parameterized boundary is the only unresolved result that
may leave the finite-boundary loop.  Universal boundaries are equality-owned
by structural inspection, while finite zero sets are exhausted by winding
point exclusion. -/
structure CurveBoundary
    (p : GaussianPolynomial) (reference : CCL.GaussianProjective.Mat2)
    (current : Box) (denominatorMargin : RFAP.ConstructiveFraction.Rational)
    (marginPositive : 0 < denominatorMargin)
    (atom : CCL.CCLFormula.Atom) where
  source : CCL.CCLBoundaryDescription.CurveSource
    reference atom.form
  analyses : List (Sigma fun chart :
    CCL.CCLBoundaryCharts.BoundedChart atom.form =>
      CCL.CCLBoundaryCharts.BoundedAnalysis p current chart)
  analyses_eq : analyses =
    CCL.CCLBoundaryCharts.analyzeCharts p source current
      denominatorMargin marginPositive

/-- Total result of terminal preparation followed by structural strict-sign
and exact equality-owner inspection. -/
inductive Dispatch
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) where
  | decided (result : StepResult current)
  | boundary (prepared : Prepared current)
      (denominator : DenominatorCertificate prepared)
      (next : BoundaryNext prepared.state)
      (boundary : CurveBoundary p
        (CCL.CCLPullback.adjugate
          (CCL.RawParser.parse prepared.state.word).matrix)
        prepared.state.numerical.box denominator.margin
        denominator.margin_pos next.atom)

/-- Every atom form that can occur in either local child formula at a fixed
raw prefix.  The list deliberately retains duplicates: erasing the first
occurrence of a newly resolved form still gives a strict natural measure,
and the cache prevents that form from being returned again. -/
private def candidateForms (word : List Bool) : List HermitianForm :=
  let parser := CCL.RawParser.parse word
  (((CCL.CCLNextBit.inputIncrementalAdvanceFormula parser false).atoms ++
    (CCL.CCLNextBit.inputIncrementalAdvanceFormula parser true).atoms).map
      fun atom => atom.form)

private theorem form_mem_candidateForms
    (word : List Bool) (bit : Bool)
    {atom : CCL.CCLFormula.Atom}
    (member : atom ∈
      (CCL.CCLNextBit.inputIncrementalAdvanceFormula
        (CCL.RawParser.parse word) bit).atoms) :
    atom.form ∈ candidateForms word := by
  apply QuotientFreeList.mem_map.mpr
  refine ⟨atom, ?_, rfl⟩
  cases bit with
  | false => exact List.mem_append_left _ member
  | true => exact List.mem_append_right _ member

/-- Choice-free first-occurrence deletion for the finite form measure.  The
generic library theorems about `List.erase` have a broader axiom closure than
their executable definition, so the two facts needed here are proved
directly by structural recursion. -/
private def eraseForm (target : HermitianForm) :
    List HermitianForm → List HermitianForm
  | [] => []
  | form :: remaining =>
      if form = target then remaining else form :: eraseForm target remaining

private theorem mem_eraseForm_of_ne
    {target other : HermitianForm} {forms : List HermitianForm}
    (different : other ≠ target) (member : other ∈ forms) :
    other ∈ eraseForm target forms := by
  induction forms with
  | nil => simp at member
  | cons form remaining inductionHypothesis =>
      rcases List.mem_cons.mp member with equal | tailMember
      · subst form
        simp [eraseForm, different]
      · by_cases equal : form = target
        · simp [eraseForm, equal, tailMember]
        · simp [eraseForm, equal, inductionHypothesis tailMember]

private theorem length_eraseForm_lt
    {target : HermitianForm} {forms : List HermitianForm}
    (member : target ∈ forms) :
    (eraseForm target forms).length < forms.length := by
  induction forms with
  | nil => simp at member
  | cons form remaining inductionHypothesis =>
      by_cases equal : form = target
      · simp [eraseForm, equal]
      · have tailMember : target ∈ remaining := by
          rcases List.mem_cons.mp member with head | tail
          · exact (equal head.symm).elim
          · exact tail
        have shorter := inductionHypothesis tailMember
        simp only [eraseForm, if_neg equal, List.length_cons]
        omega

/-- Refining a box preserves every cached form sign. -/
private theorem findFormOverride_refine_ne_none
    {outer inner : Box} (overrides : List (FormOverride outer))
    (refines : inner.Refines outer) (target : HermitianForm)
    (found : CCL.CCLFormulaBoxSign.findFormOverride
      overrides target ≠ none) :
    CCL.CCLFormulaBoxSign.findFormOverride
      (overrides.map fun override => override.refine refines) target ≠ none := by
  induction overrides with
  | nil => exact (found rfl).elim
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨form, stability⟩
      cases stability with
      | negative holds =>
          by_cases equal : form = target
          · simp [CCL.CCLFormulaBoxSign.findFormOverride,
              CCL.CCLFormulaBoxSign.FormOverride.refine, equal]
          · have tailFound :
                CCL.CCLFormulaBoxSign.findFormOverride
                  remaining target ≠ none := by
              simpa [CCL.CCLFormulaBoxSign.findFormOverride,
                equal] using found
            simpa [CCL.CCLFormulaBoxSign.findFormOverride,
              CCL.CCLFormulaBoxSign.FormOverride.refine,
              equal] using inductionHypothesis tailFound
      | positive holds =>
          by_cases equal : form = target
          · simp [CCL.CCLFormulaBoxSign.findFormOverride,
              CCL.CCLFormulaBoxSign.FormOverride.refine, equal]
          · have tailFound :
                CCL.CCLFormulaBoxSign.findFormOverride
                  remaining target ≠ none := by
              simpa [CCL.CCLFormulaBoxSign.findFormOverride,
                equal] using found
            simpa [CCL.CCLFormulaBoxSign.findFormOverride,
              CCL.CCLFormulaBoxSign.FormOverride.refine,
              equal] using inductionHypothesis tailFound
      | zero holds =>
          by_cases equal : form = target
          · simp [CCL.CCLFormulaBoxSign.findFormOverride,
              CCL.CCLFormulaBoxSign.FormOverride.refine, equal]
          · have tailFound :
                CCL.CCLFormulaBoxSign.findFormOverride
                  remaining target ≠ none := by
              simpa [CCL.CCLFormulaBoxSign.findFormOverride,
                equal] using found
            simpa [CCL.CCLFormulaBoxSign.findFormOverride,
              CCL.CCLFormulaBoxSign.FormOverride.refine,
              equal] using inductionHypothesis tailFound

/-- Adding one cache entry preserves every form already found in the tail. -/
private theorem findFormOverride_cons_ne_none
    {current : Box} (entry : FormOverride current)
    (overrides : List (FormOverride current)) (target : HermitianForm)
    (found : CCL.CCLFormulaBoxSign.findFormOverride
      overrides target ≠ none) :
    CCL.CCLFormulaBoxSign.findFormOverride
      (entry :: overrides) target ≠ none := by
  by_cases equal : entry.form = target
  · simp [CCL.CCLFormulaBoxSign.findFormOverride, equal]
  · simpa [CCL.CCLFormulaBoxSign.findFormOverride, equal] using found

/-- Lift a prepared state's stable one-bit result back through all same-prefix
finite-boundary refinements to the dispatcher input. -/
private def liftStable
    {p : GaussianPolynomial} {ambient : Box}
    {current : State p ambient} (prepared : Prepared current)
    (stable : CCL.PersistentCCLStrict.StableNext prepared.state) :
    StepResult current :=
  .next stable.bit stable.state prepared.boxRefines (by
    rw [CCL.PersistentCCLStrict.StableNext.state_word,
      prepared.word_eq])

/-- Eliminate finite equality boundaries.  `unresolved` is exactly the
finite multiset of forms not yet known to have a reusable sign.  A returned
finite boundary belongs to one of the two child formulas; if it is absent
from the cache it must therefore occur in `unresolved`.  Winding exclusion
adds its positive sign to the cache and erases one occurrence, so the
recursion is structural on a strictly decreasing explicit finite list. -/
private def dispatchFinite
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient)
    {current : State p ambient}
    (prepared : Prepared current)
    (denominator : DenominatorCertificate prepared)
    (unresolved : List HermitianForm)
    (overrides : List (FormOverride prepared.state.numerical.box))
    (covered : ∀ (bit : Bool) (atom : CCL.CCLFormula.Atom),
      atom ∈ (CCL.CCLNextBit.inputIncrementalAdvanceFormula
        (CCL.RawParser.parse prepared.state.word) bit).atoms →
      atom.form ∈ unresolved ∨
        CCL.CCLFormulaBoxSign.findFormOverride
          overrides atom.form ≠ none) :
    Dispatch current := by
  match CCL.CCLEqualityOwner.inspectNextWith prepared.state
      denominator.margin denominator.margin_pos overrides with
  | .terminal terminal =>
      have impossible : False := by
        rcases prepared.canContinue prepared.state.currentSample with
          ⟨bit, canStep⟩
        exact terminal.none bit canStep
      exact impossible.elim
  | .stable stable => exact .decided (liftStable prepared stable)
  | .boundary next notResolved remaining =>
      cases remaining with
      | curve source analyses analysesEq =>
          exact .boundary prepared denominator next
            { source := source
              analyses := analyses
              analyses_eq := analysesEq }
      | finite points complete nonnegative _evaluations _evaluationsEq =>
          have atomUnresolved : next.atom.form ∈ unresolved := by
            rcases covered next.bit next.atom next.member with member | found
            · exact member
            · exact (found notResolved).elim
          match CCL.CCLEqualityOwner.resolveFinite degreePositive
              track prepared.state next.atom points complete nonnegative with
          | .exact root =>
              exact .decided (.exact
                { point := root.point
                  root := root.root
                  inside := prepared.boxRefines.contains root.inside })
          | .positive state boxRefines wordEq stability formEq =>
              let nextPrepared : Prepared current :=
                { state := state
                  boxRefines := boxRefines.trans prepared.boxRefines
                  word_eq := wordEq.trans prepared.word_eq
                  canContinue := fun sample => by
                    let priorSample :
                        CCL.PersistentCCL.CompatibleSample
                          prepared.state.word prepared.state.numerical.box :=
                      { point := sample.point
                        inside := boxRefines.contains sample.inside
                        nonzero := sample.nonzero
                        represented := by
                          simpa only [wordEq] using sample.represented }
                    rcases prepared.canContinue priorSample with
                      ⟨bit, canStep⟩
                    exact ⟨bit, by simpa only [wordEq] using canStep⟩ }
              let refinedOverrides :=
                overrides.map fun override => override.refine boxRefines
              let nextOverrides : List
                  (FormOverride nextPrepared.state.numerical.box) :=
                stability :: refinedOverrides
              let nextUnresolved := eraseForm next.atom.form unresolved
              have nextCovered : ∀ (bit : Bool)
                  (other : CCL.CCLFormula.Atom),
                  other ∈
                    (CCL.CCLNextBit.inputIncrementalAdvanceFormula
                      (CCL.RawParser.parse
                        nextPrepared.state.word) bit).atoms →
                  other.form ∈ nextUnresolved ∨
                    CCL.CCLFormulaBoxSign.findFormOverride
                      nextOverrides other.form ≠ none := by
                intro bit other member
                have sameWord : nextPrepared.state.word =
                    prepared.state.word := wordEq
                have priorMember : other ∈
                    (CCL.CCLNextBit.inputIncrementalAdvanceFormula
                      (CCL.RawParser.parse
                        prepared.state.word) bit).atoms := by
                  simpa only [sameWord] using member
                rcases covered bit other priorMember with candidate | found
                · by_cases equal : other.form = next.atom.form
                  · right
                    have headEqual : stability.form = other.form := by
                      rw [formEq]
                      exact equal.symm
                    simp only [nextOverrides,
                      CCL.CCLFormulaBoxSign.findFormOverride]
                    simp [headEqual]
                  · left
                    exact mem_eraseForm_of_ne equal candidate
                · right
                  exact findFormOverride_cons_ne_none stability
                    refinedOverrides other.form
                    (findFormOverride_refine_ne_none overrides boxRefines
                      other.form found)
              let nextDenominator : DenominatorCertificate nextPrepared :=
                { margin := denominator.margin
                  margin_pos := denominator.margin_pos
                  lower := by
                    intro value inside
                    have lower := denominator.lower
                      (boxRefines.contains inside)
                    have sameWord : nextPrepared.state.word =
                        prepared.state.word := wordEq
                    simpa only [sameWord] using lower }
              exact dispatchFinite degreePositive track nextPrepared
                nextDenominator nextUnresolved nextOverrides nextCovered
termination_by unresolved.length
decreasing_by
  exact length_eraseForm_lt atomUnresolved

/-- Execute denominator and terminal preparation, exhaust every finite
equality boundary, and either append one stable bit or return the first
genuinely parameterized curve event. -/
def dispatch
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient) :
    Dispatch current := by
  let parser := CCL.RawParser.parse current.word
  let inverse := CCL.CCLPullback.adjugate parser.matrix
  have inverseDeterminantNonzero :
      CCL.Chordal.Mat2.det inverse ≠ 0 := by
    change CCL.CCLPullback.determinant
      (CCL.CCLPullback.adjugate parser.matrix) ≠ 0
    rw [CCL.CCLPullback.determinant_adjugate]
    simpa only [parser, CCL.CCLPullback.determinant] using
      CCL.RawParser.parse_det_ne current.word
  match CCL.CCLDenominator.decide degreePositive track
      current.numerical inverse
      (CCL.CCLDenominator.lowerRow_ne_of_determinant_ne inverse
        inverseDeterminantNonzero) with
  | .exact point root inside _denominatorZero =>
      exact .decided (.exact ⟨point, root, inside⟩)
  | .separated separated =>
    let separatedState := current.refine separated.state separated.refines
    match CCL.PersistentCCLTerminal.prepare degreePositive track
        separatedState with
    | .exact root =>
      exact .decided (.exact
        { point := root.point
          root := root.root
          inside := separated.refines.contains root.inside })
    | .ready localPrepared =>
      let prepared : Prepared current :=
        { state := localPrepared.state
          boxRefines := localPrepared.boxRefines.trans separated.refines
          word_eq := by
            simpa only [separatedState,
              CCL.PersistentCCL.State.refine_word] using
              localPrepared.word_eq
          canContinue := localPrepared.canContinue }
      let denominator : DenominatorCertificate prepared :=
        { margin := separated.margin
          margin_pos := separated.margin_pos
          lower := by
            intro value inside
            have lower := separated.lower
              (localPrepared.boxRefines.contains inside)
            have wordIdentity : prepared.state.word = current.word :=
              prepared.word_eq
            simpa only [wordIdentity, parser, inverse] using lower }
      exact dispatchFinite degreePositive track prepared denominator
        (candidateForms prepared.state.word) [] (by
          intro bit atom member
          exact Or.inl (form_mem_candidateForms
            prepared.state.word bit member))

end CCL.PersistentCCLDispatch
