import CCL.Boundary.FormulaBoxSign
import CCL.Boundary.FormulaBoundaries
import CCL.Boundary.Charts
import CCL.Persistent.Strict
import CCL.Persistent.Terminal

/-!
# Finite equality ownership for CCL formula atoms

The parser's weak/strict convention decides every atom exactly at a zero of
its Hermitian form.  This module records that decision as finite data and
lets formula inspection reuse boundaries already proved identically zero.
Consequently a universal boundary is discharged once, and structural
reinspection either proves the complete formula stable or returns a
different unresolved atom.
-/

namespace CCL.CCLEqualityOwner

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev SignTest := CCL.CCLFormula.SignTest
abbrev Atom := CCL.CCLFormula.Atom
abbrev Formula := CCL.CCLFormula.Formula
abbrev Stable := CCL.CCLFormulaBoxSign.Stable
abbrev Override := CCL.CCLFormulaBoxSign.Override
abbrev Reinspection := CCL.CCLFormulaBoxSign.Reinspection
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Mat2 := CCL.GaussianProjective.Mat2
abbrev Description := CCL.CCLBoundaryDescription.Description

open CCL.CCLFormula

/-- The exact boundary decision attached to one of the six finite sign
tests. -/
inductive EqualityDecision (test : SignTest) where
  | owned (holds : test.Holds 0)
  | excluded (fails : ¬test.Holds 0)

/-- Execute the six-case weak/strict equality convention. -/
def decideEquality (test : SignTest) : EqualityDecision test := by
  cases test with
  | negative => exact .excluded (by simp [SignTest.Holds])
  | nonpositive => exact .owned (by simp [SignTest.Holds])
  | zero => exact .owned (by simp [SignTest.Holds])
  | nonzero => exact .excluded (by simp [SignTest.Holds])
  | nonnegative => exact .owned (by simp [SignTest.Holds])
  | positive => exact .excluded (by simp [SignTest.Holds])

/-- An atom whose form vanishes either owns that equality or excludes it,
exactly as reported by its finite sign tag. -/
def atomEqualityDecision (atom : Atom) : EqualityDecision atom.sign :=
  decideEquality atom.sign

theorem atom_holds_of_boundary
    {atom : Atom} {value : Gaussian}
    (boundary : atom.form.eval value = 0)
    (ownedProof : atom.sign.Holds 0)
    (_owned : atomEqualityDecision atom = .owned ownedProof) :
    atom.Holds value := by
  unfold Atom.Holds
  rw [boundary]
  exact ownedProof

theorem atom_not_holds_of_boundary
    {atom : Atom} {value : Gaussian}
    (boundary : atom.form.eval value = 0)
    (excludedProof : ¬atom.sign.Holds 0)
    (_excluded : atomEqualityDecision atom = .excluded excludedProof) :
    ¬atom.Holds value := by
  unfold Atom.Holds
  rw [boundary]
  exact excludedProof

/-- Reinspection after resolving an identically-zero atom either certifies
the entire formula or exposes a genuinely different boundary. -/
inductive UniversalResolution
    (bounding current : Box) (refines : current.Refines bounding)
    (sample : Gaussian) (sampleInside : current.Contains sample)
    (formula : Formula) (resolved : Atom) where
  | stable (result : Stable bounding current formula)
  | boundary (atom : Atom) (member : atom ∈ formula.atoms)
      (different : atom ≠ resolved)
      (failure : CCL.CCLBoxSign.certificate?
        atom.form bounding current refines sample sampleInside = none)

private theorem singleOverride_self_ne_none
    {bounding current : Box} (override : Override bounding current) :
    CCL.CCLFormulaBoxSign.findOverride [override]
      override.atom ≠ none := by
  simp [CCL.CCLFormulaBoxSign.findOverride]

/-- Cache one universal boundary and continue the finite structural
inspection.  The `different` field is the progress measure needed by a
bounded multi-atom owner loop. -/
def resolveUniversal
    (bounding current : Box) (refines : current.Refines bounding)
    (sample : Gaussian) (sampleInside : current.Contains sample)
    (formula : Formula) (resolved : Atom)
    (zero : ∀ value, resolved.form.eval value = 0) :
    UniversalResolution bounding current refines sample sampleInside
      formula resolved := by
  let override : Override bounding current :=
    CCL.CCLFormulaBoxSign.Override.zero resolved
      (fun value _inside => zero value)
  match CCL.CCLFormulaBoxSign.inspectWith bounding current
      [override] formula refines sample sampleInside with
  | .stable stable => exact .stable stable
  | .unresolved atom member notResolved failure =>
      exact .boundary atom member (by
        intro equal
        subst atom
        exact singleOverride_self_ne_none override notResolved) failure

/-! ## Structural owner inspection -/

/-- A non-universal boundary that still requires polynomial/curve handling.
Universal zero forms are converted directly into equality-owned atom
stability and therefore never appear here. -/
inductive RemainingBoundary
    (p : GaussianPolynomial) (reference : Mat2) (current : Box)
    (denominatorMargin : Coordinate) (marginPositive : 0 < denominatorMargin) :
    Atom → Type where
  | curve (atom : Atom)
      (source : CCL.CCLBoundaryDescription.CurveSource
        reference atom.form)
      (analyses : List (Sigma fun chart :
        CCL.CCLBoundaryCharts.BoundedChart atom.form =>
          CCL.CCLBoundaryCharts.BoundedAnalysis p current chart))
      (analyses_eq : analyses =
        CCL.CCLBoundaryCharts.analyzeCharts p source current
          denominatorMargin marginPositive) :
      RemainingBoundary p reference current denominatorMargin marginPositive
        atom
  | finite (atom : Atom) (points : List Gaussian)
      (complete : ∀ value, atom.form.eval value = 0 → value ∈ points)
      (nonnegative : ∀ value, 0 ≤ atom.form.eval value)
      (evaluations : List
        (CCL.CCLBoundaryAnalysis.EvaluatedPoint p))
      (evaluations_eq : evaluations =
        CCL.CCLBoundaryAnalysis.evaluatePoints p points) :
      RemainingBoundary p reference current denominatorMargin marginPositive
        atom

/-- Formula inspection that immediately applies exact equality ownership to
every universal atom it encounters. -/
inductive OwnerInspection
    (p : GaussianPolynomial) (reference : Mat2)
    (bounding current : Box) (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin)
    (refines : current.Refines bounding)
    (sample : Gaussian) (sampleInside : current.Contains sample)
    (formOverrides : List
      (CCL.CCLFormulaBoxSign.FormOverride current)) :
    Formula → Type where
  | stable {formula : Formula} (result : Stable bounding current formula) :
      OwnerInspection p reference bounding current denominatorMargin
        marginPositive refines sample sampleInside formOverrides formula
  | boundary {formula : Formula} (atom : Atom)
      (member : atom ∈ formula.atoms)
      (notResolved : CCL.CCLFormulaBoxSign.findFormOverride
        formOverrides atom.form = none)
      (failure : CCL.CCLBoxSign.certificate?
        atom.form bounding current refines sample sampleInside = none)
      (remaining : RemainingBoundary p reference current denominatorMargin
        marginPositive atom) :
      OwnerInspection p reference bounding current denominatorMargin
        marginPositive refines sample sampleInside formOverrides formula

/-- Traverse one finite formula.  Strictly stable atoms use their ordinary
margin certificates; identically-zero atoms use the parser's equality
convention; the first finite or curve boundary is returned with its complete
bounded analysis. -/
def inspectOwnerWith
    (p : GaussianPolynomial) (reference : Mat2)
    (bounding current : Box) (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin)
    (overrides : List
      (CCL.CCLFormulaBoxSign.Override bounding current))
    (formOverrides : List
      (CCL.CCLFormulaBoxSign.FormOverride current))
    (formula : Formula)
    (description : ∀ atom, atom ∈ formula.atoms →
      Description reference atom.form)
    (refines : current.Refines bounding)
    (sample : Gaussian) (sampleInside : current.Contains sample) :
    OwnerInspection p reference bounding current denominatorMargin
      marginPositive refines sample sampleInside formOverrides formula := by
  match formula with
  | .truth => exact .stable .truth
  | .falsity => exact .stable .falsity
  | .atom value =>
      have member : value ∈ (Formula.atom value).atoms := by
        simp [Formula.atoms]
      match found : CCL.CCLFormulaBoxSign.findFormOverride
          formOverrides value.form with
      | some formStability =>
          exact .stable (.atom value formStability.toAtom)
      | none =>
          match CCL.CCLFormulaBoxSign.findOverride overrides
              value with
          | some stability => exact .stable (.atom value stability)
          | none =>
              match failure : CCL.CCLBoxSign.certificate?
                  value.form bounding current refines sample sampleInside with
              | some certificate =>
                  exact .stable (.atom value (.strict certificate))
              | none =>
                  match description value member with
                  | .curve source =>
                      exact .boundary value member found failure
                        (.curve value source
                        (CCL.CCLBoundaryCharts.analyzeCharts p
                          source current denominatorMargin marginPositive) rfl)
                  | .finite points complete nonnegative =>
                      exact .boundary value member found failure
                        (.finite value points complete nonnegative
                          (CCL.CCLBoundaryAnalysis.evaluatePoints p
                            points) rfl)
                  | .universal zero =>
                      exact .stable (.atom value (.zero fun point _inside =>
                        zero point))
  | .and left right =>
      let leftDescription : ∀ atom, atom ∈ left.atoms →
          Description reference atom.form := fun atom member =>
        description atom (by
          simp only [Formula.atoms, List.mem_append]
          exact Or.inl member)
      match inspectOwnerWith p reference bounding current denominatorMargin
          marginPositive overrides formOverrides left leftDescription refines
          sample sampleInside with
      | .boundary atom member notResolved failure remaining =>
          exact .boundary atom (by
            simp only [Formula.atoms, List.mem_append]
            exact Or.inl member) notResolved failure remaining
      | .stable leftStable =>
          let rightDescription : ∀ atom, atom ∈ right.atoms →
              Description reference atom.form := fun atom member =>
            description atom (by
              simp only [Formula.atoms, List.mem_append]
              exact Or.inr member)
          match inspectOwnerWith p reference bounding current
              denominatorMargin marginPositive overrides formOverrides right
              rightDescription refines sample
              sampleInside with
          | .boundary atom member notResolved failure remaining =>
              exact .boundary atom (by
                simp only [Formula.atoms, List.mem_append]
                exact Or.inr member) notResolved failure remaining
          | .stable rightStable =>
              exact .stable (.and leftStable rightStable)
  | .or left right =>
      let leftDescription : ∀ atom, atom ∈ left.atoms →
          Description reference atom.form := fun atom member =>
        description atom (by
          simp only [Formula.atoms, List.mem_append]
          exact Or.inl member)
      match inspectOwnerWith p reference bounding current denominatorMargin
          marginPositive overrides formOverrides left leftDescription refines
          sample sampleInside with
      | .boundary atom member notResolved failure remaining =>
          exact .boundary atom (by
            simp only [Formula.atoms, List.mem_append]
            exact Or.inl member) notResolved failure remaining
      | .stable leftStable =>
          let rightDescription : ∀ atom, atom ∈ right.atoms →
              Description reference atom.form := fun atom member =>
            description atom (by
              simp only [Formula.atoms, List.mem_append]
              exact Or.inr member)
          match inspectOwnerWith p reference bounding current
              denominatorMargin marginPositive overrides formOverrides right
              rightDescription refines sample
              sampleInside with
          | .boundary atom member notResolved failure remaining =>
              exact .boundary atom (by
                simp only [Formula.atoms, List.mem_append]
                exact Or.inr member) notResolved failure remaining
          | .stable rightStable =>
              exact .stable (.or leftStable rightStable)

/-- Initial owner inspection with no previously resolved boundaries. -/
def inspectOwner
    (p : GaussianPolynomial) (reference : Mat2)
    (bounding current : Box) (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin)
    (formula : Formula)
    (description : ∀ atom, atom ∈ formula.atoms →
      Description reference atom.form)
    (refines : current.Refines bounding)
    (sample : Gaussian) (sampleInside : current.Contains sample) :
    OwnerInspection p reference bounding current denominatorMargin
      marginPositive refines sample sampleInside [] formula :=
  inspectOwnerWith p reference bounding current denominatorMargin
    marginPositive [] [] formula description refines sample sampleInside

/-- Public entry point using the atom descriptions generated alongside a
parser formula. -/
def inspectDescriptions
    (p : GaussianPolynomial) (reference : Mat2)
    (bounding current : Box) (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin)
    (formula : Formula)
    (descriptions : CCL.CCLFormulaBoundaries.Descriptions
      reference formula)
    (refines : current.Refines bounding)
    (sample : Gaussian) (sampleInside : current.Contains sample) :
    OwnerInspection p reference bounding current denominatorMargin
      marginPositive refines sample sampleInside [] formula :=
  inspectOwner p reference bounding current denominatorMargin marginPositive
    formula (fun atom member => descriptions.boundaryFor atom member)
    refines sample sampleInside

/-! ## Persistent next-bit inspection -/

abbrev State := CCL.PersistentCCL.State
abbrev LocalTerminal
    {p : GaussianPolynomial} {ambient : Box} (current : State p ambient) :=
  CCL.PersistentCCLStrict.LocalTerminal current
abbrev StableNext
    {p : GaussianPolynomial} {ambient : Box} (current : State p ambient) :=
  CCL.PersistentCCLStrict.StableNext current
abbrev BoundaryNext
    {p : GaussianPolynomial} {ambient : Box} (current : State p ambient) :=
  CCL.PersistentCCLStrict.BoundaryNext current

/-- The strict next-bit inspection with universal equality boundaries already
discharged. -/
inductive NextInspection
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin)
    (formOverrides : List
      (CCL.CCLFormulaBoxSign.FormOverride
        current.numerical.box)) where
  | terminal (result : LocalTerminal current)
  | stable (result : StableNext current)
  | boundary (next : BoundaryNext current)
      (notResolved : CCL.CCLFormulaBoxSign.findFormOverride
        formOverrides next.atom.form = none)
      (remaining : RemainingBoundary p
        (CCL.CCLPullback.adjugate
          (CCL.RawParser.parse current.word).matrix)
        current.numerical.box denominatorMargin marginPositive next.atom)

/-- Decide the local bit, inspect its complete incremental formula with exact
boundary provenance, and immediately apply universal equality ownership. -/
def inspectNextWith
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin)
    (formOverrides : List
      (CCL.CCLFormulaBoxSign.FormOverride
        current.numerical.box)) :
    NextInspection current denominatorMargin marginPositive formOverrides := by
  let sample := current.currentSample
  let next := sample.nextDecision
  match next.decision with
  | .terminal terminalNone =>
      exact .terminal
        { none := by
            intro bit possible
            apply terminalNone bit
            apply (CCL.CCLNextBit.advanceFormula_iff
              (CCL.RawParser.parse current.word) bit
              next.tail).2
            exact (CCL.ParserStep.canStep_iff_canAdvanceAt
              (CCL.RawParser.parse current.word) sample.point
              next.tail
              (CCL.RawParser.parse_det_ne current.word)
              next.represents bit).1 possible }
  | .next bit tailHolds _unique =>
      let parser := CCL.RawParser.parse current.word
      let reference := CCL.CCLPullback.adjugate parser.matrix
      let formula :=
        CCL.CCLNextBit.inputIncrementalAdvanceFormula parser bit
      have currentHolds : formula.Holds sample.point := by
        exact CCL.PersistentCCLStrict.CompatibleSample.inputIncrementalAdvanceFormula_holds_of_advance
          sample bit tailHolds
      let descriptions :=
        CCL.CCLFormulaBoundaries.inputIncremental parser
          (CCL.RawParser.parse_det_ne current.word) bit
      match inspectOwnerWith p reference ambient current.numerical.box
          denominatorMargin marginPositive [] formOverrides formula
          (fun atom member => descriptions.boundaryFor atom member)
          current.numerical.refinesAmbient sample.point sample.inside with
      | .stable stable =>
          exact .stable
            { bit := bit
              stable := stable
              currentHolds := currentHolds }
      | .boundary atom member notResolved failure remaining =>
          exact .boundary
            { bit := bit
              atom := atom
              member := by simpa only [formula] using member
              failure := by simpa only [sample, formula] using failure
              currentHolds := by simpa only [sample, formula] using currentHolds }
            notResolved
            (by simpa only [reference, parser] using remaining)

/-- Initial persistent owner inspection with no previously resolved finite
form signs. -/
def inspectNext
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) (denominatorMargin : Coordinate)
    (marginPositive : 0 < denominatorMargin) :
    NextInspection current denominatorMargin marginPositive [] :=
  inspectNextWith current denominatorMargin marginPositive []

/-! ## Finite-boundary ownership -/

abbrev WindingOneTrack (p : GaussianPolynomial) (ambient : Box) :=
  RFAP.ShrinkingTrack.WindingOneTrack p ambient
abbrev ExactRootIn (p : GaussianPolynomial) (box : Box) :=
  CCL.PersistentCCL.ExactRootIn p box

/-- Resolving a finite nonnegative zero set either finds an exact polynomial
root or produces a same-prefix refinement on which that form is strictly
positive. -/
inductive FiniteResolution
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) (atom : Atom) where
  | exact (root : ExactRootIn p current.numerical.box)
  | positive (state : State p ambient)
      (boxRefines : state.numerical.box.Refines current.numerical.box)
      (word_eq : state.word = current.word)
      (stability : CCL.CCLFormulaBoxSign.FormOverride
        state.numerical.box)
      (form_eq : stability.form = atom.form)

/-- Exclude all displayed zeros using the winding track, then turn
nonnegativity plus nonvanishing into a reusable strict-positive form
override. -/
def resolveFinite
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (atom : Atom) (points : List Gaussian)
    (complete : ∀ value, atom.form.eval value = 0 → value ∈ points)
    (nonnegative : ∀ value, 0 ≤ atom.form.eval value) :
    FiniteResolution current atom := by
  match CCL.PersistentCCLTerminal.resolvePoints degreePositive
      track current points with
  | .exact root => exact .exact root
  | .excluded state boxRefines word_eq outside =>
      let stability : CCL.CCLFormulaBoxSign.FormOverride
          state.numerical.box :=
        CCL.CCLFormulaBoxSign.FormOverride.positive atom.form
          (by
            intro value inside
            have nonzero : atom.form.eval value ≠ 0 := by
              intro evaluatesZero
              exact outside value (complete value evaluatesZero) inside
            rcases lt_trichotomy (atom.form.eval value) 0 with
                negative | equal | positive
            · exact (not_lt_of_ge (nonnegative value) negative).elim
            · exact (nonzero equal).elim
            · exact positive)
      exact .positive state boxRefines word_eq stability rfl

end CCL.CCLEqualityOwner
