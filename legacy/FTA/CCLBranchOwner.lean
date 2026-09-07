import FTA.CCLBranchPlan
import FTA.CCLFormulaPath
import FTA.CCLIntersectionSampler

/-!
# Cell-local owners for CCL branch curves

A complete generalized circle or line can pass through several CCL sectors,
so it need not have one globally valid equality owner.  Ownership is instead
decided after the curve has been split into parameter cells on which every
other child-formula atom has stable sign.  The distinguished boundary atom is
handled by its exact zero theorem; other atoms use the cleared rational
polynomials from `FTA.CCLFormulaPath`.
-/

namespace FTA
namespace CCLBranchOwner

open CCL CCL.GaussianRat
open FTA.CCLGeometry
open FTA.CCLParserGeometry
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLIntersectionSampler
open FTA.ProjectivePath
open FTA.PathPolynomial
open FTA.RationalPolynomialBounds
open FTA.SturmTransducer

abbrev QI := CCL.GaussianRat
abbrev RatPolynomial := FTA.ComputablePolynomial.DensePolynomial ℚ
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

/-- One atom is stable either because it is the distinguished curve equation
or because its cleared polynomial is zero/strict throughout the cell.  The
Boolean tag keeps this certificate computationally lightweight. -/
structure AtomStatus
    (boundary : HermitianForm) (atom : Atom)
    (path : Path) (interval : RationalInterval) where
  isBoundary : Bool
  boundaryProof : isBoundary = true → atom.form = boundary
  polynomialProof : isBoundary = false →
    PolynomialStatus (clearedForm atom.form path) interval

def AtomStatus.boundary
    {boundary : HermitianForm} {atom : Atom}
    {path : Path} {interval : RationalInterval}
    (equal : atom.form = boundary) :
    AtomStatus boundary atom path interval where
  isBoundary := true
  boundaryProof := fun _ => equal
  polynomialProof := by
    intro impossible
    exact Bool.noConfusion impossible

def AtomStatus.polynomial
    {boundary : HermitianForm} {atom : Atom}
    {path : Path} {interval : RationalInterval}
    (status : PolynomialStatus (clearedForm atom.form path) interval) :
    AtomStatus boundary atom path interval where
  isBoundary := false
  boundaryProof := by simp
  polynomialProof := fun _ => status

/-- Cell certificate for every atom in a formula, allowing occurrences of the
distinguished boundary form to be discharged by exact equality. -/
structure StableFormula
    (boundary : HermitianForm) (formula : Formula)
    (path : Path) (interval : RationalInterval) : Type where
  status : ∀ atom ∈ formulaAtoms formula,
    Nonempty (AtomStatus boundary atom path interval)

/-- Cleared polynomials for exactly the atoms not definitionally equal to the
distinguished boundary. -/
def otherPolynomials
    (boundary : HermitianForm) (formula : Formula) (path : Path) :
    List RatPolynomial :=
  ((formulaAtoms formula).filter fun atom => decide (atom.form ≠ boundary)).map
    fun atom => clearedForm atom.form path

/-- Zero-or-strict certificates aligned with a finite polynomial list. -/
structure PolynomialStatuses
    (polynomials : List RatPolynomial) (interval : RationalInterval) : Type where
  status : ∀ polynomial ∈ polynomials,
    Nonempty (PolynomialStatus polynomial interval)

/-- Direct finite attempt to classify a complete polynomial list on one
cell. -/
def polynomialStatuses?
    (interval : RationalInterval) (proper : interval.Proper) :
    (polynomials : List RatPolynomial) →
      Option (PolynomialStatuses polynomials interval)
  | [] => some
      { status := by
          intro polynomial member
          simp at member }
  | polynomial :: polynomials =>
      match polynomialStatus? polynomial interval proper,
          polynomialStatuses? interval proper polynomials with
      | some head, some tail =>
          some
            { status := by
                intro candidate member
                rcases List.mem_cons.mp member with rfl | tailMember
                · exact ⟨head⟩
                · exact tail.status candidate tailMember }
      | _, _ => none

/-- Turn aligned non-boundary polynomial certificates into the complete
boundary-aware formula certificate. -/
def StableFormula.ofPolynomialStatuses
    (boundary : HermitianForm) (formula : Formula)
    (path : Path) (interval : RationalInterval)
    (statuses : PolynomialStatuses
      (otherPolynomials boundary formula path) interval) :
    StableFormula boundary formula path interval where
  status := by
    intro atom member
    if equal : atom.form = boundary then
      exact ⟨AtomStatus.boundary equal⟩
    else
      have polynomialMember : clearedForm atom.form path ∈
          otherPolynomials boundary formula path := by
        apply List.mem_map.mpr
        exact ⟨atom, List.mem_filter.mpr ⟨member, by simp [equal]⟩, rfl⟩
      rcases statuses.status (clearedForm atom.form path) polynomialMember with
        ⟨polynomialStatus⟩
      exact ⟨AtomStatus.polynomial polynomialStatus⟩

/-- Executable boundary-aware formula classifier on a proposed parameter
cell. -/
def stableFormula?
    (boundary : HermitianForm) (formula : Formula)
    (path : Path) (interval : RationalInterval) (proper : interval.Proper) :
    Option (StableFormula boundary formula path interval) :=
  match polynomialStatuses? interval proper
      (otherPolynomials boundary formula path) with
  | none => none
  | some statuses => some
      (StableFormula.ofPolynomialStatuses boundary formula path interval statuses)

theorem AtomStatus.holds_iff
    {boundary : HermitianForm} {atom : Atom}
    {path : Path} {interval : RationalInterval}
    (status : AtomStatus boundary atom path interval)
    (onBoundary : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
      boundary.eval (path.value t) = 0)
    {s t : ℚ}
    (sLower : interval.lower ≤ s) (sUpper : s ≤ interval.upper)
    (tLower : interval.lower ≤ t) (tUpper : t ≤ interval.upper)
    (sDenominator : path.denominator.eval (PathPolynomial.ofRat s) ≠ 0)
    (tDenominator : path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    atom.Holds (path.value s) ↔ atom.Holds (path.value t) := by
  cases boundaryCheck : status.isBoundary with
  | false =>
      let polynomialStatus := status.polynomialProof boundaryCheck
      rw [← atomPathHolds_iff atom path s sDenominator,
        ← atomPathHolds_iff atom path t tDenominator]
      exact polynomialStatus.holds_iff atom.sign
        sLower sUpper tLower tUpper
  | true =>
      have equal := status.boundaryProof boundaryCheck
      simp only [Atom.Holds]
      rw [equal, onBoundary sLower sUpper, onBoundary tLower tUpper]

/-- A boundary-stable formula has constant truth throughout the parameter
cell. -/
theorem StableFormula.holds_iff
    {boundary : HermitianForm} {formula : Formula}
    {path : Path} {interval : RationalInterval}
    (stable : StableFormula boundary formula path interval)
    (onBoundary : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
      boundary.eval (path.value t) = 0)
    {s t : ℚ}
    (sLower : interval.lower ≤ s) (sUpper : s ≤ interval.upper)
    (tLower : interval.lower ≤ t) (tUpper : t ≤ interval.upper)
    (sDenominator : path.denominator.eval (PathPolynomial.ofRat s) ≠ 0)
    (tDenominator : path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    formula.Holds (path.value s) ↔ formula.Holds (path.value t) := by
  induction formula with
  | truth => rfl
  | falsity => rfl
  | atom atom =>
      rcases stable.status atom (by simp [formulaAtoms]) with ⟨status⟩
      exact status.holds_iff
        onBoundary sLower sUpper tLower tUpper
        sDenominator tDenominator
  | and left right leftInduction rightInduction =>
      let leftStable : StableFormula boundary left path interval :=
        { status := by
            intro atom member
            exact stable.status atom
              (List.mem_append_left (formulaAtoms right) member) }
      let rightStable : StableFormula boundary right path interval :=
        { status := by
            intro atom member
            exact stable.status atom
              (List.mem_append_right (formulaAtoms left) member) }
      exact and_congr
        (leftInduction leftStable)
        (rightInduction rightStable)
  | or left right leftInduction rightInduction =>
      let leftStable : StableFormula boundary left path interval :=
        { status := by
            intro atom member
            exact stable.status atom
              (List.mem_append_left (formulaAtoms right) member) }
      let rightStable : StableFormula boundary right path interval :=
        { status := by
            intro atom member
            exact stable.status atom
              (List.mem_append_right (formulaAtoms left) member) }
      exact or_congr
        (leftInduction leftStable)
        (rightInduction rightStable)

/-- Complete stable truth table for two child formulas on one boundary cell. -/
inductive PairDecision
    (left right : Formula) (path : Path) (interval : RationalInterval) where
  | neither
      (leftFails : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        ¬left.Holds (path.value t))
      (rightFails : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        ¬right.Holds (path.value t))
  | left
      (leftHolds : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        left.Holds (path.value t))
      (rightFails : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        ¬right.Holds (path.value t))
  | right
      (leftFails : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        ¬left.Holds (path.value t))
      (rightHolds : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        right.Holds (path.value t))
  | both
      (leftHolds : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        left.Holds (path.value t))
      (rightHolds : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        right.Holds (path.value t))

private theorem stable_holds_everywhere
    {boundary : HermitianForm} {formula : Formula}
    {path : Path} {interval : RationalInterval}
    (stable : StableFormula boundary formula path interval)
    (onBoundary : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
      boundary.eval (path.value t) = 0)
    (denominator : DenominatorCertificate path interval)
    {sample : ℚ} (sampleLower : interval.lower ≤ sample)
    (sampleUpper : sample ≤ interval.upper)
    (sampleHolds : formula.Holds (path.value sample)) :
    ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
      formula.Holds (path.value t) := by
  intro t lower upper
  apply (stable.holds_iff onBoundary sampleLower sampleUpper lower upper
    (denominator.denominator_ne sampleLower sampleUpper)
    (denominator.denominator_ne lower upper)).1
  exact sampleHolds

private theorem stable_fails_everywhere
    {boundary : HermitianForm} {formula : Formula}
    {path : Path} {interval : RationalInterval}
    (stable : StableFormula boundary formula path interval)
    (onBoundary : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
      boundary.eval (path.value t) = 0)
    (denominator : DenominatorCertificate path interval)
    {sample : ℚ} (sampleLower : interval.lower ≤ sample)
    (sampleUpper : sample ≤ interval.upper)
    (sampleFails : ¬formula.Holds (path.value sample)) :
    ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
      ¬formula.Holds (path.value t) := by
  intro t lower upper holds
  apply sampleFails
  apply (stable.holds_iff onBoundary sampleLower sampleUpper lower upper
    (denominator.denominator_ne sampleLower sampleUpper)
    (denominator.denominator_ne lower upper)).2
  exact holds

/-- Evaluate both children once and lift the result to the whole stable
boundary cell.  `neither` marks an irrelevant/terminal arc; `both` is retained
until parser uniqueness is supplied by the track controller. -/
def decidePair
    (boundary : HermitianForm) (left right : Formula)
    (path : Path) (interval : RationalInterval)
    (leftStable : StableFormula boundary left path interval)
    (rightStable : StableFormula boundary right path interval)
    (onBoundary : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
      boundary.eval (path.value t) = 0)
    (denominator : DenominatorCertificate path interval)
    (sample : ℚ) (sampleLower : interval.lower ≤ sample)
    (sampleUpper : sample ≤ interval.upper) :
    PairDecision left right path interval := by
  if leftCheck : left.evalBool (path.value sample) = true then
    have leftHolds := (Formula.evalBool_eq_true left _).1 leftCheck
    if rightCheck : right.evalBool (path.value sample) = true then
      have rightHolds := (Formula.evalBool_eq_true right _).1 rightCheck
      exact .both
          (stable_holds_everywhere leftStable onBoundary denominator
            sampleLower sampleUpper leftHolds)
          (stable_holds_everywhere rightStable onBoundary denominator
            sampleLower sampleUpper rightHolds)
    else
      have rightFails : ¬right.Holds (path.value sample) := by
        intro holds
        exact rightCheck ((Formula.evalBool_eq_true right _).2 holds)
      exact .left
          (stable_holds_everywhere leftStable onBoundary denominator
            sampleLower sampleUpper leftHolds)
          (stable_fails_everywhere rightStable onBoundary denominator
            sampleLower sampleUpper rightFails)
  else
    have leftFails : ¬left.Holds (path.value sample) := by
      intro holds
      exact leftCheck ((Formula.evalBool_eq_true left _).2 holds)
    if rightCheck : right.evalBool (path.value sample) = true then
      have rightHolds := (Formula.evalBool_eq_true right _).1 rightCheck
      exact .right
          (stable_fails_everywhere leftStable onBoundary denominator
            sampleLower sampleUpper leftFails)
          (stable_holds_everywhere rightStable onBoundary denominator
            sampleLower sampleUpper rightHolds)
    else
      have rightFails : ¬right.Holds (path.value sample) := by
        intro holds
        exact rightCheck ((Formula.evalBool_eq_true right _).2 holds)
      exact .neither
          (stable_fails_everywhere leftStable onBoundary denominator
            sampleLower sampleUpper leftFails)
          (stable_fails_everywhere rightStable onBoundary denominator
            sampleLower sampleUpper rightFails)

/-! ## Specialization to the two pulled-back parser children -/

/-- Cell-local branch result in raw-bit form. -/
inductive InputCellDecision
    (state : RawParser.State) (source : CCLBranchPlan.BoundarySource)
    (interval : RationalInterval) where
  | irrelevant
      (none : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        ∀ bit, ¬(inputAdvanceFormula state bit).Holds (source.path.value t))
  | owner (bit : Bool)
      (holds : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        (inputAdvanceFormula state bit).Holds (source.path.value t))
      (otherFails : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        ¬(inputAdvanceFormula state (!bit)).Holds (source.path.value t))
  | ambiguous
      (falseHolds : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        (inputAdvanceFormula state false).Holds (source.path.value t))
      (trueHolds : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
        (inputAdvanceFormula state true).Holds (source.path.value t))

/-- One exact sample chooses the equality owner on a sign-stable planned
source cell. -/
def decideInputCell
    (state : RawParser.State) (source : CCLBranchPlan.BoundarySource)
    (interval : RationalInterval)
    (falseStable : StableFormula source.form
      (inputAdvanceFormula state false) source.path interval)
    (trueStable : StableFormula source.form
      (inputAdvanceFormula state true) source.path interval)
    (onBoundary : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
      source.form.eval (source.path.value t) = 0)
    (denominator : DenominatorCertificate source.path interval)
    (sample : ℚ) (sampleLower : interval.lower ≤ sample)
    (sampleUpper : sample ≤ interval.upper) :
    InputCellDecision state source interval :=
  match decidePair source.form
      (inputAdvanceFormula state false) (inputAdvanceFormula state true)
      source.path interval falseStable trueStable onBoundary denominator
      sample sampleLower sampleUpper with
  | .neither falseFails trueFails =>
      .irrelevant (by
        intro t lower upper bit
        cases bit
        · exact falseFails lower upper
        · exact trueFails lower upper)
  | .left falseHolds trueFails =>
      .owner false falseHolds (by
        intro t lower upper
        simpa using trueFails lower upper)
  | .right falseFails trueHolds =>
      .owner true trueHolds (by
        intro t lower upper
        simpa using falseFails lower upper)
  | .both falseHolds trueHolds =>
      .ambiguous falseHolds trueHolds

/-- Fully executable finite attempt at a cell-local parser owner.  `none`
requests another parameter subdivision; `some` carries the whole-cell proof. -/
def decideInputCell?
    (state : RawParser.State) (source : CCLBranchPlan.BoundarySource)
    (interval : RationalInterval) (proper : interval.Proper)
    (onBoundary : ∀ {t : ℚ}, interval.lower ≤ t → t ≤ interval.upper →
      source.form.eval (source.path.value t) = 0)
    (denominator : DenominatorCertificate source.path interval)
    (sample : ℚ) (sampleLower : interval.lower ≤ sample)
    (sampleUpper : sample ≤ interval.upper) :
    Option (InputCellDecision state source interval) :=
  match stableFormula? source.form (inputAdvanceFormula state false)
      source.path interval proper,
    stableFormula? source.form (inputAdvanceFormula state true)
      source.path interval proper with
  | some falseStable, some trueStable =>
      some (decideInputCell state source interval falseStable trueStable
        onBoundary denominator sample sampleLower sampleUpper)
  | _, _ => none

end CCLBranchOwner
end FTA
