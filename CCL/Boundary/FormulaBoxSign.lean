import CCL.Boundary.BoxSign
import CCL.Boundary.Formula

/-!
# Box stability of finite CCL formulas

If every Hermitian atom in a finite branch formula has a strict box-sign
certificate, evaluating the formula at any one point decides it everywhere
in that box.  The certificate search is structural recursion over the finite
formula; it neither enumerates points nor forms a root set.
-/

namespace CCL.CCLFormulaBoxSign

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev SignTest := CCL.CCLFormula.SignTest
abbrev Atom := CCL.CCLFormula.Atom
abbrev Formula := CCL.CCLFormula.Formula

open CCL.CCLFormula

private theorem holds_iff_of_negative
    (test : SignTest) {left right : RFAP.ConstructiveFraction.Rational}
    (leftNegative : left < 0) (rightNegative : right < 0) :
    test.Holds left ↔ test.Holds right := by
  cases test with
  | negative => exact iff_of_true leftNegative rightNegative
  | nonpositive => exact iff_of_true leftNegative.le rightNegative.le
  | zero => exact iff_of_false (ne_of_lt leftNegative) (ne_of_lt rightNegative)
  | nonzero => exact iff_of_true (ne_of_lt leftNegative) (ne_of_lt rightNegative)
  | nonnegative =>
      exact iff_of_false (not_le_of_gt leftNegative) (not_le_of_gt rightNegative)
  | positive =>
      exact iff_of_false (not_lt_of_ge leftNegative.le)
        (not_lt_of_ge rightNegative.le)

private theorem holds_iff_of_positive
    (test : SignTest) {left right : RFAP.ConstructiveFraction.Rational}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    test.Holds left ↔ test.Holds right := by
  cases test with
  | negative =>
      exact iff_of_false (not_lt_of_ge leftPositive.le)
        (not_lt_of_ge rightPositive.le)
  | nonpositive =>
      exact iff_of_false (not_le_of_gt leftPositive)
        (not_le_of_gt rightPositive)
  | zero =>
      exact iff_of_false (Ne.symm (ne_of_lt leftPositive))
        (Ne.symm (ne_of_lt rightPositive))
  | nonzero =>
      exact iff_of_true (Ne.symm (ne_of_lt leftPositive))
        (Ne.symm (ne_of_lt rightPositive))
  | nonnegative => exact iff_of_true leftPositive.le rightPositive.le
  | positive => exact iff_of_true leftPositive rightPositive

/-- An atom is stable either because its form has one strict sign throughout
the box or because the form is identically zero there.  The latter is the
finite equality-owner case: the atom's weak/strict convention decides its
truth value once and for all at zero. -/
inductive AtomStability (atom : Atom) (bounding current : Box) where
  | strict (certificate : CCL.CCLBoxSign.Certificate
      atom.form bounding current)
  | negative (holds : ∀ value, current.Contains value →
      atom.form.eval value < 0)
  | positive (holds : ∀ value, current.Contains value →
      0 < atom.form.eval value)
  | zero (evaluatesZero : ∀ value, current.Contains value →
      atom.form.eval value = 0)

/-- Form-sign stability is independent of the atom's weak/strict sign tag
and can therefore be reused by either child formula. -/
inductive FormStability (form : CCL.CCLGeometry.HermitianForm)
    (current : Box) where
  | negative (holds : ∀ value, current.Contains value → form.eval value < 0)
  | positive (holds : ∀ value, current.Contains value → 0 < form.eval value)
  | zero (holds : ∀ value, current.Contains value → form.eval value = 0)

def FormStability.toAtom
    {atom : Atom} {bounding current : Box}
    (stability : FormStability atom.form current) :
    AtomStability atom bounding current :=
  match stability with
  | .negative holds => .negative holds
  | .positive holds => .positive holds
  | .zero holds => .zero holds

/-- Strict sign of the underlying form makes every weak, strict, equality,
and disequality atom test constant throughout the box. -/
theorem atom_holds_iff
    {atom : Atom} {bounding current : Box}
    (stability : AtomStability atom bounding current)
    {left right : Gaussian} (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    atom.Holds left ↔ atom.Holds right := by
  cases stability with
  | strict certificate =>
      cases certificate.strictSign with
      | negative negative =>
          exact holds_iff_of_negative atom.sign
            (negative left leftInside) (negative right rightInside)
      | positive positive =>
          exact holds_iff_of_positive atom.sign
            (positive left leftInside) (positive right rightInside)
  | negative negative =>
      exact holds_iff_of_negative atom.sign
        (negative left leftInside) (negative right rightInside)
  | positive positive =>
      exact holds_iff_of_positive atom.sign
        (positive left leftInside) (positive right rightInside)
  | zero evaluatesZero =>
      unfold Atom.Holds
      rw [evaluatesZero left leftInside, evaluatesZero right rightInside]

/-- Structural evidence that every atom of a finite formula has a strict
box-sign certificate. -/
inductive Stable (bounding current : Box) : Formula → Type where
  | truth : Stable bounding current .truth
  | falsity : Stable bounding current .falsity
  | atom (value : Atom)
      (stability : AtomStability value bounding current) :
      Stable bounding current (.atom value)
  | and {left right : Formula}
      (leftStable : Stable bounding current left)
      (rightStable : Stable bounding current right) :
      Stable bounding current (.and left right)
  | or {left right : Formula}
      (leftStable : Stable bounding current left)
      (rightStable : Stable bounding current right) :
      Stable bounding current (.or left right)

namespace Stable

/-- A stable formula has the same truth value at every two points in the
certified box. -/
theorem holds_iff
    {bounding current : Box} {formula : Formula}
    (stable : Stable bounding current formula)
    {left right : Gaussian} (leftInside : current.Contains left)
    (rightInside : current.Contains right) :
    formula.Holds left ↔ formula.Holds right := by
  induction stable with
  | truth => exact iff_of_true True.intro True.intro
  | falsity => exact iff_of_false id id
  | atom value stability =>
      exact atom_holds_iff stability leftInside rightInside
  | and leftStable rightStable leftHypothesis rightHypothesis =>
      exact and_congr leftHypothesis rightHypothesis
  | or leftStable rightStable leftHypothesis rightHypothesis =>
      exact or_congr leftHypothesis rightHypothesis

end Stable

/-- One already-resolved atom that may be reused while structurally
reinspecting the same finite formula. -/
structure Override (bounding current : Box) where
  atom : Atom
  stability : AtomStability atom bounding current

namespace Override

/-- Equality ownership for a form proved identically zero on the current
box. -/
def zero
    {bounding current : Box} (atom : Atom)
    (evaluatesZero : ∀ value, current.Contains value →
      atom.form.eval value = 0) : Override bounding current :=
  ⟨atom, .zero evaluatesZero⟩

end Override

/-- One resolved form sign, reusable for every occurrence and every sign tag
of that form. -/
structure FormOverride (current : Box) where
  form : CCL.CCLGeometry.HermitianForm
  stability : FormStability form current

namespace FormOverride

def positive
    {current : Box} (form : CCL.CCLGeometry.HermitianForm)
    (holds : ∀ value, current.Contains value → 0 < form.eval value) :
    FormOverride current :=
  ⟨form, .positive holds⟩

def zero
    {current : Box} (form : CCL.CCLGeometry.HermitianForm)
    (holds : ∀ value, current.Contains value → form.eval value = 0) :
    FormOverride current :=
  ⟨form, .zero holds⟩

/-- A resolved form sign remains resolved on every displayed subbox. -/
def refine
    {outer inner : Box} (override : FormOverride outer)
    (refines : inner.Refines outer) : FormOverride inner :=
  match override.stability with
  | .negative holds =>
      ⟨override.form, .negative fun value inside =>
        holds value (refines.contains inside)⟩
  | .positive holds =>
      ⟨override.form, .positive fun value inside =>
        holds value (refines.contains inside)⟩
  | .zero holds =>
      ⟨override.form, .zero fun value inside =>
        holds value (refines.contains inside)⟩

@[simp] theorem refine_form
    {outer inner : Box} (override : FormOverride outer)
    (refines : inner.Refines outer) :
    (override.refine refines).form = override.form := by
  rcases override with ⟨form, stability⟩
  cases stability <;> rfl

end FormOverride

def findFormOverride
    {current : Box} (overrides : List (FormOverride current))
    (target : CCL.CCLGeometry.HermitianForm) :
    Option (FormStability target current) :=
  match overrides with
  | [] => none
  | entry :: remaining =>
      if equal : entry.form = target then
        some (equal ▸ entry.stability)
      else
        findFormOverride remaining target

/-- Look up an exact atom match in a finite list of resolved boundaries. -/
def findOverride
    {bounding current : Box} (overrides : List (Override bounding current))
    (target : Atom) : Option (AtomStability target bounding current) :=
  match overrides with
  | [] => none
  | entry :: remaining =>
      if equal : entry.atom = target then
        some (equal ▸ entry.stability)
      else
        findOverride remaining target

/-- Reuse a resolved equality boundary when present; otherwise execute the
ordinary strict-margin comparison. -/
def atomStability?
    {bounding current : Box} (overrides : List (Override bounding current))
    (refines : current.Refines bounding) (sample : Gaussian)
    (sampleInside : current.Contains sample) (atom : Atom) :
    Option (AtomStability atom bounding current) :=
  match findOverride overrides atom with
  | some stability => some stability
  | none =>
      match CCL.CCLBoxSign.certificate?
          atom.form bounding current refines sample sampleInside with
      | none => none
      | some certificate => some (.strict certificate)

/-- Execute all of the finitely many atom-margin comparisons in a formula. -/
def stable?
    (formula : Formula) (bounding current : Box)
    (refines : current.Refines bounding) (sample : Gaussian)
    (sampleInside : current.Contains sample) :
    Option (Stable bounding current formula) :=
  match formula with
  | .truth => some .truth
  | .falsity => some .falsity
  | .atom value =>
      match CCL.CCLBoxSign.certificate?
          value.form bounding current refines sample sampleInside with
      | none => none
      | some certificate => some (.atom value (.strict certificate))
  | .and left right =>
      match stable? left bounding current refines sample sampleInside with
      | none => none
      | some leftStable =>
          match stable? right bounding current refines sample sampleInside with
          | none => none
          | some rightStable => some (.and leftStable rightStable)
  | .or left right =>
      match stable? left bounding current refines sample sampleInside with
      | none => none
      | some leftStable =>
          match stable? right bounding current refines sample sampleInside with
          | none => none
          | some rightStable => some (.or leftStable rightStable)

/-- Execute formula stability while reusing a finite list of exact boundary
decisions already made by the equality-owner layer. -/
def stableWith?
    (bounding current : Box)
    (overrides : List (Override bounding current))
    (formula : Formula)
    (refines : current.Refines bounding) (sample : Gaussian)
    (sampleInside : current.Contains sample) :
    Option (Stable bounding current formula) :=
  match formula with
  | .truth => some .truth
  | .falsity => some .falsity
  | .atom value =>
      match atomStability? overrides refines sample sampleInside value with
      | none => none
      | some stability => some (.atom value stability)
  | .and left right =>
      match stableWith? bounding current overrides left refines sample
          sampleInside with
      | none => none
      | some leftStable =>
          match stableWith? bounding current overrides right refines sample
              sampleInside with
          | none => none
          | some rightStable => some (.and leftStable rightStable)
  | .or left right =>
      match stableWith? bounding current overrides left refines sample
          sampleInside with
      | none => none
      | some leftStable =>
          match stableWith? bounding current overrides right refines sample
              sampleInside with
          | none => none
          | some rightStable => some (.or leftStable rightStable)

/-- Proof-bearing result of the same structural inspection as `stable?`.
Failure retains the first concrete atom whose strict margin comparison did
not succeed, rather than erasing its boundary provenance into `none`. -/
inductive Inspection
    (bounding current : Box) (refines : current.Refines bounding)
    (sample : Gaussian) (sampleInside : current.Contains sample) :
    (formula : Formula) → Type where
  | stable {formula : Formula} (result : Stable bounding current formula) :
      Inspection bounding current refines sample sampleInside formula
  | unresolved {formula : Formula} (atom : Atom)
      (member : atom ∈ formula.atoms)
      (failure : CCL.CCLBoxSign.certificate?
        atom.form bounding current refines sample sampleInside = none) :
      Inspection bounding current refines sample sampleInside formula

/-- Inspect a finite formula and retain the first unresolved atom when it is
not box-stable. -/
def inspect
    (formula : Formula) (bounding current : Box)
    (refines : current.Refines bounding) (sample : Gaussian)
    (sampleInside : current.Contains sample) :
    Inspection bounding current refines sample sampleInside formula :=
  match formula with
  | .truth => .stable .truth
  | .falsity => .stable .falsity
  | .atom value =>
      match result : CCL.CCLBoxSign.certificate?
          value.form bounding current refines sample sampleInside with
      | none => .unresolved value (by simp [Formula.atoms]) result
      | some certificate => .stable (.atom value (.strict certificate))
  | .and left right =>
      match inspect left bounding current refines sample sampleInside with
      | .unresolved atom member failure =>
          .unresolved atom (by
            simp only [Formula.atoms, List.mem_append]
            exact Or.inl member) failure
      | .stable leftStable =>
          match inspect right bounding current refines sample sampleInside with
          | .unresolved atom member failure =>
              .unresolved atom (by
                simp only [Formula.atoms, List.mem_append]
                exact Or.inr member) failure
          | .stable rightStable => .stable (.and leftStable rightStable)
  | .or left right =>
      match inspect left bounding current refines sample sampleInside with
      | .unresolved atom member failure =>
          .unresolved atom (by
            simp only [Formula.atoms, List.mem_append]
            exact Or.inl member) failure
      | .stable leftStable =>
          match inspect right bounding current refines sample sampleInside with
          | .unresolved atom member failure =>
              .unresolved atom (by
                simp only [Formula.atoms, List.mem_append]
                exact Or.inr member) failure
          | .stable rightStable => .stable (.or leftStable rightStable)

/-- Reinspection records that a returned failure was not already present in
the finite equality-owner cache. -/
inductive Reinspection
    (bounding current : Box) (refines : current.Refines bounding)
    (sample : Gaussian) (sampleInside : current.Contains sample)
    (overrides : List (Override bounding current)) :
    (formula : Formula) → Type where
  | stable {formula : Formula} (result : Stable bounding current formula) :
      Reinspection bounding current refines sample sampleInside overrides
        formula
  | unresolved {formula : Formula} (atom : Atom)
      (member : atom ∈ formula.atoms)
      (notResolved : findOverride overrides atom = none)
      (failure : CCL.CCLBoxSign.certificate?
        atom.form bounding current refines sample sampleInside = none) :
      Reinspection bounding current refines sample sampleInside overrides
        formula

/-- Structural inspection with a finite cache of equality-owned atoms.  A
new failure is therefore a genuinely different unresolved boundary, so
adding its resolution makes finite progress through the formula's atom
list. -/
def inspectWith
    (bounding current : Box)
    (overrides : List (Override bounding current))
    (formula : Formula)
    (refines : current.Refines bounding) (sample : Gaussian)
    (sampleInside : current.Contains sample) :
    Reinspection bounding current refines sample sampleInside overrides
      formula :=
  match formula with
  | .truth => .stable .truth
  | .falsity => .stable .falsity
  | .atom value =>
      match found : findOverride overrides value with
      | some stability => .stable (.atom value stability)
      | none =>
          match result : CCL.CCLBoxSign.certificate?
              value.form bounding current refines sample sampleInside with
          | none => .unresolved value (by simp [Formula.atoms]) found result
          | some certificate => .stable (.atom value (.strict certificate))
  | .and left right =>
      match inspectWith bounding current overrides left refines sample
          sampleInside with
      | .unresolved atom member notResolved failure =>
          .unresolved atom (by
            simp only [Formula.atoms, List.mem_append]
            exact Or.inl member) notResolved failure
      | .stable leftStable =>
          match inspectWith bounding current overrides right refines sample
              sampleInside with
          | .unresolved atom member notResolved failure =>
              .unresolved atom (by
                simp only [Formula.atoms, List.mem_append]
                exact Or.inr member) notResolved failure
          | .stable rightStable => .stable (.and leftStable rightStable)
  | .or left right =>
      match inspectWith bounding current overrides left refines sample
          sampleInside with
      | .unresolved atom member notResolved failure =>
          .unresolved atom (by
            simp only [Formula.atoms, List.mem_append]
            exact Or.inl member) notResolved failure
      | .stable leftStable =>
          match inspectWith bounding current overrides right refines sample
              sampleInside with
          | .unresolved atom member notResolved failure =>
              .unresolved atom (by
                simp only [Formula.atoms, List.mem_append]
                exact Or.inr member) notResolved failure
          | .stable rightStable => .stable (.or leftStable rightStable)

end CCL.CCLFormulaBoxSign
