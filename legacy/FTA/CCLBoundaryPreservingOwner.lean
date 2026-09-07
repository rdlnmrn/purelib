import FTA.CCLBranchCharts
import FTA.CCLHistoricalEventTangentSigns
import FTA.CCLRationalTangentCone

/-!
# Boundary-preserving historical CCL owners

A reachable finite CCL cylinder can retain the same generalized-circle
boundary in both orientations.  Such faces cannot all be made strict, but a
face whose denominator-cleared polynomial is identically zero on the selected
projective path remains an exact equality at every affine rational parameter.

This module separates those path-equality faces from the genuine crossing
faces.  It also gives the weak realization principle needed by the final
historical sampler: equality faces may remain zero, while only crossing faces
need a nonnegative side choice and canonically strict atoms retain their sign.
-/

namespace FTA
namespace CCLBoundaryPreservingOwner

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLBranchCharts
open FTA.CCLBranchController
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchPlan
open FTA.CCLCanonicalEvent
open FTA.CCLCompleteEventTangentSigns
open FTA.CCLCountOneClassification
open FTA.CCLEventExtraction
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLHistoricalEventOwner
open FTA.CCLHistoricalEventTangentSigns
open FTA.CCLMultiOwnerGrid
open FTA.CCLPathIntersection
open FTA.CCLEventTangentSigns
open FTA.CCLOwnerDirection
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventSemantics
open FTA.CCLPositiveEventConvergence
open FTA.CCLRationalTangentCone
open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.PathPolynomial
open FTA.ProjectivePath
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- If a Hermitian form vanishes at every affine value of a projective path
and the path denominator is not identically zero, then its executable
denominator-cleared restriction is itself identically zero.  Multiplication
by the denominator norm makes the proof cover pole parameters without any
choice of a nearby affine point. -/
theorem clearedForm_isZero_of_vanishes
    (form : HermitianForm) (path : Path)
    (vanishes : ∀ i : Fin
        (((clearedForm form path).toPolynomial *
          (denominatorNorm path).toPolynomial).natDegree + 1),
      let t : ℚ := ((i : ℕ) : ℚ)
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 →
        form.eval (path.value t) = 0)
    (denominatorNonzero : (denominatorNorm path).isZero = false) :
    (clearedForm form path).isZero = true := by
  have productZero :
      (clearedForm form path).toPolynomial *
          (denominatorNorm path).toPolynomial = 0 := by
    apply rationalPolynomial_eq_zero_of_eval_eq_on_fin
    intro i
    let t : ℚ := ((i : ℕ) : ℚ)
    change Polynomial.eval t
      ((clearedForm form path).toPolynomial *
        (denominatorNorm path).toPolynomial) = 0
    rw [Polynomial.eval_mul, eval_toPolynomial, eval_toPolynomial]
    by_cases denominator :
        path.denominator.eval (PathPolynomial.ofRat t) = 0
    · rw [eval_denominatorNorm, denominator, normSq_zero]
      ring
    · have clearedZero : (clearedForm form path).eval t = 0 := by
        rw [eval_clearedForm form path t denominator,
          vanishes i denominator]
        ring
      rw [clearedZero]
      ring
  rcases mul_eq_zero.mp productZero with clearedZero | denominatorZero
  · exact (toPolynomial_eq_zero_iff_isZero _).1 clearedZero
  · exact (toPolynomial_ne_zero_of_isZero_false denominatorNonzero
      denominatorZero).elim

/-- The form represented by a nondegenerate bounded source chart has an
identically-zero cleared restriction along that chart. -/
theorem boundedChart_source_clearedForm_isZero
    {source : CCLBranchPlan.BoundarySource} (chart : BoundedChart source)
    (determinantNonzero : determinant source.matrix ≠ 0)
    (nondegenerate : source.ParametrizationNondegenerate) :
    (clearedForm source.form chart.path).isZero = true := by
  apply clearedForm_isZero_of_vanishes source.form chart.path
  · intro _i
    dsimp only
    intro denominator
    exact chart.onBoundary determinantNonzero denominator
  · exact chart.denominatorNorm_isZero_false determinantNonzero nondegenerate

theorem boundedChart_clearedRealComparison_natDegree_le_one_of_real
    {matrix : Mat2 QI} {sourceThreshold comparisonThreshold : ℚ}
    (chart : BoundedChart (.real matrix sourceThreshold))
    (nonzero : (clearedForm (realComparisonForm matrix comparisonThreshold)
      chart.path).isZero = false) :
    (clearedForm (realComparisonForm matrix comparisonThreshold)
      chart.path).natDegree ≤ 1 := by
  have pathEq : chart.path =
      CCLBoundaryPath.inverseRealBoundaryPath matrix sourceThreshold := by
    simpa [CCLBranchPlan.BoundarySource.paths] using chart.pathMember
  rw [pathEq] at nonzero ⊢
  exact clearedForm_realComparison_inverseReal_natDegree_le_one matrix
    comparisonThreshold sourceThreshold nonzero

theorem boundedChart_clearedImagComparison_natDegree_le_one_of_real
    {matrix : Mat2 QI} {sourceThreshold comparisonThreshold : ℚ}
    (chart : BoundedChart (.real matrix sourceThreshold))
    (nonzero : (clearedForm (imagComparisonForm matrix comparisonThreshold)
      chart.path).isZero = false) :
    (clearedForm (imagComparisonForm matrix comparisonThreshold)
      chart.path).natDegree ≤ 1 := by
  have pathEq : chart.path =
      CCLBoundaryPath.inverseRealBoundaryPath matrix sourceThreshold := by
    simpa [CCLBranchPlan.BoundarySource.paths] using chart.pathMember
  rw [pathEq] at nonzero ⊢
  exact clearedForm_imagComparison_inverseReal_natDegree_le_one matrix
    comparisonThreshold sourceThreshold nonzero

theorem boundedChart_clearedRealComparison_natDegree_le_one_of_imag
    {matrix : Mat2 QI} {sourceThreshold comparisonThreshold : ℚ}
    (chart : BoundedChart (.imag matrix sourceThreshold))
    (nonzero : (clearedForm (realComparisonForm matrix comparisonThreshold)
      chart.path).isZero = false) :
    (clearedForm (realComparisonForm matrix comparisonThreshold)
      chart.path).natDegree ≤ 1 := by
  have pathEq : chart.path =
      CCLBoundaryPath.inverseImagBoundaryPath matrix sourceThreshold := by
    simpa [CCLBranchPlan.BoundarySource.paths] using chart.pathMember
  rw [pathEq] at nonzero ⊢
  exact clearedForm_realComparison_inverseImag_natDegree_le_one matrix
    comparisonThreshold sourceThreshold nonzero

theorem boundedChart_clearedImagComparison_natDegree_le_one_of_imag
    {matrix : Mat2 QI} {sourceThreshold comparisonThreshold : ℚ}
    (chart : BoundedChart (.imag matrix sourceThreshold))
    (nonzero : (clearedForm (imagComparisonForm matrix comparisonThreshold)
      chart.path).isZero = false) :
    (clearedForm (imagComparisonForm matrix comparisonThreshold)
      chart.path).natDegree ≤ 1 := by
  have pathEq : chart.path =
      CCLBoundaryPath.inverseImagBoundaryPath matrix sourceThreshold := by
    simpa [CCLBranchPlan.BoundarySource.paths] using chart.pathMember
  rw [pathEq] at nonzero ⊢
  exact clearedForm_imagComparison_inverseImag_natDegree_le_one matrix
    comparisonThreshold sourceThreshold nonzero

private theorem boundedChart_clearedPullbackRealComparison_natDegree_le_one_of_real
    {outer inner : Mat2 QI} {sourceThreshold comparisonThreshold : ℚ}
    (chart : BoundedChart
      ((CCLBranchPlan.BoundarySource.real inner sourceThreshold).pullback outer))
    (nonzero : (clearedForm
      (pullbackForm outer (realComparisonForm inner comparisonThreshold))
      chart.path).isZero = false) :
    (clearedForm
      (pullbackForm outer (realComparisonForm inner comparisonThreshold))
      chart.path).natDegree ≤ 1 := by
  simp only [CCLBranchPlan.BoundarySource.pullback,
    pullbackForm_realComparison] at nonzero ⊢
  exact boundedChart_clearedRealComparison_natDegree_le_one_of_real
    chart nonzero

private theorem boundedChart_clearedPullbackImagComparison_natDegree_le_one_of_real
    {outer inner : Mat2 QI} {sourceThreshold comparisonThreshold : ℚ}
    (chart : BoundedChart
      ((CCLBranchPlan.BoundarySource.real inner sourceThreshold).pullback outer))
    (nonzero : (clearedForm
      (pullbackForm outer (imagComparisonForm inner comparisonThreshold))
      chart.path).isZero = false) :
    (clearedForm
      (pullbackForm outer (imagComparisonForm inner comparisonThreshold))
      chart.path).natDegree ≤ 1 := by
  simp only [CCLBranchPlan.BoundarySource.pullback,
    pullbackForm_imagComparison] at nonzero ⊢
  exact boundedChart_clearedImagComparison_natDegree_le_one_of_real
    chart nonzero

private theorem boundedChart_clearedPullbackRealComparison_natDegree_le_one_of_imag
    {outer inner : Mat2 QI} {sourceThreshold comparisonThreshold : ℚ}
    (chart : BoundedChart
      ((CCLBranchPlan.BoundarySource.imag inner sourceThreshold).pullback outer))
    (nonzero : (clearedForm
      (pullbackForm outer (realComparisonForm inner comparisonThreshold))
      chart.path).isZero = false) :
    (clearedForm
      (pullbackForm outer (realComparisonForm inner comparisonThreshold))
      chart.path).natDegree ≤ 1 := by
  simp only [CCLBranchPlan.BoundarySource.pullback,
    pullbackForm_realComparison] at nonzero ⊢
  exact boundedChart_clearedRealComparison_natDegree_le_one_of_imag
    chart nonzero

private theorem boundedChart_clearedPullbackImagComparison_natDegree_le_one_of_imag
    {outer inner : Mat2 QI} {sourceThreshold comparisonThreshold : ℚ}
    (chart : BoundedChart
      ((CCLBranchPlan.BoundarySource.imag inner sourceThreshold).pullback outer))
    (nonzero : (clearedForm
      (pullbackForm outer (imagComparisonForm inner comparisonThreshold))
      chart.path).isZero = false) :
    (clearedForm
      (pullbackForm outer (imagComparisonForm inner comparisonThreshold))
      chart.path).natDegree ≤ 1 := by
  simp only [CCLBranchPlan.BoundarySource.pullback,
    pullbackForm_imagComparison] at nonzero ⊢
  exact boundedChart_clearedImagComparison_natDegree_le_one_of_imag
    chart nonzero

/-- Every nonzero form which actually decides the current CCL bit restricts
to an affine polynomial on any planned source chart.  Unary phases have only
their own circle and hence fall into the identically-zero alternative;
sector phases reduce to the four coordinate-line calculations above. -/
theorem inputDecisionForm_clearedForm_natDegree_le_one
    (state : RawParser.State) {source : CCLBranchPlan.BoundarySource}
    (sourceMember : source ∈ inputPlan state)
    (chart : BoundedChart source) (sourceDeterminant :
      determinant source.matrix ≠ 0)
    (sourceNondegenerate : source.ParametrizationNondegenerate)
    (form : HermitianForm) (formMember : form ∈ inputDecisionForms state)
    (nonzero : (clearedForm form chart.path).isZero = false) :
    (clearedForm form chart.path).natDegree ≤ 1 := by
  rcases (mem_inputPlan_iff state source).1 sourceMember with
    ⟨localSource, localSourceMember, rfl⟩
  rcases List.mem_map.mp formMember with
    ⟨localForm, localFormMember, rfl⟩
  by_cases sameForm : localForm = localSource.form
  · subst localForm
    have zero := boundedChart_source_clearedForm_isZero chart
      sourceDeterminant sourceNondegenerate
    have clearedZero :
        (clearedForm (pullbackForm (adjugate state.matrix) localSource.form)
          chart.path).isZero = true := by
      rw [← CCLBranchPlan.BoundarySource.form_pullback]
      exact zero
    exact (Bool.false_ne_true (nonzero.symm.trans clearedZero)).elim
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      simp [localPlan] at localSourceMember
      subst localSource
      simp [localDecisionForms, localForms, localPlan] at localFormMember
      subst localForm
      exact (sameForm rfl).elim
  | highUnary count =>
      simp [localPlan] at localSourceMember
      subst localSource
      simp [localDecisionForms, localForms, localPlan] at localFormMember
      subst localForm
      exact (sameForm rfl).elim
  | lowUnary count =>
      cases count with
      | zero =>
          simp [localPlan] at localSourceMember
          subst localSource
          simp [localDecisionForms, localForms, localPlan] at localFormMember
          subst localForm
          exact (sameForm rfl).elim
      | succ count =>
          simp [localPlan] at localSourceMember
          subst localSource
          simp [localDecisionForms, localForms, localPlan] at localFormMember
          subst localForm
          exact (sameForm rfl).elim
  | loopUnary count =>
      simp [localPlan] at localSourceMember
      subst localSource
      simp [localDecisionForms, localForms, localPlan] at localFormMember
      subst localForm
      exact (sameForm rfl).elim
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simp [localPlan] at localSourceMember
          simp [localDecisionForms, localForms, localPlan] at localFormMember
          rcases localSourceMember with rfl | rfl | rfl
          · rcases localFormMember with rfl | rfl | rfl
            · exact (sameForm rfl).elim
            · exact
                boundedChart_clearedPullbackImagComparison_natDegree_le_one_of_real
                chart nonzero
            · exact
                boundedChart_clearedPullbackImagComparison_natDegree_le_one_of_real
                chart nonzero
          · rcases localFormMember with rfl | rfl | rfl
            · exact
                boundedChart_clearedPullbackRealComparison_natDegree_le_one_of_imag
                chart nonzero
            · exact (sameForm rfl).elim
            · exact
                boundedChart_clearedPullbackImagComparison_natDegree_le_one_of_imag
                chart nonzero
          · rcases localFormMember with rfl | rfl | rfl
            · exact
                boundedChart_clearedPullbackRealComparison_natDegree_le_one_of_imag
                chart nonzero
            · exact
                boundedChart_clearedPullbackImagComparison_natDegree_le_one_of_imag
                chart nonzero
            · exact (sameForm rfl).elim
      | one first =>
          cases first with
          | false =>
              simp [localPlan] at localSourceMember
              simp [localDecisionForms] at localFormMember
              subst localForm
              rcases localSourceMember with rfl | rfl | rfl
              · exact (sameForm rfl).elim
              · exact
                  boundedChart_clearedPullbackRealComparison_natDegree_le_one_of_imag
                  chart nonzero
              · exact
                  boundedChart_clearedPullbackRealComparison_natDegree_le_one_of_real
                  chart nonzero
          | true =>
              simp [localPlan] at localSourceMember
              simp [localDecisionForms] at localFormMember
              subst localForm
              rcases localSourceMember with rfl | rfl | rfl
              · exact (sameForm rfl).elim
              · exact
                  boundedChart_clearedPullbackRealComparison_natDegree_le_one_of_imag
                  chart nonzero
              · exact
                  boundedChart_clearedPullbackRealComparison_natDegree_le_one_of_real
                  chart nonzero
      | two first second =>
          cases first <;> cases second <;>
            simp [localPlan] at localSourceMember <;>
            simp [localDecisionForms, localForms, localPlan] at localFormMember <;>
            subst localSource <;> subst localForm <;>
            exact (sameForm rfl).elim

/-- Faces whose cleared restriction to a projective path is the zero
polynomial.  The test is finite and executable. -/
def pathEqualityForms (forms : List HermitianForm) (path : Path) :
    List HermitianForm :=
  forms.filter fun form => decide ((clearedForm form path).isZero = true)

/-- The complementary active faces: their cleared path restrictions are
genuine nonzero polynomials. -/
def pathCrossingForms (forms : List HermitianForm) (path : Path) :
    List HermitianForm :=
  forms.filter fun form => decide ((clearedForm form path).isZero = false)

@[simp] theorem mem_pathEqualityForms_iff
    (forms : List HermitianForm) (path : Path) (form : HermitianForm) :
    form ∈ pathEqualityForms forms path ↔
      form ∈ forms ∧ (clearedForm form path).isZero = true := by
  simp [pathEqualityForms]

@[simp] theorem mem_pathCrossingForms_iff
    (forms : List HermitianForm) (path : Path) (form : HermitianForm) :
    form ∈ pathCrossingForms forms path ↔
      form ∈ forms ∧ (clearedForm form path).isZero = false := by
  simp [pathCrossingForms]

/-- Every source face belongs to exactly one of the two executable path
classes. -/
theorem mem_pathEqualityForms_or_mem_pathCrossingForms
    (forms : List HermitianForm) (path : Path) {form : HermitianForm}
    (member : form ∈ forms) :
    form ∈ pathEqualityForms forms path ∨
      form ∈ pathCrossingForms forms path := by
  cases zero : (clearedForm form path).isZero with
  | false => exact Or.inr (by simp [member, zero])
  | true => exact Or.inl (by simp [member, zero])

/-- No face can be both identically zero and a genuine crossing on the same
path. -/
theorem pathEqualityForms_disjoint_pathCrossingForms
    (forms : List HermitianForm) (path : Path) :
    List.Disjoint (pathEqualityForms forms path)
      (pathCrossingForms forms path) := by
  rw [List.disjoint_left]
  intro form equalityMember crossingMember
  have equalityZero := (mem_pathEqualityForms_iff forms path form).1
    equalityMember
  have crossingNonzero := (mem_pathCrossingForms_iff forms path form).1
    crossingMember
  simp [equalityZero.2] at crossingNonzero

/-- An identically-zero cleared form is an exact equality at every affine
rational path value. -/
theorem eval_eq_zero_of_mem_pathEqualityForms
    (forms : List HermitianForm) (path : Path) {form : HermitianForm}
    (member : form ∈ pathEqualityForms forms path) (t : ℚ)
    (denominator : path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    form.eval (path.value t) = 0 := by
  have zero := (mem_pathEqualityForms_iff forms path form).1 member
  have clearedZero := eval_eq_zero_of_isZero zero.2 t
  rw [eval_clearedForm form path t denominator] at clearedZero
  exact (mul_eq_zero.mp clearedZero).resolve_left
    (eval_denominatorNorm_pos path t denominator).ne'

/-- List-facing form of exact equality preservation. -/
theorem pathEqualityForms_eval_zero
    (forms : List HermitianForm) (path : Path) (t : ℚ)
    (denominator : path.denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    ∀ form ∈ pathEqualityForms forms path,
      form.eval (path.value t) = 0 := by
  intro form member
  exact eval_eq_zero_of_mem_pathEqualityForms forms path member t denominator

/-- A canonically active parser atom remains true when its oriented weak form
is merely nonnegative.  Strict positivity is unnecessary on a retained
boundary stratum. -/
theorem activeSatisfyingAtom_holds_of_oriented_nonneg
    {formula : Formula} {value : HermitianForm → ℚ}
    (evaluation : formulaEvalWith formula value = true)
    (noZeroTest : ∀ atom ∈ satisfyingAtoms formula value,
      atom.sign ≠ .zero)
    {atom : Atom} (member : atom ∈ activeSatisfyingAtoms formula value)
    {point : QI} (nonnegative : 0 ≤ (orientedWeakForm atom).eval point) :
    atom.Holds point := by
  rcases activeSatisfyingAtom_sign_weak evaluation noZeroTest member with
      nonpositive | nonnegativeSign
  · simp only [nonpositive, orientedWeakForm, HermitianForm.eval_neg]
      at nonnegative
    simp only [Atom.Holds, nonpositive, SignTest.Holds]
    linarith
  · simpa only [Atom.Holds, nonnegativeSign, SignTest.Holds,
      orientedWeakForm] using nonnegative

/-- Realize a true canonical formula while allowing active weak faces to stay
on equality. -/
theorem formula_holds_of_active_weak_strict
    (formula : Formula) (value : HermitianForm → ℚ) (point : QI)
    (evaluation : formulaEvalWith formula value = true)
    (noZeroTest : ∀ atom ∈ satisfyingAtoms formula value,
      atom.sign ≠ .zero)
    (activeNonnegative : ∀ atom ∈ activeSatisfyingAtoms formula value,
      0 ≤ (orientedWeakForm atom).eval point)
    (strictSameSign : ∀ atom ∈ strictSatisfyingAtoms formula value,
      0 < value atom.form * atom.form.eval point) :
    formula.Holds point := by
  apply formula_holds_of_satisfyingAtoms formula value point evaluation
  intro atom source
  by_cases zero : value atom.form = 0
  · apply activeSatisfyingAtom_holds_of_oriented_nonneg evaluation
      noZeroTest
      (List.mem_filter.mpr ⟨source, by simpa only [decide_eq_true_eq]⟩)
    exact activeNonnegative atom
      (List.mem_filter.mpr ⟨source, by simpa only [decide_eq_true_eq]⟩)
  · apply strictSatisfyingAtom_holds_of_mul_pos evaluation
      (List.mem_filter.mpr ⟨source, by simpa only [decide_eq_true_eq]⟩)
    exact strictSameSign atom
      (List.mem_filter.mpr ⟨source, by simpa only [decide_eq_true_eq]⟩)

/-- List-facing weak realization principle matching the active and strict
owner lists used by the CCL grid construction. -/
theorem formula_holds_of_owner_form_lists_nonnegative
    (formula : Formula) (value : HermitianForm → ℚ) (point : QI)
    (evaluation : formulaEvalWith formula value = true)
    (noZero : formulaNoZeroTests formula)
    (activeNonnegative : ∀ form ∈ activeOwnerForms formula value,
      0 ≤ form.eval point)
    (strictSameSign : ∀ form ∈ strictPriorForms formula value,
      0 < value form * form.eval point) :
    formula.Holds point := by
  apply formula_holds_of_active_weak_strict formula value point evaluation
    (satisfyingAtoms_noZeroTest formula value noZero)
  · intro atom member
    apply activeNonnegative (orientedWeakForm atom)
    exact List.mem_map.mpr ⟨atom, member, rfl⟩
  · intro atom member
    apply strictSameSign atom.form
    exact List.mem_map.mpr ⟨atom, member, rfl⟩

/-- A formula is realized on a rational path sample once only its genuine
crossing faces have been placed on their weak owner side; identically-zero
faces are discharged automatically. -/
theorem formula_holds_of_path_owner_partition
    (formula : Formula) (value : HermitianForm → ℚ)
    (path : Path) (t : ℚ)
    (evaluation : formulaEvalWith formula value = true)
    (noZero : formulaNoZeroTests formula)
    (denominator : path.denominator.eval (PathPolynomial.ofRat t) ≠ 0)
    (crossingNonnegative :
      ∀ form ∈ pathCrossingForms (activeOwnerForms formula value) path,
        0 ≤ form.eval (path.value t))
    (strictSameSign : ∀ form ∈ strictPriorForms formula value,
      0 < value form * form.eval (path.value t)) :
    formula.Holds (path.value t) := by
  apply formula_holds_of_owner_form_lists_nonnegative formula value
    (path.value t) evaluation noZero
  · intro form member
    rcases mem_pathEqualityForms_or_mem_pathCrossingForms
        (activeOwnerForms formula value) path member with
      equalityMember | crossingMember
    · rw [eval_eq_zero_of_mem_pathEqualityForms
          (activeOwnerForms formula value) path equalityMember t denominator]
    · exact crossingNonnegative form crossingMember
  · exact strictSameSign

/-- Historical active faces that are identically zero along the selected
source path. -/
def historicalPathEqualityForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : List HermitianForm :=
  pathEqualityForms (historicalActiveOwnerForms selected)
    (selectedCompletePath selected)

/-- The complementary historical faces whose source-path restrictions are
nonzero. -/
def historicalPathCrossingForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : List HermitianForm :=
  pathCrossingForms (historicalActiveOwnerForms selected)
    (selectedCompletePath selected)

/-- The planned source carried by a reachable selected historical event is
identically zero after denominator clearing along its selected chart. -/
theorem historicalSource_clearedForm_isZero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation) :
    (clearedForm
      selected.candidate.sourceEvent.partition.entry.source.form
      (selectedCompletePath selected)).isZero = true := by
  let state := RawParser.parse current.word
  let source := selected.candidate.sourceEvent.partition.entry.source
  let chart := selected.candidate.sourceEvent.partition.entry.chart
  have stateDeterminant : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.word
  have sourceDeterminant : determinant source.matrix ≠ 0 :=
    CCLBranchPlan.inputPlan_determinant_ne state selected.sourceMember
      stateDeterminant
  have nondegenerate : source.ParametrizationNondegenerate :=
    CCLBranchPlan.inputPlan_parametrizationNondegenerate state
      selected.sourceMember
  simpa only [state, source, chart, selectedPath] using
    boundedChart_source_clearedForm_isZero chart sourceDeterminant
      nondegenerate

/-- The history-refined algebraic oracle therefore assigns exact zero to the
planned source form, independently of whether that source is an active face
of the selected satisfying branch. -/
theorem historicalCanonicalValue_source_eq_zero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation) :
    historicalCanonicalValue selected
      selected.candidate.sourceEvent.partition.entry.source.form = 0 := by
  let cell := historicalInputCell selected
  let form := selected.candidate.sourceEvent.partition.entry.source.form
  have clearedZero :
      (clearedForm form (selectedCompletePath selected)).toPolynomial = 0 :=
    (toPolynomial_eq_zero_iff_isZero _).2
      (historicalSource_clearedForm_isZero current separation selected)
  have divides : cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm form (selectedCompletePath selected)).toPolynomial := by
    rw [clearedZero]
    exact dvd_zero _
  simpa only [historicalCanonicalValue, inputEventCanonicalValue,
    historicalInputCell, selectedPath, cell, form] using
      canonicalEventValue_eq_zero_of_dvd cell.branch.factor.input
        (clearedForm form (selectedCompletePath selected))
        (cell.branch.computeEventSigns cell.parent).refined.interval.lower
        divides

/-- Reversing the orientation of the selected source does not change its
identically-zero path restriction. -/
theorem historicalSource_neg_clearedForm_isZero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation) :
    (clearedForm
      selected.candidate.sourceEvent.partition.entry.source.form.neg
      (selectedCompletePath selected)).isZero = true := by
  let source := selected.candidate.sourceEvent.partition.entry.source
  let chart := selected.candidate.sourceEvent.partition.entry.chart
  let state := RawParser.parse current.word
  have stateDeterminant : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.word
  have sourceDeterminant : determinant source.matrix ≠ 0 :=
    CCLBranchPlan.inputPlan_determinant_ne state selected.sourceMember
      stateDeterminant
  have nondegenerate : source.ParametrizationNondegenerate :=
    CCLBranchPlan.inputPlan_parametrizationNondegenerate state
      selected.sourceMember
  apply clearedForm_isZero_of_vanishes source.form.neg chart.path
  · intro t
    dsimp only
    intro denominator
    have zero : source.form.eval (chart.path.value ((t : ℕ) : ℚ)) = 0 :=
      chart.onBoundary sourceDeterminant denominator
    rw [HermitianForm.eval_neg, zero, neg_zero]
  · exact chart.denominatorNorm_isZero_false sourceDeterminant nondegenerate

/-- Whenever the selected source (in either weak orientation) really occurs
among the historical active owners, it is an executable path-equality face.
The source label itself is intentionally not assumed active. -/
theorem historicalSource_mem_pathEqualityForms_of_active
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (active :
      selected.candidate.sourceEvent.partition.entry.source.form ∈
          historicalActiveOwnerForms selected ∨
        selected.candidate.sourceEvent.partition.entry.source.form.neg ∈
          historicalActiveOwnerForms selected) :
    historicalPathEqualityForms selected ≠ [] := by
  intro empty
  rcases active with sourceActive | sourceNegActive
  · have member :
        selected.candidate.sourceEvent.partition.entry.source.form ∈
          historicalPathEqualityForms selected := by
      exact (mem_pathEqualityForms_iff _ _ _).2
        ⟨sourceActive,
          historicalSource_clearedForm_isZero current separation selected⟩
    rw [empty] at member
    simp at member
  · have member :
        selected.candidate.sourceEvent.partition.entry.source.form.neg ∈
          historicalPathEqualityForms selected := by
      exact (mem_pathEqualityForms_iff _ _ _).2
        ⟨sourceNegActive,
          historicalSource_neg_clearedForm_isZero current separation selected⟩
    rw [empty] at member
    simp at member

/-- Every historical path-equality face remains exactly zero at every affine
rational parameter on the selected source path. -/
theorem historicalPathEqualityForms_eval_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (t : ℚ)
    (denominator :
      (selectedCompletePath selected).denominator.eval (PathPolynomial.ofRat t) ≠ 0) :
    ∀ form ∈ historicalPathEqualityForms selected,
      form.eval ((selectedCompletePath selected).value t) = 0 := by
  exact pathEqualityForms_eval_zero (historicalActiveOwnerForms selected)
    (selectedCompletePath selected) t denominator

/-- Parser formulas contain no exact-equality tests, so the conjunction of
the old prefix and selected child is eligible for weak boundary realization. -/
theorem historicalOwnerFormula_noZeroTests
    (state : RawParser.State) (bit : Bool) :
    formulaNoZeroTests (historicalOwnerFormula state bit) := by
  exact ⟨inputStateFormula_noZeroTests state,
    inputAdvanceFormula_noZeroTests state bit⟩

private theorem canonical_mul_form_eval_pos_of_cleared
    (canonical : ℚ) (form : HermitianForm) (path : Path) (t : ℚ)
    (denominator : path.denominator.eval (PathPolynomial.ofRat t) ≠ 0)
    (clearedPositive :
      0 < canonical * (clearedForm form path).eval t) :
    0 < canonical * form.eval (path.value t) := by
  rw [eval_clearedForm form path t denominator] at clearedPositive
  have reordered :
      0 < (denominatorNorm path).eval t *
        (canonical * form.eval (path.value t)) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using clearedPositive
  rcases mul_pos_iff.mp reordered with positive | negative
  · exact positive.2
  · exact (not_lt_of_ge
      (eval_denominatorNorm_pos path t denominator).le negative.1).elim

/-- A canonically strict current-prefix face retains its sign at every
rational parameter in the final historical slope interval. -/
theorem historicalCurrentStrictPrior_mul_eval_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (member : form ∈ strictPriorForms (inputStateFormula state)
      (historicalCanonicalValue selected))
    {t : ℚ}
    (lower : (historicalSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (historicalSlopeSigns selected).refined.interval.upper) :
    0 < historicalCanonicalValue selected form *
      form.eval ((selectedCompletePath selected).value t) := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  let classification :=
    currentFormulaClassification selected.candidate.inputCell
  let currentSigns := classification.branch.computeEventSigns
    classification.parent
  let cell := historicalInputCell selected
  let finalSigns := cell.branch.computeEventSigns cell.parent
  have polynomialMember : clearedForm atom.form (selectedCompletePath selected) ∈
      eventFormulaPolynomials (inputStateFormula state)
        (selectedCompletePath selected) :=
    List.mem_map.mpr
      ⟨atom, satisfyingAtoms_mem_formulaAtoms _ _
        (strictSatisfyingAtoms_source atomMember), rfl⟩
  have finalLower : finalSigns.refined.interval.lower ≤ t :=
    (historicalSlopeSigns_refines_inputCell selected).1.trans lower
  have finalUpper : t ≤ finalSigns.refined.interval.upper :=
    upper.trans (historicalSlopeSigns_refines_inputCell selected).2
  have currentLower : currentSigns.refined.interval.lower ≤ t :=
    finalSigns.refines.1.trans finalLower
  have currentUpper : t ≤ currentSigns.refined.interval.upper :=
    finalUpper.trans finalSigns.refines.2
  have sampleLower : currentSigns.refined.interval.lower ≤
      finalSigns.refined.interval.lower := finalSigns.refines.1
  have sampleUpper : finalSigns.refined.interval.lower ≤
      currentSigns.refined.interval.upper :=
    finalSigns.refined.proper.le.trans finalSigns.refines.2
  have historicalNonzero :
      historicalCanonicalValue selected atom.form ≠ 0 :=
    strictPriorForms_value_ne _ _ member
  have sameCanonicalSign (test : SignTest) :
      test.Holds
          (canonicalEventValue classification.branch.factor.input
            (clearedForm atom.form (selectedCompletePath selected))
            currentSigns.refined.interval.lower) ↔
        test.Holds (historicalCanonicalValue selected atom.form) := by
    have agreement :=
      ConditionRelations.canonicalEventValue_holds_iff_between
        classification.branch.relations classification.parent currentSigns
        polynomialMember test sampleLower sampleUpper
    simpa only [historicalCanonicalValue, inputEventCanonicalValue,
      historicalInputCell, currentFormulaInputCell, classification,
      currentSigns, cell, finalSigns, selectedPath] using agreement
  let currentCanonical :=
    canonicalEventValue classification.branch.factor.input
      (clearedForm atom.form (selectedCompletePath selected))
      currentSigns.refined.interval.lower
  have currentNonzero : currentCanonical ≠ 0 := by
    rcases lt_or_gt_of_ne historicalNonzero with negative | positive
    · have currentNegative : currentCanonical < 0 := by
        exact (sameCanonicalSign .negative).2 negative
      exact ne_of_lt currentNegative
    · have currentPositive : 0 < currentCanonical := by
        exact (sameCanonicalSign .positive).2 positive
      exact ne_of_gt currentPositive
  have clearedProduct : 0 < currentCanonical *
      (clearedForm atom.form (selectedCompletePath selected)).eval t := by
    exact ConditionRelations.canonicalEventValue_mul_eval_pos
      classification.branch.relations classification.parent currentSigns
      polynomialMember currentNonzero currentLower currentUpper
  have currentProduct : 0 < currentCanonical *
      atom.form.eval ((selectedCompletePath selected).value t) := by
    apply canonical_mul_form_eval_pos_of_cleared currentCanonical atom.form
      (selectedCompletePath selected) t
    · exact cell.path_denominator_ne_on_cell finalLower finalUpper
    · exact clearedProduct
  rcases lt_or_gt_of_ne historicalNonzero with historicalNegative |
      historicalPositive
  · have currentNegative : currentCanonical < 0 :=
      (sameCanonicalSign .negative).2 historicalNegative
    have evaluationNegative :
        atom.form.eval ((selectedCompletePath selected).value t) < 0 := by
      rcases mul_pos_iff.mp currentProduct with positive | negative
      · exact (not_lt_of_ge positive.1.le currentNegative).elim
      · exact negative.2
    exact mul_pos_of_neg_of_neg historicalNegative evaluationNegative
  · have currentPositive : 0 < currentCanonical :=
      (sameCanonicalSign .positive).2 historicalPositive
    have evaluationPositive :
        0 < atom.form.eval ((selectedCompletePath selected).value t) := by
      rcases mul_pos_iff.mp currentProduct with positive | negative
      · exact positive.2
      · exact (not_lt_of_ge currentPositive.le negative.1).elim
    exact mul_pos historicalPositive evaluationPositive

/-- A canonically strict selected-child face has the same persistence
property on the final historical slope interval. -/
theorem historicalChildStrictPrior_mul_eval_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (member : form ∈ strictPriorForms
      (inputAdvanceFormula state selected.bit)
      (historicalCanonicalValue selected))
    {t : ℚ}
    (lower : (historicalSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (historicalSlopeSigns selected).refined.interval.upper) :
    0 < historicalCanonicalValue selected form *
      form.eval ((selectedCompletePath selected).value t) := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  let cell := historicalInputCell selected
  let signs := cell.branch.computeEventSigns cell.parent
  have polynomialMember : clearedForm atom.form (selectedCompletePath selected) ∈
      inputEventPolynomials state (selectedCompletePath selected) :=
    clearedForm_mem_inputEventPolynomials_of_advance_atom state
      (selectedCompletePath selected) selected.bit atom
      (satisfyingAtoms_mem_formulaAtoms _ _
        (strictSatisfyingAtoms_source atomMember))
  have cellLower : signs.refined.interval.lower ≤ t :=
    (historicalSlopeSigns_refines_inputCell selected).1.trans lower
  have cellUpper : t ≤ signs.refined.interval.upper :=
    upper.trans (historicalSlopeSigns_refines_inputCell selected).2
  have canonicalNonzero :
      historicalCanonicalValue selected atom.form ≠ 0 :=
    strictPriorForms_value_ne _ _ member
  have clearedProduct :
      0 < historicalCanonicalValue selected atom.form *
        (clearedForm atom.form (selectedCompletePath selected)).eval t := by
    have product :=
      ConditionRelations.canonicalEventValue_mul_eval_pos
        cell.branch.relations cell.parent signs polynomialMember
        (by simpa only [historicalCanonicalValue, inputEventCanonicalValue,
          cell, signs, selectedPath] using canonicalNonzero)
        cellLower cellUpper
    simpa only [historicalCanonicalValue, inputEventCanonicalValue,
      cell, signs, selectedPath] using product
  apply canonical_mul_form_eval_pos_of_cleared
    (historicalCanonicalValue selected atom.form) atom.form
    (selectedCompletePath selected) t
  · exact cell.path_denominator_ne_on_cell cellLower cellUpper
  · exact clearedProduct

/-- Every canonically strict face of the complete historical conjunction
retains its sign throughout the final classified interval. -/
theorem historicalStrictPriorForms_mul_eval_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {t : ℚ}
    (lower : (historicalSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (historicalSlopeSigns selected).refined.interval.upper) :
    ∀ form ∈ historicalStrictPriorForms selected,
      0 < historicalCanonicalValue selected form *
        form.eval ((selectedCompletePath selected).value t) := by
  intro form member
  rw [historicalStrictPriorForms_eq_append] at member
  rcases List.mem_append.mp member with currentMember | childMember
  · exact historicalCurrentStrictPrior_mul_eval_pos selected currentMember
      lower upper
  · exact historicalChildStrictPrior_mul_eval_pos selected childMember
      lower upper

/-- The selected historical conjunction is realized by a rational source-path
sample once its genuine crossing faces lie on their weak owner side and its
canonical strict atoms retain their signs.  Path-equality faces require no
strict tangent and are discharged internally. -/
theorem historicalOwnerFormula_holds_of_path_partition
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    (t : ℚ)
    (denominator :
      (selectedCompletePath selected).denominator.eval (PathPolynomial.ofRat t) ≠ 0)
    (crossingNonnegative :
      ∀ form ∈ historicalPathCrossingForms selected,
        0 ≤ form.eval ((selectedCompletePath selected).value t))
    (strictSameSign :
      ∀ form ∈ historicalStrictPriorForms selected,
        0 < historicalCanonicalValue selected form *
          form.eval ((selectedCompletePath selected).value t)) :
    (historicalOwnerFormula (RawParser.parse current.word) selected.bit).Holds
      ((selectedCompletePath selected).value t) := by
  apply formula_holds_of_path_owner_partition
    (historicalOwnerFormula (RawParser.parse current.word) selected.bit)
    (historicalCanonicalValue selected) (selectedCompletePath selected) t
    (historicalOwnerFormula_canonical_holds current separation selected
      squarefree degreeNonzero elimination valid)
    (historicalOwnerFormula_noZeroTests
      (RawParser.parse current.word) selected.bit)
    denominator
  · simpa only [historicalPathCrossingForms,
      historicalActiveOwnerForms] using crossingNonnegative
  · simpa only [historicalStrictPriorForms] using strictSameSign

/-- The two rational endpoints of the fully classified historical event
cell.  A path-preserving branch needs to test only these two explicit side
representatives. -/
def historicalPathParameters
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : List ℚ :=
  [(historicalSlopeSigns selected).refined.interval.lower,
    (historicalSlopeSigns selected).refined.interval.upper]

/-- Exact weak-owner test for only the genuine crossing faces at one rational
path parameter. -/
def historicalCrossingsNonnegative?
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (t : ℚ) : Bool :=
  (historicalPathCrossingForms selected).all fun form =>
    decide (0 ≤ form.eval ((selectedCompletePath selected).value t))

theorem historicalCrossingsNonnegative?_eq_true_iff
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (t : ℚ) :
    historicalCrossingsNonnegative? selected t = true ↔
      ∀ form ∈ historicalPathCrossingForms selected,
        0 ≤ form.eval ((selectedCompletePath selected).value t) := by
  simp [historicalCrossingsNonnegative?]

/-- Finite side search that examines the lower and upper rational endpoints
of the fully classified historical event interval. -/
def historicalCrossingParameter?
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : Option ℚ :=
  (historicalPathParameters selected).find? fun t =>
    historicalCrossingsNonnegative? selected t

/-- Executable split between a boundary-preserving path side and the
remaining transverse geometric case. -/
inductive HistoricalSamplingPlan
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : Type where
  | path (parameter : ℚ)
      (search : historicalCrossingParameter? selected = some parameter)
  | transverse (failure : historicalCrossingParameter? selected = none)

def decideHistoricalSamplingPlan
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    HistoricalSamplingPlan selected := by
  cases search : historicalCrossingParameter? selected with
  | none => exact .transverse search
  | some parameter => exact .path parameter search

/-- Failure of the two-side path test is quantitative: at each displayed
endpoint, at least one genuine crossing face is strictly violated.  This is
the exact finite obstruction handed to the transverse fallback. -/
theorem historicalCrossingParameter?_eq_none_violates_each_endpoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (failure : historicalCrossingParameter? selected = none) :
    ∀ t ∈ historicalPathParameters selected,
      ∃ form ∈ historicalPathCrossingForms selected,
        form.eval ((selectedCompletePath selected).value t) < 0 := by
  intro t parameterMember
  by_contra noViolation
  have allNonnegative :
      ∀ form ∈ historicalPathCrossingForms selected,
        0 ≤ form.eval ((selectedCompletePath selected).value t) := by
    intro form formMember
    apply le_of_not_gt
    intro negative
    exact noViolation ⟨form, formMember, negative⟩
  have check : historicalCrossingsNonnegative? selected t = true :=
    (historicalCrossingsNonnegative?_eq_true_iff selected t).2
      allNonnegative
  have succeeds : (historicalCrossingParameter? selected).isSome := by
    rw [historicalCrossingParameter?, List.find?_isSome]
    exact ⟨t, parameterMember, check⟩
  rw [failure] at succeeds
  simp at succeeds

/-- Complete executable geometric split.  A selected historical event either
has a boundary-preserving rational path side, has one of the existing eight
strict tangent directions for every active face, or exposes the exact pair of
finite search failures that the remaining parser-compatibility theorem must
exclude. -/
inductive HistoricalOwnerSamplingPlan
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : Type where
  | path (parameter : ℚ)
      (search : historicalCrossingParameter? selected = some parameter)
  | tangent (direction : QI)
      (search : historicalClassifiedTangentDirection? selected =
        some direction)
  | obstructed
      (pathFailure : historicalCrossingParameter? selected = none)
      (tangentFailure :
        historicalClassifiedTangentDirection? selected = none)

def decideHistoricalOwnerSamplingPlan
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    HistoricalOwnerSamplingPlan selected := by
  cases pathSearch : historicalCrossingParameter? selected with
  | some parameter => exact .path parameter pathSearch
  | none =>
      cases tangentSearch :
          historicalClassifiedTangentDirection? selected with
      | some direction => exact .tangent direction tangentSearch
      | none => exact .obstructed pathSearch tangentSearch

/-- The obstructed branch necessarily contains a genuine crossing face; the
pure equality stratum was already closed by either endpoint. -/
theorem historicalOwnerSamplingPlan_obstructed_crossings_ne_nil
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (pathFailure : historicalCrossingParameter? selected = none) :
    historicalPathCrossingForms selected ≠ [] := by
  intro noCrossings
  have succeeds : (historicalCrossingParameter? selected).isSome := by
    rw [historicalCrossingParameter?, List.find?_isSome]
    refine ⟨(historicalSlopeSigns selected).refined.interval.lower, ?_, ?_⟩
    · simp [historicalPathParameters]
    · apply (historicalCrossingsNonnegative?_eq_true_iff selected _).2
      simp [noCrossings]
  rw [pathFailure] at succeeds
  simp at succeeds

/-- Under the ordinary parsed-event hypotheses, failure of the strict compass
search forces at least two active faces.  Empty and singleton cones have
already been proved total constructively. -/
theorem historicalOwnerSamplingPlan_obstructed_active_length_ge_two
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    (tangentFailure :
      historicalClassifiedTangentDirection? selected = none) :
    2 ≤ (historicalActiveOwnerForms selected).length := by
  by_contra notTwo
  have lengthLeOne : (historicalActiveOwnerForms selected).length ≤ 1 := by
    omega
  have succeeds :=
    historicalClassifiedTangentDirection?_isSome_of_parsed_length_le_one
      current separation selected squarefree degreeNonzero elimination
      valid lengthLeOne
  rw [tangentFailure] at succeeds
  simp at succeeds

/-- For a displayed two-face obstruction, the invariant angle gap cannot be
positive; otherwise the fixed compass table already supplies a common strict
direction. -/
theorem historicalOwnerSamplingPlan_obstructed_pair_angleGap_nonpos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (forms : historicalActiveOwnerForms selected = [left, right])
    (tangentFailure :
      historicalClassifiedTangentDirection? selected = none) :
    boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2 ≤ 0 := by
  apply le_of_not_gt
  intro positive
  have succeeds :=
    historicalClassifiedTangentDirection?_isSome_of_pair_angleGap selected
      forms positive
  rw [tangentFailure] at succeeds
  simp at succeeds

/-- Executable two-endpoint search for a rational source-path realization of
the complete historical conjunction. -/
def historicalPathParameter?
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : Option ℚ :=
  (historicalPathParameters selected).find? fun t =>
    pathEvalBool (historicalOwnerFormula state selected.bit)
      (selectedCompletePath selected) t

/-- Every candidate in the endpoint search lies in the final common-sign
interval. -/
theorem historicalPathParameters_bounds
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {t : ℚ}
    (member : t ∈ historicalPathParameters selected) :
    (historicalSlopeSigns selected).refined.interval.lower ≤ t ∧
      t ≤ (historicalSlopeSigns selected).refined.interval.upper := by
  simp [historicalPathParameters] at member
  rcases member with rfl | rfl
  · exact ⟨le_rfl, (historicalSlopeSigns selected).refined.proper.le⟩
  · exact ⟨(historicalSlopeSigns selected).refined.proper.le, le_rfl⟩

/-- The selected source path is affine at both rational endpoint candidates. -/
theorem historicalPathParameters_denominator_ne
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {t : ℚ}
    (member : t ∈ historicalPathParameters selected) :
    (selectedCompletePath selected).denominator.eval (PathPolynomial.ofRat t) ≠ 0 := by
  have bounds := historicalPathParameters_bounds selected member
  apply (historicalInputCell selected).path_denominator_ne_on_cell
  · exact (historicalSlopeSigns_refines_inputCell selected).1.trans bounds.1
  · exact bounds.2.trans
      (historicalSlopeSigns_refines_inputCell selected).2

/-- A successful endpoint search returns an actual rational realization of
the old prefix and selected child, not merely a canonical-oracle check. -/
theorem historicalPathParameter?_some_holds
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {t : ℚ}
    (search : historicalPathParameter? selected = some t) :
    (historicalOwnerFormula state selected.bit).Holds
      ((selectedCompletePath selected).value t) := by
  have member : t ∈ historicalPathParameters selected :=
    List.mem_of_find?_eq_some search
  apply (pathEvalBool_eq_true_iff
    (historicalOwnerFormula state selected.bit) (selectedCompletePath selected) t
    (historicalPathParameters_denominator_ne selected member)).1
  exact List.find?_some search

/-- Final executable search split using the complete historical formula at
the two source-path sides, rather than only one preselected satisfying-atom
conjunction.  This admits Boolean disjunct switching at an equality event. -/
inductive HistoricalFormulaSamplingPlan
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : Type where
  | path (parameter : ℚ)
      (search : historicalPathParameter? selected = some parameter)
  | tangent (direction : QI)
      (search : historicalClassifiedTangentDirection? selected =
        some direction)
  | obstructed
      (pathFailure : historicalPathParameter? selected = none)
      (tangentFailure :
        historicalClassifiedTangentDirection? selected = none)

def decideHistoricalFormulaSamplingPlan
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    HistoricalFormulaSamplingPlan selected := by
  cases pathSearch : historicalPathParameter? selected with
  | some parameter => exact .path parameter pathSearch
  | none =>
      cases tangentSearch :
          historicalClassifiedTangentDirection? selected with
      | some direction => exact .tangent direction tangentSearch
      | none => exact .obstructed pathSearch tangentSearch

/-- Failure of the stronger path branch means that the actual old-prefix and
selected-child conjunction fails at both displayed affine source sides. -/
theorem historicalPathParameter?_eq_none_fails_each_endpoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (failure : historicalPathParameter? selected = none) :
    ∀ t ∈ historicalPathParameters selected,
      ¬(historicalOwnerFormula state selected.bit).Holds
        ((selectedCompletePath selected).value t) := by
  intro t member holds
  have denominator := historicalPathParameters_denominator_ne selected member
  have checkTrue : pathEvalBool
      (historicalOwnerFormula state selected.bit)
      (selectedCompletePath selected) t = true :=
    (pathEvalBool_eq_true_iff
      (historicalOwnerFormula state selected.bit)
      (selectedCompletePath selected) t denominator).2 holds
  have succeeds : (historicalPathParameter? selected).isSome := by
    rw [historicalPathParameter?, List.find?_isSome]
    exact ⟨t, member, checkTrue⟩
  rw [failure] at succeeds
  simp at succeeds

/-- Failure of the strict compass search exposes a concrete active face with
nonpositive classified slope in every displayed rational direction. -/
theorem historicalClassifiedTangentDirection?_eq_none_violates_each_direction
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (failure : historicalClassifiedTangentDirection? selected = none) :
    ∀ direction : QI,
      direction ∈ CCLMultiOwnerGrid.coordinateDirections →
      ∃ form ∈ historicalActiveOwnerForms selected,
        historicalSlopeValue selected form direction ≤ 0 := by
  intro direction directionMember
  by_contra noViolation
  have allPositive : ∀ form ∈ historicalActiveOwnerForms selected,
      0 < historicalSlopeValue selected form direction := by
    intro form formMember
    apply lt_of_not_ge
    intro nonpositive
    exact noViolation ⟨form, formMember, nonpositive⟩
  have succeeds :
      (historicalClassifiedTangentDirection? selected).isSome :=
    historicalClassifiedTangentDirection?_isSome_of_exists selected
      ⟨direction, directionMember, allPositive⟩
  rw [failure] at succeeds
  simp at succeeds

/-- Exact dynamic tangent search at any affine point of the selected source
path.  Unlike the historical compass classifier, this searches the complete
rational strict cone generated by the actual active-form gradients. -/
def historicalRationalTangentDirectionCertificateAt?
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (t : ℚ) :
    Option (TangentDirection (historicalActiveOwnerForms selected)
      ((selectedCompletePath selected).value t)) :=
  rationalTangentDirectionCertificate?
    (historicalActiveOwnerForms selected) ((selectedCompletePath selected).value t)

/-- The dynamic historical search is complete for every inhabited rational
strict tangent cone. -/
theorem historicalRationalTangentDirectionCertificateAt?_isSome_of_exists
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (t : ℚ)
    (existsDirection : ∃ direction : QI,
      ∀ form ∈ historicalActiveOwnerForms selected,
        0 < directionalSlope form ((selectedCompletePath selected).value t)
          direction) :
    (historicalRationalTangentDirectionCertificateAt? selected t).isSome := by
  exact rationalTangentDirectionCertificate?_isSome_of_exists
    (historicalActiveOwnerForms selected) ((selectedCompletePath selected).value t)
    existsDirection

/-- Every successful fixed-compass classification is also accepted by the
complete dynamic solver at each point of its final sign interval. -/
theorem historicalRationalTangentDirectionCertificateAt?_isSome_of_classified
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : historicalClassifiedTangentDirection? selected = some direction)
    (t : ℚ)
    (lower : (historicalSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (historicalSlopeSigns selected).refined.interval.upper) :
    (historicalRationalTangentDirectionCertificateAt? selected t).isSome := by
  apply historicalRationalTangentDirectionCertificateAt?_isSome_of_exists
  exact ⟨direction,
    (historicalClassifiedTangentDirectionAt search t lower upper).slopes⟩

/-- Failure of the exact solver is a genuine finite-cone obstruction: every
rational direction violates some active owner half-plane. -/
theorem historicalRationalTangentDirectionCertificateAt?_eq_none_violates_each_direction
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (t : ℚ)
    (failure :
      historicalRationalTangentDirectionCertificateAt? selected t = none) :
    ∀ direction : QI,
      ∃ form ∈ historicalActiveOwnerForms selected,
        directionalSlope form ((selectedCompletePath selected).value t) direction ≤ 0 := by
  intro direction
  by_contra noViolation
  have allPositive : ∀ form ∈ historicalActiveOwnerForms selected,
      0 < directionalSlope form ((selectedCompletePath selected).value t)
        direction := by
    intro form formMember
    apply lt_of_not_ge
    intro nonpositive
    exact noViolation ⟨form, formMember, nonpositive⟩
  have succeeds :=
    historicalRationalTangentDirectionCertificateAt?_isSome_of_exists
      selected t ⟨direction, allPositive⟩
  rw [failure] at succeeds
  simp at succeeds

/-- A successful crossing-side search is itself a successful complete-formula
path search once canonical reachability is supplied. -/
theorem historicalPathParameter?_isSome_of_crossingParameter?_eq_some
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    {t : ℚ} (crossingSearch :
      historicalCrossingParameter? selected = some t) :
    (historicalPathParameter? selected).isSome := by
  have member := List.mem_of_find?_eq_some crossingSearch
  have bounds := historicalPathParameters_bounds selected member
  have denominator := historicalPathParameters_denominator_ne selected member
  have holds := historicalOwnerFormula_holds_of_path_partition current
    separation selected squarefree degreeNonzero elimination valid t
    denominator
    ((historicalCrossingsNonnegative?_eq_true_iff selected t).1
      (List.find?_some crossingSearch))
    (historicalStrictPriorForms_mul_eval_pos selected bounds.1 bounds.2)
  rw [historicalPathParameter?, List.find?_isSome]
  refine ⟨t, member, ?_⟩
  exact (pathEvalBool_eq_true_iff
    (historicalOwnerFormula (RawParser.parse current.word) selected.bit)
    (selectedCompletePath selected) t denominator).2 holds

/-- Under canonical reachability, failure of the complete-formula side search
forces failure of the sufficient crossing-only search as well. -/
theorem historicalCrossingParameter?_eq_none_of_pathParameter?_eq_none
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    (failure : historicalPathParameter? selected = none) :
    historicalCrossingParameter? selected = none := by
  cases crossingSearch : historicalCrossingParameter? selected with
  | none => rfl
  | some parameter =>
      have succeeds :=
        historicalPathParameter?_isSome_of_crossingParameter?_eq_some
          current separation selected squarefree degreeNonzero elimination
          valid crossingSearch
      rw [failure] at succeeds
      simp at succeeds

/-- Direct semantic correctness of the crossing-side parameter returned by
the finite search. -/
theorem historicalCrossingParameter?_some_holds
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    {t : ℚ} (crossingSearch :
      historicalCrossingParameter? selected = some t) :
    (historicalOwnerFormula (RawParser.parse current.word)
      selected.bit).Holds ((selectedCompletePath selected).value t) := by
  have member := List.mem_of_find?_eq_some crossingSearch
  have bounds := historicalPathParameters_bounds selected member
  apply historicalOwnerFormula_holds_of_path_partition current separation
    selected squarefree degreeNonzero elimination valid t
    (historicalPathParameters_denominator_ne selected member)
  · exact (historicalCrossingsNonnegative?_eq_true_iff selected t).1
      (List.find?_some crossingSearch)
  · exact historicalStrictPriorForms_mul_eval_pos selected bounds.1 bounds.2

/-- If either displayed endpoint places every genuine crossing face on its
weak owner side, the finite endpoint search succeeds.  Equality faces,
strict prior signs, and the path denominator are all discharged internally. -/
theorem historicalPathParameter?_isSome_of_crossing_nonnegative
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    {t : ℚ} (member : t ∈ historicalPathParameters selected)
    (crossingNonnegative :
      ∀ form ∈ historicalPathCrossingForms selected,
        0 ≤ form.eval ((selectedCompletePath selected).value t)) :
    (historicalPathParameter? selected).isSome := by
  have bounds := historicalPathParameters_bounds selected member
  have denominator := historicalPathParameters_denominator_ne selected member
  have holds := historicalOwnerFormula_holds_of_path_partition current
    separation selected squarefree degreeNonzero elimination valid t
    denominator crossingNonnegative
    (historicalStrictPriorForms_mul_eval_pos selected bounds.1 bounds.2)
  rw [historicalPathParameter?, List.find?_isSome]
  refine ⟨t, member, ?_⟩
  exact (pathEvalBool_eq_true_iff
    (historicalOwnerFormula (RawParser.parse current.word) selected.bit)
    (selectedCompletePath selected) t denominator).2 holds

/-- A purely lower-dimensional event, with every active historical face
identically zero on the source path, is closed unconditionally by the finite
endpoint search. -/
theorem historicalPathParameter?_isSome_of_crossingForms_eq_nil
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    (noCrossings : historicalPathCrossingForms selected = []) :
    (historicalPathParameter? selected).isSome := by
  apply historicalPathParameter?_isSome_of_crossing_nonnegative current
    separation selected squarefree degreeNonzero elimination valid
    (t := (historicalSlopeSigns selected).refined.interval.lower)
  · simp [historicalPathParameters]
  · simp [noCrossings]

/-- Complete finite evidence exposed when neither a rational path endpoint
nor one of the classified strict tangent directions closes the historical
owner.  This record turns the residual branch into explicit geometry: there
is a genuine path crossing, at least two active faces, both path endpoints
fail the complete formula, and every displayed compass direction violates an
active half-plane. -/
structure HistoricalFormulaConeObstruction
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation) : Prop where
  pathFailure : historicalPathParameter? selected = none
  tangentFailure : historicalClassifiedTangentDirection? selected = none
  crossingFailure : historicalCrossingParameter? selected = none
  crossings_ne_nil : historicalPathCrossingForms selected ≠ []
  active_length_ge_two : 2 ≤ (historicalActiveOwnerForms selected).length
  endpointFails : ∀ t ∈ historicalPathParameters selected,
    ¬(historicalOwnerFormula (RawParser.parse current.word)
      selected.bit).Holds ((selectedCompletePath selected).value t)
  directionViolated : ∀ direction : QI,
    direction ∈ CCLMultiOwnerGrid.coordinateDirections →
      ∃ form ∈ historicalActiveOwnerForms selected,
        historicalSlopeValue selected form direction ≤ 0

/-- Assemble the full obstruction record from the two executable failed
searches.  Canonical reachability is used only to show that failure of the
complete path formula also rules out the sufficient crossing-only test. -/
theorem historicalFormulaConeObstructionOfFailures
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    (pathFailure : historicalPathParameter? selected = none)
    (tangentFailure :
      historicalClassifiedTangentDirection? selected = none) :
    HistoricalFormulaConeObstruction current separation selected := by
  let crossingFailure :=
    historicalCrossingParameter?_eq_none_of_pathParameter?_eq_none current
      separation selected squarefree degreeNonzero elimination valid
        pathFailure
  exact
    { pathFailure := pathFailure
      tangentFailure := tangentFailure
      crossingFailure := crossingFailure
      crossings_ne_nil :=
        historicalOwnerSamplingPlan_obstructed_crossings_ne_nil selected
          crossingFailure
      active_length_ge_two :=
        historicalOwnerSamplingPlan_obstructed_active_length_ge_two current
          separation selected squarefree degreeNonzero elimination valid
            tangentFailure
      endpointFails :=
        historicalPathParameter?_eq_none_fails_each_endpoint selected
          pathFailure
      directionViolated :=
        historicalClassifiedTangentDirection?_eq_none_violates_each_direction
          selected tangentFailure }

/-! ## Localized boundary samples -/

/-- Repackage the final historical slope descendant as an ordinary input
event cell.  Its child-formula relations are inherited by exact divisor
restriction, while its parent is the fully classified common-sign interval. -/
def historicalSlopeInputCell
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    InputEventCell state selected.candidate.sourceEvent.event :=
  let classification := historicalSlopeClassification selected
  { branch :=
      { factor := classification.branch.factor
        relations := (historicalInputCell selected).branch.relations.ofDvd
          classification.branch.factor.input classification.divides }
    divides := classification.divides.trans
      (historicalInputCell selected).divides
    parent := (historicalSlopeSigns selected).refined
    refines := FTA.SturmTransducer.RationalInterval.refines_trans
      (historicalSlopeSigns_refines_inputCell selected)
      (historicalInputCell selected).signRefines }

private def localizedEventParameter
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) : ℚ :=
  (cell.clearedApproximation
    (eventSourceApproximationWidth cell squarefree clearance)
    (eventSourceApproximationWidth_pos cell squarefree clearance)).refined.interval.lower

private theorem localizedEventParameter_bounds
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    (cell.branch.computeEventSigns cell.parent).refined.interval.lower ≤
        localizedEventParameter cell squarefree clearance ∧
      localizedEventParameter cell squarefree clearance ≤
        (cell.branch.computeEventSigns cell.parent).refined.interval.upper := by
  let approximation := cell.clearedApproximation
    (eventSourceApproximationWidth cell squarefree clearance)
    (eventSourceApproximationWidth_pos cell squarefree clearance)
  exact ⟨approximation.refines.1,
    approximation.refined.proper.le.trans approximation.refines.2⟩

private theorem localizedEventParameter_denominator_ne
    {p : GaussianPolynomial} {path : Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box) :
    path.denominator.eval (PathPolynomial.ofRat
      (localizedEventParameter cell squarefree clearance)) ≠ 0 := by
  simpa only [localizedEventParameter] using
    eventSourcePoint_pathDenominator_ne cell squarefree clearance

/-- Parameter of the standard shrinking event point, now based at the final
historical slope cell. -/
def historicalBoundaryParameter
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) : ℚ :=
  localizedEventParameter (historicalSlopeInputCell selected) squarefree
    (shrinkingEventClearance output radius radiusPositive)

/-- The localized rational point on the selected source boundary. -/
def historicalBoundaryPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) : QI :=
  (selectedCompletePath selected).value
    (historicalBoundaryParameter selected squarefree radius radiusPositive)

/-- The ordinary shrinking winding-one extraction centered at that boundary
point. -/
def historicalBoundaryState
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    WindingOneState p ambient :=
  shrinkingInputEventState (historicalSlopeInputCell selected) squarefree
    elimination radius radiusPositive

theorem historicalBoundaryPoint_eq_shrinkingInputEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    historicalBoundaryPoint selected squarefree radius radiusPositive =
      shrinkingInputEventPoint (historicalSlopeInputCell selected) squarefree
        radius radiusPositive := by
  rfl

/-- The localized boundary parameter remains in the final historical
common-sign interval. -/
theorem historicalBoundaryParameter_bounds
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (historicalSlopeSigns selected).refined.interval.lower ≤
        historicalBoundaryParameter selected squarefree radius
          radiusPositive ∧
      historicalBoundaryParameter selected squarefree radius radiusPositive ≤
        (historicalSlopeSigns selected).refined.interval.upper := by
  let cell := historicalSlopeInputCell selected
  let clearance := shrinkingEventClearance output radius radiusPositive
  let signs := cell.branch.computeEventSigns cell.parent
  have bounds := localizedEventParameter_bounds cell squarefree clearance
  have lower : (historicalSlopeSigns selected).refined.interval.lower ≤
      localizedEventParameter cell squarefree clearance :=
    signs.refines.1.trans bounds.1
  have upper : localizedEventParameter cell squarefree clearance ≤
      (historicalSlopeSigns selected).refined.interval.upper :=
    bounds.2.trans signs.refines.2
  simpa only [historicalBoundaryParameter, cell, clearance] using
    And.intro lower upper

/-- The localized boundary parameter is affine. -/
theorem historicalBoundaryParameter_denominator_ne
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (selectedCompletePath selected).denominator.eval (PathPolynomial.ofRat
      (historicalBoundaryParameter selected squarefree radius
        radiusPositive)) ≠ 0 := by
  exact localizedEventParameter_denominator_ne
    (historicalSlopeInputCell selected) squarefree
      (shrinkingEventClearance output radius radiusPositive)

/-- The extracted winding-one box contains its rational boundary sample. -/
theorem historicalBoundaryState_contains_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (historicalBoundaryState selected squarefree elimination radius
      radiusPositive).box.Contains
        (historicalBoundaryPoint selected squarefree radius radiusPositive) := by
  rw [historicalBoundaryPoint_eq_shrinkingInputEventPoint]
  exact shrinkingInputEventState_contains_point
    (historicalSlopeInputCell selected) squarefree elimination radius
      radiusPositive

/-- The localized historical state is strictly nested in, hence refines, the
denominator-separated owner box. -/
theorem historicalBoundaryState_refines_separation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (historicalBoundaryState selected squarefree elimination radius
      radiusPositive).box.Refines output.state.box := by
  exact (eventWindingOneState_strictInterior output.state.refinesAmbient
    (historicalSlopeInputCell selected) squarefree
    (shrinkingEventClearance output radius radiusPositive)
    elimination).refines

/-- With no genuine path crossings, every shrinking boundary sample realizes
the complete historical conjunction.  Thus the lower-dimensional branch is
compatible with arbitrarily small extracted winding-one boxes, not only with
one fixed endpoint. -/
theorem historicalBoundaryPoint_holds_of_crossingForms_eq_nil
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    (noCrossings : historicalPathCrossingForms selected = [])
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (historicalOwnerFormula (RawParser.parse current.word) selected.bit).Holds
      (historicalBoundaryPoint selected squarefree radius radiusPositive) := by
  let t := historicalBoundaryParameter selected squarefree radius
    radiusPositive
  have bounds := historicalBoundaryParameter_bounds selected squarefree
    radius radiusPositive
  apply historicalOwnerFormula_holds_of_path_partition current separation
    selected squarefree degreeNonzero elimination valid t
    (historicalBoundaryParameter_denominator_ne selected squarefree radius
      radiusPositive)
  · simp [noCrossings]
  · simpa only [historicalBoundaryPoint, t] using
      historicalStrictPriorForms_mul_eval_pos selected bounds.1 bounds.2

/-- The same lower-dimensional sample has the exact raw-parser semantics of
the extended word.  This proof reconstructs the old representation from the
complete historical formula, so it does not rely on an open strict-prior
neighbourhood. -/
theorem historicalBoundaryPoint_represented_append_of_crossingForms_eq_nil
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    (noCrossings : historicalPathCrossingForms selected = [])
    (radius : ℚ) (radiusPositive : 0 < radius) :
    RawParserSemantics.Represented (current.word ++ [selected.bit])
      (historicalBoundaryPoint selected squarefree radius radiusPositive) := by
  let point := historicalBoundaryPoint selected squarefree radius
    radiusPositive
  have complete := historicalBoundaryPoint_holds_of_crossingForms_eq_nil
    current separation selected squarefree degreeNonzero elimination valid
    noCrossings radius radiusPositive
  have components :
      (inputStateFormula (RawParser.parse current.word)).Holds point ∧
        (inputAdvanceFormula (RawParser.parse current.word)
          selected.bit).Holds point := by
    simpa only [historicalOwnerFormula, Formula.Holds, point] using complete
  have insideState := historicalBoundaryState_contains_point selected
    squarefree elimination radius radiusPositive
  have insideSeparation : separation.state.box.Contains point :=
    (historicalBoundaryState_refines_separation selected squarefree
      elimination radius radiusPositive).contains insideState
  have inverseDenominator :=
    CCLBranchEvidence.separation_denominator_ne separation insideSeparation
  have representedCurrent : RawParserSemantics.Represented current.word point :=
    represented_of_inputStateFormula current.word point inverseDenominator
      components.1
  have extended :=
    CCLBranchSampling.represented_append_of_inputFormula current.word
      point selected.bit inverseDenominator representedCurrent components.2
  simpa only [point] using extended

end CCLBoundaryPreservingOwner
end FTA
