import FTA.SturmTransducer

/-!
# Finite one-dimensional Sturm isolation

This module extracts the first-member leaves of the executable event
partition as a finite list of count-one interval transducers.  The extraction
preserves the exact doubled Sturm count, the parent-refinement relation, and
the left-to-right order imposed by the partition tree.  Thus the local
classifier program becomes the finite isolation-list interface used after
Theorem 3.2(d).
-/

namespace FTA.SturmIsolation

open FTA.ComputablePolynomial
open ComputablePolynomial.DensePolynomial
open FTA.Sturm
open FTA.SturmTransducer

abbrev RatPolynomial := DensePolynomial ℚ

/-- Extract precisely the first-member leaves of a finite event partition. -/
def zeroTransducers {p : RatPolynomial} :
    (interval : RationalInterval) → EventPartition p interval →
      List (CountOneInterval p)
  | _, .leaf _ _ _ .interior _ => []
  | interval, .leaf proper lowerClear upperClear .firstMember countCertificate =>
      [{ interval
         proper
         countOne := by
           simpa [EventKind.contribution2] using countCertificate
         lowerClear
         upperClear }]
  | _, .split _ _ _ _ left right =>
      zeroTransducers _ left ++ zeroTransducers _ right

@[simp] theorem zeroTransducers_length {p : RatPolynomial}
    {interval : RationalInterval} (partition : EventPartition p interval) :
    (zeroTransducers interval partition).length = partition.firstMemberCount := by
  induction partition with
  | leaf proper lowerClear upperClear kind countCertificate =>
      cases kind <;> rfl
  | split cut lowerLt ltUpper cutClear left right leftIH rightIH =>
      simp [zeroTransducers, EventPartition.firstMemberCount, leftIH, rightIH]

/-- Every extracted count-one interval is nested in the partition root. -/
theorem zeroTransducers_refine {p : RatPolynomial}
    {interval : RationalInterval} (partition : EventPartition p interval) :
    ∀ child ∈ zeroTransducers interval partition,
      child.interval.Refines interval := by
  induction partition with
  | leaf proper lowerClear upperClear kind countCertificate =>
      cases kind
      · simp [zeroTransducers]
      · intro child hchild
        simp only [zeroTransducers, List.mem_singleton] at hchild
        subst child
        exact RationalInterval.refines_refl _
  | @split partitionInterval cut lowerLt ltUpper cutClear left right leftIH rightIH =>
      intro child hchild
      rw [zeroTransducers, List.mem_append] at hchild
      rcases hchild with hleft | hright
      · exact RationalInterval.refines_trans (leftIH child hleft)
          ⟨le_rfl, ltUpper.le⟩
      · exact RationalInterval.refines_trans (rightIH child hright)
          ⟨lowerLt.le, le_rfl⟩

/-- The weak left-to-right separation relation carried by a partition tree. -/
def Before {p : RatPolynomial} (left right : CountOneInterval p) : Prop :=
  left.interval.upper ≤ right.interval.lower

theorem before_ne {p : RatPolynomial} {left right : CountOneInterval p}
    (hbefore : Before left right) : left ≠ right := by
  intro heq
  subst right
  exact (not_le_of_gt left.proper) hbefore

/-- Extracted leaves occur in interval order and have disjoint interiors. -/
theorem zeroTransducers_pairwise_before {p : RatPolynomial}
    {interval : RationalInterval} (partition : EventPartition p interval) :
    (zeroTransducers interval partition).Pairwise Before := by
  induction partition with
  | leaf proper lowerClear upperClear kind countCertificate =>
      cases kind <;> simp [zeroTransducers]
  | @split partitionInterval cut lowerLt ltUpper cutClear left right leftIH rightIH =>
      rw [zeroTransducers, List.pairwise_append]
      refine ⟨leftIH, rightIH, ?_⟩
      intro leftChild hleft rightChild hright
      have hleftRefines := zeroTransducers_refine left leftChild hleft
      have hrightRefines := zeroTransducers_refine right rightChild hright
      exact hleftRefines.2.trans hrightRefines.1

/-- In particular, the extracted finite list contains no duplicate
transducer records. -/
theorem zeroTransducers_nodup {p : RatPolynomial}
    {interval : RationalInterval} (partition : EventPartition p interval) :
    (zeroTransducers interval partition).Nodup := by
  exact (zeroTransducers_pairwise_before partition).imp
    (fun hbefore => before_ne hbefore)

/-- Proof-bearing finite output of one-dimensional squarefree isolation. -/
structure IsolationResult (p : RatPolynomial) (root : RationalInterval) where
  partition : EventPartition p root
  transducers : List (CountOneInterval p)
  extracted : transducers = zeroTransducers root partition
  refine : ∀ child ∈ transducers, child.interval.Refines root
  ordered : transducers.Pairwise Before
  nodup : transducers.Nodup
  exactCount : sturmRootCount2 p root.lower root.upper =
    2 * (transducers.length : ℤ)

/-- Every finite event partition canonically yields its exact isolation
result. -/
def isolationResultOfPartition {p : RatPolynomial}
    {root : RationalInterval} (partition : EventPartition p root) :
    IsolationResult p root where
  partition := partition
  transducers := zeroTransducers root partition
  extracted := rfl
  refine := zeroTransducers_refine partition
  ordered := zeroTransducers_pairwise_before partition
  nodup := zeroTransducers_nodup partition
  exactCount := by
    rw [partition.count_eq_two_mul_firstMemberCount,
      zeroTransducers_length]

/-- The canonical squarefree event-partition program therefore returns a
finite exact isolation list on every proper interval with clear endpoints. -/
def isolate {p : RatPolynomial} (input : SquarefreeInput p)
    (a b : ℚ) (proper : a < b) (lowerClear : p.eval a ≠ 0)
    (upperClear : p.eval b ≠ 0) : IsolationResult p ⟨a, b⟩ :=
  isolationResultOfPartition
    ((computedEventPartitionProgram input).run a b proper lowerClear upperClear)

/-- A zero parent count forces the executable isolation list to be empty. -/
theorem IsolationResult.eq_nil_of_count_eq_zero {p : RatPolynomial}
    {root : RationalInterval} (result : IsolationResult p root)
    (hcount : sturmRootCount2 p root.lower root.upper = 0) :
    result.transducers = [] := by
  have h := result.exactCount
  rw [hcount] at h
  norm_num at h
  exact h

/-- The doubled parent count is nonnegative because it is twice the length of
the returned finite list. -/
theorem IsolationResult.count_nonnegative {p : RatPolynomial}
    {root : RationalInterval} (result : IsolationResult p root) :
    0 ≤ sturmRootCount2 p root.lower root.upper := by
  rw [result.exactCount]
  positivity

/-! ## Quantitative finite separation -/

/-- Root-dependent positive width used to separate every pair of count-one
transducers after finite refinement. -/
def separationWidth {p : RatPolynomial} (input : SquarefreeInput p)
    (root : RationalInterval) : ℚ :=
  (computedEventClassifierResolution input root).threshold / 3

theorem separationWidth_pos {p : RatPolynomial} (input : SquarefreeInput p)
    (root : RationalInterval) : 0 < separationWidth input root := by
  exact div_pos (computedEventClassifierResolution input root).positive (by norm_num)

theorem three_mul_separationWidth_le_resolution {p : RatPolynomial}
    (input : SquarefreeInput p) (root : RationalInterval) :
    3 * separationWidth input root ≤
      (computedEventClassifierResolution input root).threshold := by
  dsimp [separationWidth]
  linarith

/-- Two ordered count-one intervals nested in one root must span at least the
computed local-classifier threshold.  Otherwise their union would be one
locally classified `0/2` leaf while additivity and nonnegativity force count
at least four. -/
theorem countOne_span_ge_resolution {p : RatPolynomial}
    (input : SquarefreeInput p) (root : RationalInterval)
    {left right : CountOneInterval p}
    (leftRefines : left.interval.Refines root)
    (rightRefines : right.interval.Refines root)
    (before : Before left right) :
    (computedEventClassifierResolution input root).threshold ≤
      right.interval.upper - left.interval.lower := by
  apply le_of_not_gt
  intro hspan
  let union : RationalInterval :=
    ⟨left.interval.lower, right.interval.upper⟩
  have unionProper : union.Proper := by
    dsimp only [union, RationalInterval.Proper]
    exact left.proper.trans_le (before.trans right.proper.le)
  have unionRefines : union.Refines root :=
    ⟨leftRefines.1, rightRefines.2⟩
  have unionWidth : union.width <
      (computedEventClassifierResolution input root).threshold := by
    simpa [union, RationalInterval.width] using hspan
  have classified := (computedEventClassifierResolution input root).classify
    union unionRefines unionProper left.lowerClear right.upperClear unionWidth
  have localCount := classifiedEventLeaf?_some_count classified.2
  have gapNonnegative :
      0 ≤ sturmRootCount2 p left.interval.upper right.interval.lower := by
    rcases lt_or_eq_of_le before with gapProper | gapEq
    · exact (computedEventPartitionProgram input).nonnegativeLaw gapProper
        left.upperClear right.lowerClear
    · rw [gapEq]
      simp
  have leftAndGap := sturmRootCount2_add p left.interval.lower
    left.interval.upper right.interval.lower
  have fullSum := sturmRootCount2_add p left.interval.lower
    right.interval.lower right.interval.upper
  change sturmRootCount2 p left.interval.lower right.interval.upper = 0 ∨
    sturmRootCount2 p left.interval.lower right.interval.upper = 2 at localCount
  rw [left.countOne] at leftAndGap
  rw [right.countOne] at fullSum
  omega

/-- Finite refinement of one count-one track to the common separation width. -/
def refineForSeparation {p : RatPolynomial} (input : SquarefreeInput p)
    (root : RationalInterval) (child : CountOneInterval p) : CountOneInterval p :=
  runToWidth input (computedEventPartitionProgram input) child
    (separationWidth input root) (separationWidth_pos input root)

theorem refineForSeparation_refines {p : RatPolynomial}
    (input : SquarefreeInput p) (root : RationalInterval)
    (child : CountOneInterval p) :
    (refineForSeparation input root child).interval.Refines child.interval :=
  runToWidth_refines input (computedEventPartitionProgram input) child
    (separationWidth input root) (separationWidth_pos input root)

theorem refineForSeparation_width_le {p : RatPolynomial}
    (input : SquarefreeInput p) (root : RationalInterval)
    (child : CountOneInterval p) :
    (refineForSeparation input root child).interval.width ≤
      separationWidth input root :=
  runToWidth_le input (computedEventPartitionProgram input) child
    (separationWidth input root) (separationWidth_pos input root)

/-- Quantitative positive-gap relation for refined count-one tracks. -/
def SeparatedBy {p : RatPolynomial} (margin : ℚ)
    (left right : CountOneInterval p) : Prop :=
  margin ≤ right.interval.lower - left.interval.upper

theorem strictlyBefore_of_separatedBy {p : RatPolynomial} {margin : ℚ}
    {left right : CountOneInterval p} (marginPos : 0 < margin)
    (separated : SeparatedBy margin left right) :
    left.interval.upper < right.interval.lower := by
  dsimp only [SeparatedBy] at separated
  linarith

/-- Refining every ordered count-one interval to one third of the local
resolution threshold gives a uniform positive gap between every later pair. -/
theorem refineList_pairwise_separated {p : RatPolynomial}
    (input : SquarefreeInput p) (root : RationalInterval)
    (transducers : List (CountOneInterval p))
    (refines : ∀ child ∈ transducers, child.interval.Refines root)
    (ordered : transducers.Pairwise Before) :
    (transducers.map (refineForSeparation input root)).Pairwise
      (SeparatedBy (separationWidth input root)) := by
  rw [List.pairwise_map]
  induction transducers with
  | nil => exact .nil
  | cons head tail ih =>
      rw [List.pairwise_cons] at ordered ⊢
      refine ⟨?_, ih (fun child hchild =>
        refines child (List.mem_cons_of_mem head hchild)) ordered.2⟩
      intro right hright
      have headRoot := refines head (List.mem_cons_self)
      have rightRoot := refines right (List.mem_cons_of_mem head hright)
      have refinedHeadRoot := RationalInterval.refines_trans
        (refineForSeparation_refines input root head) headRoot
      have refinedRightRoot := RationalInterval.refines_trans
        (refineForSeparation_refines input root right) rightRoot
      have refinedBefore : Before (refineForSeparation input root head)
          (refineForSeparation input root right) := by
        exact (refineForSeparation_refines input root head).2.trans
          ((ordered.1 right hright).trans
            (refineForSeparation_refines input root right).1)
      have hspan := countOne_span_ge_resolution input root
        refinedHeadRoot refinedRightRoot refinedBefore
      have hleftWidth := refineForSeparation_width_le input root head
      have hrightWidth := refineForSeparation_width_le input root right
      have hthreshold := three_mul_separationWidth_le_resolution input root
      dsimp only [SeparatedBy]
      dsimp only [RationalInterval.width] at hleftWidth hrightWidth
      nlinarith

/-- Fully separated finite output of constructive Sturm isolation. -/
structure SeparatedIsolationResult {p : RatPolynomial}
    (input : SquarefreeInput p) (root : RationalInterval) where
  transducers : List (CountOneInterval p)
  refine : ∀ child ∈ transducers, child.interval.Refines root
  separated : transducers.Pairwise (SeparatedBy (separationWidth input root))
  nodup : transducers.Nodup
  exactCount : sturmRootCount2 p root.lower root.upper =
    2 * (transducers.length : ℤ)

/-- A finite common-width refinement turns an exact isolation result into a
quantitatively separated one without changing its cardinality. -/
def IsolationResult.separate {p : RatPolynomial} {root : RationalInterval}
    (input : SquarefreeInput p) (result : IsolationResult p root) :
    SeparatedIsolationResult input root := by
  let refined := result.transducers.map (refineForSeparation input root)
  have hrefine : ∀ child ∈ refined, child.interval.Refines root := by
    intro child hchild
    rcases List.mem_map.mp hchild with ⟨parent, hparent, rfl⟩
    exact RationalInterval.refines_trans
      (refineForSeparation_refines input root parent)
      (result.refine parent hparent)
  have hseparated : refined.Pairwise
      (SeparatedBy (separationWidth input root)) :=
    refineList_pairwise_separated input root result.transducers
      result.refine result.ordered
  refine
    { transducers := refined
      refine := hrefine
      separated := hseparated
      nodup := ?_
      exactCount := ?_ }
  · exact hseparated.imp (fun hgap => by
      apply before_ne
      have hpositive := separationWidth_pos input root
      dsimp only [SeparatedBy] at hgap
      dsimp only [Before]
      linarith)
  · simpa [refined] using result.exactCount

/-- The canonical one-dimensional isolation algorithm with finite positive
gaps between all returned count-one transducers. -/
def isolateSeparated {p : RatPolynomial} (input : SquarefreeInput p)
    (a b : ℚ) (proper : a < b) (lowerClear : p.eval a ≠ 0)
    (upperClear : p.eval b ≠ 0) : SeparatedIsolationResult input ⟨a, b⟩ :=
  (isolate input a b proper lowerClear upperClear).separate input

private def quadraticPolynomial : RatPolynomial := ⟨[1, 0, -1]⟩

private def quadraticInput : SquarefreeInput quadraticPolynomial where
  nonzero := by native_decide
  nonconstant := by native_decide
  squarefree :=
    { left := ⟨[-1]⟩
      right := ⟨[1 / 2, 0]⟩
      polynomialIdentity := by
        rw [show FTA.DenseDerivative.derivative quadraticPolynomial =
          ⟨[2, 0]⟩ by native_decide]
        simp [quadraticPolynomial, toPolynomial_eq_foldl_horner]
        have hhalf : Polynomial.C ((2 : ℚ)⁻¹) * Polynomial.C 2 = 1 := by
          rw [← map_mul]
          norm_num
        rw [show Polynomial.C ((2 : ℚ)⁻¹) * Polynomial.X *
            (Polynomial.C 2 * Polynomial.X) =
          (Polynomial.C ((2 : ℚ)⁻¹) * Polynomial.C 2) *
            (Polynomial.X * Polynomial.X) by ac_rfl]
        rw [hhalf, one_mul, neg_add_cancel_right] }

/-- End-to-end cardinality regression: the canonical separated isolation of
`T² - 1` on `[-2,2]` returns exactly two count-one transducers. -/
theorem isolateSeparated_quadratic_length_example :
    (isolateSeparated quadraticInput (-2) 2 (by norm_num)
      (by native_decide) (by native_decide)).transducers.length = 2 := by
  let result := isolateSeparated quadraticInput (-2) 2 (by norm_num)
    (by native_decide) (by native_decide)
  have hcount : sturmRootCount2 quadraticPolynomial (-2) 2 = 4 := by
    native_decide
  have hexact := result.exactCount
  rw [hcount] at hexact
  change result.transducers.length = 2
  omega

end FTA.SturmIsolation
