import FTA.CCLIntersectionGuard
import FTA.Maximality

/-!
# Common finite parameter partitions for CCL intersection signs

The squarefree factors of the simultaneous box-condition guard must be
classified on one common rational subdivision.  This module builds the shared
derivative-chain guard and its bounded central-third cut, then runs every
factor's executable local Sturm classifier on the same cell.  The common
fuel-recursive partition and its computed success depth complete the merge of
the per-factor plans from `CCLIntersectionGuard`.
-/

namespace FTA
namespace CCLIntersectionPartition

open FTA.ComputablePolynomial
open FTA.ComputablePolynomial.DensePolynomial
open FTA.CauchyProduct
open FTA.SafeCandidates
open FTA.SquarefreeFactorization
open FTA.Sturm
open FTA.SturmTransducer
open FTA.CCLIntersectionGuard

abbrev RatPolynomial := DensePolynomial ℚ
abbrev RationalInterval := FTA.SturmTransducer.RationalInterval

/-- Every polynomial whose vanishing can affect one factor's local Sturm
classifier. -/
def factorEventPolynomials (factors : List Factor) : List RatPolynomial :=
  factors.flatMap fun factor => derivativeChain factor.polynomial

/-- One nonzero simultaneous guard for all factor derivative chains. -/
def factorEventGuard (factors : List Factor) : RatPolynomial :=
  nonzeroPolynomialProduct (factorEventPolynomials factors)

theorem factorEventGuard_isZero_false (factors : List Factor) :
    (factorEventGuard factors).isZero = false :=
  nonzeroPolynomialProduct_isZero_false _

theorem factor_polynomial_mem_events
    {factors : List Factor} {factor : Factor} (member : factor ∈ factors) :
    factor.polynomial ∈ factorEventPolynomials factors := by
  rw [factorEventPolynomials, List.mem_flatMap]
  exact ⟨factor, member, by simp [derivativeChain]⟩

theorem factor_eval_ne_zero_of_eventGuard
    {factors : List Factor} {factor : Factor} {t : ℚ}
    (member : factor ∈ factors)
    (guardClear : (factorEventGuard factors).eval t ≠ 0) :
    factor.polynomial.eval t ≠ 0 := by
  exact eval_ne_zero_of_mem_nonzeroPolynomialProduct
    (factor_polynomial_mem_events member) factor.input.nonzero guardClear

theorem factorProduct_eval_ne_zero_of_eventGuard
    {factors : List Factor} {t : ℚ}
    (guardClear : (factorEventGuard factors).eval t ≠ 0) :
    (factorProduct factors).eval t ≠ 0 := by
  rw [factorProduct_eval]
  apply List.prod_ne_zero
  intro zeroMember
  rw [List.mem_map] at zeroMember
  rcases zeroMember with ⟨factor, member, evaluationZero⟩
  exact factor_eval_ne_zero_of_eventGuard member guardClear evaluationZero

def factorEventCut? (factors : List Factor) (a b : ℚ) : Option ℚ :=
  centralSearch (factorEventGuard factors) a b
    (factorEventGuard factors).natDegree

def factorEventCut (factors : List Factor) (a b : ℚ) : ℚ :=
  (factorEventCut? factors a b).getD ((a + b) / 2)

theorem factorEventCut_search_succeeds
    (factors : List Factor) {a b : ℚ} (proper : a < b) :
    ∃ cut, factorEventCut? factors a b = some cut := by
  apply centralSearch_succeeds (factorEventGuard factors)
    (factorEventGuard factors).natDegree proper
    (toPolynomial_ne_zero_of_isZero_false
      (factorEventGuard_isZero_false factors))
  rw [natDegree_toPolynomial (factorEventGuard_isZero_false factors)]

theorem factorEventCut_spec
    (factors : List Factor) {a b : ℚ} (proper : a < b) :
    (factorEventGuard factors).eval (factorEventCut factors a b) ≠ 0 ∧
      centralLeft a b < factorEventCut factors a b ∧
      factorEventCut factors a b < centralRight a b := by
  rcases factorEventCut_search_succeeds factors proper with ⟨cut, search⟩
  rcases centralSearch_some_spec proper search with
    ⟨_member, clear, left, right⟩
  have value : factorEventCut factors a b = cut := by
    simp [factorEventCut, search]
  rw [value]
  exact ⟨clear, left, right⟩

theorem factorEventCut_geometry
    (factors : List Factor) {a b : ℚ} (proper : a < b) :
    a < factorEventCut factors a b ∧
      factorEventCut factors a b < b ∧
      factorEventCut factors a b - a < (2 / 3 : ℚ) * (b - a) ∧
      b - factorEventCut factors a b < (2 / 3 : ℚ) * (b - a) := by
  rcases factorEventCut_spec factors proper with ⟨_clear, left, right⟩
  dsimp [centralLeft, centralRight] at left right
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-! ## One common local classifier -/

/-- One factor's exact local `0/2` classification on the shared cell. -/
structure LocalFactorLeaf (factor : Factor) (interval : RationalInterval) where
  proper : interval.Proper
  lowerClear : factor.polynomial.eval interval.lower ≠ 0
  upperClear : factor.polynomial.eval interval.upper ≠ 0
  kind : EventKind
  countCertificate :
    sturmRootCount2 factor.polynomial interval.lower interval.upper =
      kind.contribution2

/-- Exact local leaves for every factor, all on the same rational cell. -/
inductive LocalFactorLeaves (interval : RationalInterval) : List Factor → Type
  | nil : LocalFactorLeaves interval []
  | cons {factor : Factor} {factors : List Factor}
      (head : LocalFactorLeaf factor interval)
      (tail : LocalFactorLeaves interval factors) :
      LocalFactorLeaves interval (factor :: factors)

/-- One aligned factor together with its exact local count-one interval. -/
structure FactorCountOneInterval (factors : List Factor) where
  factor : Factor
  member : factor ∈ factors
  root : CountOneInterval factor.polynomial

/-- Retain membership when a new factor is prepended to the aligned family. -/
def FactorCountOneInterval.prepend
    (head : Factor) {factors : List Factor}
    (entry : FactorCountOneInterval factors) :
    FactorCountOneInterval (head :: factors) :=
  { factor := entry.factor
    member := List.mem_cons_of_mem head entry.member
    root := entry.root }

/-- Infer the prepended factor from an aligned head leaf. -/
def FactorCountOneInterval.prependForLeaf
    {interval : RationalInterval} {head : Factor} {factors : List Factor}
    (_headLeaf : LocalFactorLeaf head interval)
    (entry : FactorCountOneInterval factors) :
    FactorCountOneInterval (head :: factors) :=
  entry.prepend head

/-- A first-member leaf is already the standard count-one interval record. -/
def LocalFactorLeaf.countOneInterval
    {factor : Factor} {interval : RationalInterval}
    (leaf : LocalFactorLeaf factor interval)
    (firstMember : leaf.kind = .firstMember) :
    CountOneInterval factor.polynomial :=
  { interval := interval
    proper := leaf.proper
    countOne := by
      simpa [firstMember, EventKind.contribution2] using leaf.countCertificate
    lowerClear := leaf.lowerClear
    upperClear := leaf.upperClear }

/-- Executable test that every factor has zero local root count. -/
def LocalFactorLeaves.allInterior
    {interval : RationalInterval} :
    {factors : List Factor} → LocalFactorLeaves interval factors → Bool
  | [], .nil => true
  | _ :: _, .cons head tail =>
      match head.kind with
      | .interior => tail.allInterior
      | .firstMember => false

/-- Executable list of every aligned factor carrying a local real event. -/
def LocalFactorLeaves.eventIntervals
    {interval : RationalInterval} :
    {factors : List Factor} →
      (leaves : LocalFactorLeaves interval factors) →
        List (FactorCountOneInterval factors)
  | [], .nil => []
  | factor :: factors, .cons head tail =>
      let tailEvents := tail.eventIntervals.map fun entry =>
        entry.prepend factor
      match kindEquation : head.kind with
      | .interior => tailEvents
      | .firstMember =>
          { factor := factor
            member := by simp
            root := head.countOneInterval kindEquation } :: tailEvents

/-- The executable event list is nonempty exactly when the Boolean
all-interior classifier fails. -/
theorem LocalFactorLeaves.eventIntervals_ne_nil_iff
    {interval : RationalInterval} {factors : List Factor}
    (leaves : LocalFactorLeaves interval factors) :
    leaves.eventIntervals ≠ [] ↔ leaves.allInterior = false := by
  induction leaves with
  | nil => simp [LocalFactorLeaves.eventIntervals,
      LocalFactorLeaves.allInterior]
  | @cons factor factors head tail inductionHypothesis =>
      rw [LocalFactorLeaves.eventIntervals]
      split
      · rename_i kindEquation
        rw [LocalFactorLeaves.allInterior, kindEquation]
        simpa using inductionHypothesis
      · rename_i kindEquation
        simp [LocalFactorLeaves.allInterior, kindEquation]

/-- Every executable event entry uses the terminal cell's exact common
interval. -/
theorem LocalFactorLeaves.eventIntervals_root_interval
    {interval : RationalInterval} {factors : List Factor}
    (leaves : LocalFactorLeaves interval factors)
    (entry : FactorCountOneInterval factors)
    (member : entry ∈ leaves.eventIntervals) :
    entry.root.interval = interval := by
  induction leaves with
  | nil => simp [LocalFactorLeaves.eventIntervals] at member
  | @cons factor factors head tail inductionHypothesis =>
      rw [LocalFactorLeaves.eventIntervals] at member
      split at member
      · rw [List.mem_map] at member
        rcases member with ⟨tailEntry, tailMember, equality⟩
        cases equality
        exact inductionHypothesis tailEntry tailMember
      · rcases List.mem_cons.mp member with headMember | tailMember
        · cases headMember
          rfl
        · rw [List.mem_map] at tailMember
          rcases tailMember with ⟨tailEntry, tailEntryMember, equality⟩
          cases equality
          exact inductionHypothesis tailEntry tailEntryMember

/-- Locate the proof-bearing local leaf for any aligned factor.  Its exact
kind either supplies the zero-count interior branch or the corresponding
entry in the executable count-one event list. -/
theorem LocalFactorLeaves.factor_leaf_or_event
    {interval : RationalInterval} {factors : List Factor}
    (leaves : LocalFactorLeaves interval factors)
    (factor : Factor) (member : factor ∈ factors) :
    ∃ leaf : LocalFactorLeaf factor interval,
      leaf.kind = .interior ∨
        ∃ entry ∈ leaves.eventIntervals, entry.factor = factor := by
  induction leaves with
  | nil => simp at member
  | @cons headFactor tailFactors head tail inductionHypothesis =>
      rcases List.mem_cons.mp member with equality | tailMember
      · cases equality
        refine ⟨head, ?_⟩
        cases kindEquation : head.kind with
        | interior => exact Or.inl rfl
        | firstMember =>
            right
            refine ⟨{ factor := factor
                      member := List.mem_cons_self
                      root := head.countOneInterval kindEquation }, ?_, rfl⟩
            rw [LocalFactorLeaves.eventIntervals]
            split
            · rename_i interiorEquation
              rw [kindEquation] at interiorEquation
              contradiction
            · exact List.mem_cons_self
      · rcases inductionHypothesis tailMember with
          ⟨leaf, interior | event⟩
        · exact ⟨leaf, Or.inl interior⟩
        · rcases event with ⟨tailEntry, tailEntryMember, factorEquality⟩
          let entry := tailEntry.prependForLeaf head
          refine ⟨leaf, Or.inr ⟨entry, ?_, factorEquality⟩⟩
          rw [LocalFactorLeaves.eventIntervals]
          split
          · exact List.mem_map.mpr ⟨tailEntry, tailEntryMember, rfl⟩
          · exact List.mem_cons_of_mem _
              (List.mem_map.mpr ⟨tailEntry, tailEntryMember, rfl⟩)

/-- Every exact rational zero of an aligned factor is retained by the
executable count-one event list.  An `interior` leaf is impossible by its
computed positive lower bound; a `firstMember` leaf is the required entry. -/
theorem LocalFactorLeaves.eventIntervals_covers_rational_zero
    {interval : RationalInterval} {factors : List Factor}
    (leaves : LocalFactorLeaves interval factors)
    {factor : Factor} (factorMember : factor ∈ factors)
    {t : ℚ} (lower : interval.lower ≤ t) (upper : t ≤ interval.upper)
    (factorZero : factor.polynomial.eval t = 0) :
    ∃ entry ∈ leaves.eventIntervals,
      entry.factor = factor ∧
        entry.root.interval.lower ≤ t ∧
        t ≤ entry.root.interval.upper := by
  induction leaves generalizing factor t with
  | nil => simp at factorMember
  | @cons _ _ head tail inductionHypothesis =>
      rcases List.mem_cons.mp factorMember with rfl | tailMember
      · cases kindEquation : head.kind with
        | interior =>
            have countZero : sturmRootCount2 factor.polynomial
                interval.lower interval.upper = 0 := by
              simpa [kindEquation, EventKind.contribution2] using
                head.countCertificate
            exact (FTA.PositiveLowerBound.eval_ne_zero_of_sturmRootCount2_eq_zero
              factor.input interval head.proper head.lowerClear
              head.upperClear countZero lower upper factorZero).elim
        | firstMember =>
            have eventIntervalsEq :
                (LocalFactorLeaves.cons head tail).eventIntervals =
                  { factor := factor
                    member := List.mem_cons_self
                    root := head.countOneInterval kindEquation } ::
                    tail.eventIntervals.map fun entry => entry.prepend factor := by
              rw [LocalFactorLeaves.eventIntervals]
              split
              · rename_i interiorEquation
                rw [kindEquation] at interiorEquation
                contradiction
              · rfl
            rw [eventIntervalsEq]
            exact ⟨_, List.mem_cons_self, rfl, lower, upper⟩
      · rcases inductionHypothesis tailMember lower upper factorZero with
          ⟨tailEntry, tailEntryMember, factorEquality, entryLower,
            entryUpper⟩
        let entry := tailEntry.prependForLeaf head
        refine ⟨entry, ?_, factorEquality, ?_, ?_⟩
        · rw [LocalFactorLeaves.eventIntervals]
          split
          · apply List.mem_map.mpr
            exact ⟨tailEntry, tailEntryMember, rfl⟩
          · apply List.mem_cons_of_mem
            apply List.mem_map.mpr
            exact ⟨tailEntry, tailEntryMember, rfl⟩
        · exact entryLower
        · exact entryUpper

/-- A successful all-interior test proves every aligned squarefree-factor
count is zero on the common cell. -/
theorem LocalFactorLeaves.count_eq_zero_of_allInterior
    {interval : RationalInterval} {factors : List Factor}
    (leaves : LocalFactorLeaves interval factors)
    (allInterior : leaves.allInterior = true) :
    ∀ factor ∈ factors,
      sturmRootCount2 factor.polynomial interval.lower interval.upper = 0 := by
  induction leaves with
  | nil => simp
  | @cons factor factors head tail inductionHypothesis =>
      cases kindEquation : head.kind with
      | interior =>
          have tailInterior : tail.allInterior = true := by
            simpa [LocalFactorLeaves.allInterior, kindEquation] using allInterior
          intro candidate member
          rcases List.mem_cons.mp member with rfl | tailMember
          · simpa [kindEquation, EventKind.contribution2] using
              head.countCertificate
          · exact inductionHypothesis tailInterior candidate tailMember
      | firstMember =>
          simp [LocalFactorLeaves.allInterior, kindEquation] at allInterior

/-- Failure of the all-interior test exposes a concrete aligned factor with
one local real event (represented by doubled Sturm count `2`). -/
theorem LocalFactorLeaves.exists_count_eq_two_of_allInterior_eq_false
    {interval : RationalInterval} {factors : List Factor}
    (leaves : LocalFactorLeaves interval factors)
    (hasEvent : leaves.allInterior = false) :
    ∃ factor ∈ factors,
      sturmRootCount2 factor.polynomial interval.lower interval.upper = 2 := by
  induction leaves with
  | nil => simp [LocalFactorLeaves.allInterior] at hasEvent
  | @cons factor factors head tail inductionHypothesis =>
      cases kindEquation : head.kind with
      | interior =>
          have tailEvent : tail.allInterior = false := by
            simpa [LocalFactorLeaves.allInterior, kindEquation] using hasEvent
          rcases inductionHypothesis tailEvent with
            ⟨candidate, candidateMember, count⟩
          exact ⟨candidate, by simp [candidateMember], count⟩
      | firstMember =>
          exact ⟨factor, by simp, by
            simpa [kindEquation, EventKind.contribution2] using
              head.countCertificate⟩

/-- Run every factor's genuine local classifier on the same rational cell. -/
def localFactorPartitions? :
    (factors : List Factor) → (interval : RationalInterval) → interval.Proper →
      (factorProduct factors).eval interval.lower ≠ 0 →
      (factorProduct factors).eval interval.upper ≠ 0 →
      Option (LocalFactorLeaves interval factors)
  | [], _interval, _proper, _lowerClear, _upperClear => some .nil
  | factor :: factors, interval, proper, lowerClear, upperClear => by
      have headLower : factor.polynomial.eval interval.lower ≠ 0 := by
        intro zero
        apply lowerClear
        simp [factorProduct, zero]
      have headUpper : factor.polynomial.eval interval.upper ≠ 0 := by
        intro zero
        apply upperClear
        simp [factorProduct, zero]
      have tailLower : (factorProduct factors).eval interval.lower ≠ 0 := by
        intro zero
        apply lowerClear
        simp [factorProduct, zero]
      have tailUpper : (factorProduct factors).eval interval.upper ≠ 0 := by
        intro zero
        apply upperClear
        simp [factorProduct, zero]
      exact match classifiedEventLeaf? factor.input interval proper
          headLower headUpper with
      | none => none
      | some (.split _ _ _ _ _ _) => none
      | some (.leaf headProper headLower headUpper kind countCertificate) =>
          match localFactorPartitions? factors interval proper tailLower tailUpper with
          | none => none
          | some tail =>
              some (.cons
                { proper := headProper
                  lowerClear := headLower
                  upperClear := headUpper
                  kind := kind
                  countCertificate := countCertificate }
                tail)

/-- Positive common width below every factor's computed local classifier
resolution on the ambient root interval. -/
def commonFactorResolution (factors : List Factor)
    (root : RationalInterval) : ℚ :=
  FTA.Maximality.positiveMinimum
    (factors.map fun factor =>
      ambientEventClassifierWidthResolution factor.input root)

theorem commonFactorResolution_pos
    (factors : List Factor) (root : RationalInterval) :
    0 < commonFactorResolution factors root := by
  apply FTA.Maximality.positiveMinimum_pos
  intro width member
  rw [List.mem_map] at member
  rcases member with ⟨factor, _factorMember, rfl⟩
  exact ambientEventClassifierWidthResolution_pos factor.input root

theorem commonFactorResolution_le_factor
    {factors : List Factor} {factor : Factor} (member : factor ∈ factors)
    (root : RationalInterval) :
    commonFactorResolution factors root ≤
      ambientEventClassifierWidthResolution factor.input root := by
  apply FTA.Maximality.positiveMinimum_le_of_mem
  exact List.mem_map.mpr ⟨factor, member, rfl⟩

theorem commonFactorResolution_cons_le_tail
    (factor : Factor) (factors : List Factor) (root : RationalInterval) :
    commonFactorResolution (factor :: factors) root ≤
      commonFactorResolution factors root := by
  simp only [commonFactorResolution, List.map_cons,
    FTA.Maximality.positiveMinimum, List.foldr_cons]
  exact min_le_right _ _

/-- Below the common computed width, every genuine local factor classifier
succeeds on the same refined cell. -/
def localFactorPartitions?_succeeds_of_refined_width :
    (factors : List Factor) → (root interval : RationalInterval) →
      interval.Refines root → (proper : interval.Proper) →
      (lowerClear : (factorProduct factors).eval interval.lower ≠ 0) →
      (upperClear : (factorProduct factors).eval interval.upper ≠ 0) →
      interval.width < commonFactorResolution factors root →
      { partitions : LocalFactorLeaves interval factors //
        localFactorPartitions? factors interval proper lowerClear upperClear =
          some partitions }
  | [], _root, interval, _refines, proper, lowerClear, upperClear, _width =>
      ⟨.nil, by simp [localFactorPartitions?]⟩
  | factor :: factors, root, interval, refines, proper,
      lowerClear, upperClear, width => by
      have headLower : factor.polynomial.eval interval.lower ≠ 0 := by
        intro zero
        apply lowerClear
        simp [factorProduct, zero]
      have headUpper : factor.polynomial.eval interval.upper ≠ 0 := by
        intro zero
        apply upperClear
        simp [factorProduct, zero]
      have tailLower : (factorProduct factors).eval interval.lower ≠ 0 := by
        intro zero
        apply lowerClear
        simp [factorProduct, zero]
      have tailUpper : (factorProduct factors).eval interval.upper ≠ 0 := by
        intro zero
        apply upperClear
        simp [factorProduct, zero]
      have headWidth : interval.width <
          ambientEventClassifierWidthResolution factor.input root :=
        width.trans_le (commonFactorResolution_le_factor
          (by simp) root)
      have tailWidth : interval.width < commonFactorResolution factors root :=
        width.trans_le (commonFactorResolution_cons_le_tail factor factors root)
      let headResult := classifiedEventLeaf?_succeeds_of_refined_width
        factor.input root interval refines proper headLower headUpper headWidth
      let tailResult := localFactorPartitions?_succeeds_of_refined_width
        factors root interval refines proper tailLower tailUpper tailWidth
      cases headPartition : headResult.1 with
      | leaf headProper headLower' headUpper' kind countCertificate =>
          have headSuccess := headResult.2
          rw [headPartition] at headSuccess
          let headLeaf : LocalFactorLeaf factor interval :=
            { proper := headProper
              lowerClear := headLower'
              upperClear := headUpper'
              kind := kind
              countCertificate := countCertificate }
          refine ⟨.cons headLeaf tailResult.1, ?_⟩
          simp [localFactorPartitions?, headSuccess, tailResult.2, headLeaf]
      | split cut lowerLt ltUpper cutClear left right =>
          have impossible : False := by
            rcases classifiedEventLeaf?_some_isLeaf headResult.2 with
              ⟨kind, countCertificate, equality⟩
            rw [headPartition] at equality
            cases equality
          exact impossible.elim

/-! ## Fuel-recursive common partition -/

inductive CommonFactorPartition
    (factors : List Factor) : RationalInterval → Type
  | leaf {interval : RationalInterval}
      (proper : interval.Proper)
      (lowerClear : (factorEventGuard factors).eval interval.lower ≠ 0)
      (upperClear : (factorEventGuard factors).eval interval.upper ≠ 0)
      (leaves : LocalFactorLeaves interval factors) :
      CommonFactorPartition factors interval
  | split {interval : RationalInterval} (cut : ℚ)
      (lowerLt : interval.lower < cut) (ltUpper : cut < interval.upper)
      (cutClear : (factorEventGuard factors).eval cut ≠ 0)
      (left : CommonFactorPartition factors (interval.left cut))
      (right : CommonFactorPartition factors (interval.right cut)) :
      CommonFactorPartition factors interval

/-- One terminal common cell with every factor's aligned exact local count. -/
structure CommonFactorCell (factors : List Factor) where
  interval : RationalInterval
  proper : interval.Proper
  lowerClear : (factorEventGuard factors).eval interval.lower ≠ 0
  upperClear : (factorEventGuard factors).eval interval.upper ≠ 0
  leaves : LocalFactorLeaves interval factors

/-- Flatten the finite common partition tree into its ordered terminal cells. -/
def CommonFactorPartition.cells
    {factors : List Factor} {interval : RationalInterval} :
    CommonFactorPartition factors interval → List (CommonFactorCell factors)
  | .leaf proper lowerClear upperClear leaves =>
      [{ interval := interval, proper, lowerClear, upperClear, leaves }]
  | .split _cut _lowerLt _ltUpper _cutClear left right =>
      left.cells ++ right.cells

theorem CommonFactorPartition.cells_ne_nil
    {factors : List Factor} {interval : RationalInterval}
    (partition : CommonFactorPartition factors interval) :
    partition.cells ≠ [] := by
  induction partition with
  | leaf => simp [CommonFactorPartition.cells]
  | split cut lowerLt ltUpper cutClear left right leftIH rightIH =>
      simp [CommonFactorPartition.cells, leftIH, rightIH]

/-- Every flattened terminal cell refines the partition interval. -/
theorem CommonFactorPartition.cell_refines
    {factors : List Factor} {interval : RationalInterval}
    (partition : CommonFactorPartition factors interval) :
    ∀ cell ∈ partition.cells, cell.interval.Refines interval := by
  induction partition with
  | leaf proper lowerClear upperClear leaves =>
      intro cell member
      simp only [CommonFactorPartition.cells, List.mem_singleton] at member
      subst cell
      exact RationalInterval.refines_refl _
  | @split parent cut lowerLt ltUpper cutClear left right leftIH rightIH =>
      intro cell member
      rw [CommonFactorPartition.cells, List.mem_append] at member
      rcases member with leftMember | rightMember
      · exact RationalInterval.refines_trans (leftIH cell leftMember)
          ⟨le_rfl, ltUpper.le⟩
      · exact RationalInterval.refines_trans (rightIH cell rightMember)
          ⟨lowerLt.le, le_rfl⟩

/-- The flattened terminal cells cover every rational parameter of the
partition interval.  Shared cut points may be assigned to either child. -/
theorem CommonFactorPartition.cells_cover
    {factors : List Factor} {interval : RationalInterval}
    (partition : CommonFactorPartition factors interval)
    {t : ℚ} (lower : interval.lower ≤ t) (upper : t ≤ interval.upper) :
    ∃ cell ∈ partition.cells,
      cell.interval.lower ≤ t ∧ t ≤ cell.interval.upper := by
  induction partition with
  | @leaf leafInterval proper lowerClear upperClear leaves =>
      let cell : CommonFactorCell factors :=
        { interval := leafInterval
          proper := proper
          lowerClear := lowerClear
          upperClear := upperClear
          leaves := leaves }
      refine ⟨cell, ?_, ?_, ?_⟩
      · simp [CommonFactorPartition.cells, cell]
      · exact lower
      · exact upper
  | @split parent cut lowerLt ltUpper cutClear left right leftIH rightIH =>
      by_cases leftSide : t ≤ cut
      · rcases leftIH lower leftSide with
          ⟨cell, member, cellLower, cellUpper⟩
        exact ⟨cell, by
          simp [CommonFactorPartition.cells, member], cellLower, cellUpper⟩
      · have rightSide : cut ≤ t := (lt_of_not_ge leftSide).le
        rcases rightIH rightSide upper with
          ⟨cell, member, cellLower, cellUpper⟩
        exact ⟨cell, by
          simp [CommonFactorPartition.cells, member], cellLower, cellUpper⟩

/-- Executable common subdivision.  A cell is retained exactly when every
factor's genuine local classifier succeeds there. -/
def buildCommonFactorPartition? (factors : List Factor) :
    (fuel : ℕ) → (interval : RationalInterval) → interval.Proper →
      (factorEventGuard factors).eval interval.lower ≠ 0 →
      (factorEventGuard factors).eval interval.upper ≠ 0 →
      Option (CommonFactorPartition factors interval)
  | 0, interval, proper, lowerClear, upperClear =>
      let productLower := factorProduct_eval_ne_zero_of_eventGuard lowerClear
      let productUpper := factorProduct_eval_ne_zero_of_eventGuard upperClear
      match localFactorPartitions? factors interval proper
          productLower productUpper with
      | none => none
      | some leaves => some (.leaf proper lowerClear upperClear leaves)
  | fuel + 1, interval, proper, lowerClear, upperClear =>
      let productLower := factorProduct_eval_ne_zero_of_eventGuard lowerClear
      let productUpper := factorProduct_eval_ne_zero_of_eventGuard upperClear
      match localFactorPartitions? factors interval proper
          productLower productUpper with
      | some leaves => some (.leaf proper lowerClear upperClear leaves)
      | none =>
          let cut := factorEventCut factors interval.lower interval.upper
          let geometry := factorEventCut_geometry factors proper
          let cutClear := (factorEventCut_spec factors proper).1
          match buildCommonFactorPartition? factors fuel (interval.left cut)
              geometry.1 lowerClear cutClear with
          | none => none
          | some left =>
              match buildCommonFactorPartition? factors fuel (interval.right cut)
                  geometry.2.1 cutClear upperClear with
              | none => none
              | some right => some (.split cut geometry.1 geometry.2.1
                  cutClear left right)

/-- A displayed geometric fuel bound makes the executable common partition
builder succeed. -/
def buildCommonFactorPartition?_succeeds
    (factors : List Factor) (root : RationalInterval) :
    (fuel : ℕ) → (interval : RationalInterval) → interval.Refines root →
      (proper : interval.Proper) →
      (lowerClear : (factorEventGuard factors).eval interval.lower ≠ 0) →
      (upperClear : (factorEventGuard factors).eval interval.upper ≠ 0) →
      (2 / 3 : ℚ) ^ fuel * interval.width <
        commonFactorResolution factors root →
      { partition : CommonFactorPartition factors interval //
        buildCommonFactorPartition? factors fuel interval proper
          lowerClear upperClear = some partition }
  | 0, interval, refines, proper, lowerClear, upperClear, sufficient => by
      have productLower := factorProduct_eval_ne_zero_of_eventGuard lowerClear
      have productUpper := factorProduct_eval_ne_zero_of_eventGuard upperClear
      have width : interval.width < commonFactorResolution factors root := by
        simpa using sufficient
      let localResult := localFactorPartitions?_succeeds_of_refined_width
        factors root interval refines proper productLower productUpper width
      refine ⟨.leaf proper lowerClear upperClear localResult.1, ?_⟩
      simp [buildCommonFactorPartition?, localResult.2]
  | fuel + 1, interval, refines, proper,
      lowerClear, upperClear, sufficient => by
      have productLower := factorProduct_eval_ne_zero_of_eventGuard lowerClear
      have productUpper := factorProduct_eval_ne_zero_of_eventGuard upperClear
      cases localSearch : localFactorPartitions? factors interval proper
          productLower productUpper with
      | some leaves =>
          exact ⟨.leaf proper lowerClear upperClear leaves, by
            simp [buildCommonFactorPartition?, localSearch]⟩
      | none =>
          let cut := factorEventCut factors interval.lower interval.upper
          let geometry := factorEventCut_geometry factors proper
          let cutClear := (factorEventCut_spec factors proper).1
          let leftInterval := interval.left cut
          let rightInterval := interval.right cut
          have factorPositive : 0 < (2 / 3 : ℚ) ^ fuel := by positivity
          have leftWidth : leftInterval.width <
              (2 / 3 : ℚ) * interval.width := by
            dsimp [leftInterval, cut, RationalInterval.width,
              RationalInterval.left]
            exact geometry.2.2.1
          have rightWidth : rightInterval.width <
              (2 / 3 : ℚ) * interval.width := by
            dsimp [rightInterval, cut, RationalInterval.width,
              RationalInterval.right]
            exact geometry.2.2.2
          have leftSufficient : (2 / 3 : ℚ) ^ fuel * leftInterval.width <
              commonFactorResolution factors root := by
            calc
              (2 / 3 : ℚ) ^ fuel * leftInterval.width <
                  (2 / 3 : ℚ) ^ fuel *
                    ((2 / 3 : ℚ) * interval.width) :=
                mul_lt_mul_of_pos_left leftWidth factorPositive
              _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
                rw [pow_succ]
                ring
              _ < commonFactorResolution factors root := by
                simpa [Nat.succ_eq_add_one] using sufficient
          have rightSufficient : (2 / 3 : ℚ) ^ fuel * rightInterval.width <
              commonFactorResolution factors root := by
            calc
              (2 / 3 : ℚ) ^ fuel * rightInterval.width <
                  (2 / 3 : ℚ) ^ fuel *
                    ((2 / 3 : ℚ) * interval.width) :=
                mul_lt_mul_of_pos_left rightWidth factorPositive
              _ = (2 / 3 : ℚ) ^ (fuel + 1) * interval.width := by
                rw [pow_succ]
                ring
              _ < commonFactorResolution factors root := by
                simpa [Nat.succ_eq_add_one] using sufficient
          have leftRefinesParent : leftInterval.Refines interval := by
            dsimp [leftInterval, cut, RationalInterval.Refines,
              RationalInterval.left]
            exact ⟨le_rfl, geometry.2.1.le⟩
          have rightRefinesParent : rightInterval.Refines interval := by
            dsimp [rightInterval, cut, RationalInterval.Refines,
              RationalInterval.right]
            exact ⟨geometry.1.le, le_rfl⟩
          have leftRefines : leftInterval.Refines root :=
            RationalInterval.refines_trans leftRefinesParent refines
          have rightRefines : rightInterval.Refines root :=
            RationalInterval.refines_trans rightRefinesParent refines
          let leftResult := buildCommonFactorPartition?_succeeds factors root
            fuel leftInterval leftRefines geometry.1 lowerClear cutClear
            leftSufficient
          let rightResult := buildCommonFactorPartition?_succeeds factors root
            fuel rightInterval rightRefines geometry.2.1 cutClear upperClear
            rightSufficient
          refine ⟨.split cut geometry.1 geometry.2.1 cutClear
            leftResult.1 rightResult.1, ?_⟩
          simp [buildCommonFactorPartition?, localSearch, cut,
            leftInterval, rightInterval,
            leftResult.2, rightResult.2]

/-- Explicit common-partition fuel from rational ceiling arithmetic. -/
def commonPartitionDepth (factors : List Factor) (root : RationalInterval) : ℕ :=
  geometricDepth root.width (commonFactorResolution factors root / 2)

theorem commonPartitionDepth_sufficient
    (factors : List Factor) (root : RationalInterval) (proper : root.Proper) :
    (2 / 3 : ℚ) ^ commonPartitionDepth factors root * root.width <
      commonFactorResolution factors root := by
  have halfPositive : 0 < commonFactorResolution factors root / 2 := by
    linarith [commonFactorResolution_pos factors root]
  have bound := geometricDepth_sufficient
    (RationalInterval.width_pos proper).le halfPositive
  calc
    (2 / 3 : ℚ) ^ commonPartitionDepth factors root * root.width ≤
        commonFactorResolution factors root / 2 := by
      simpa [commonPartitionDepth] using bound
    _ < commonFactorResolution factors root := by
      linarith [commonFactorResolution_pos factors root]

/-- Total computed common partition on any proper interval whose simultaneous
factor guard is clear at both rational endpoints. -/
def computedCommonFactorPartition
    (factors : List Factor) (root : RationalInterval) (proper : root.Proper)
    (lowerClear : (factorEventGuard factors).eval root.lower ≠ 0)
    (upperClear : (factorEventGuard factors).eval root.upper ≠ 0) :
    CommonFactorPartition factors root :=
  (buildCommonFactorPartition?_succeeds factors root
    (commonPartitionDepth factors root) root
    (RationalInterval.refines_refl root) proper lowerClear upperClear
    (commonPartitionDepth_sufficient factors root proper)).1

end CCLIntersectionPartition
end FTA
