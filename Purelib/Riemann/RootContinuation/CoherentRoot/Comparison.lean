module

public import Purelib.Riemann.RootContinuation.CoherentRoot
public import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
import Purelib.RootIsolation.Track.Transport
public import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.State.WindingOne.Count
import Purelib.Data.Gaussian.Norm.Bounds
public import Purelib.Geometry.Rational.Box.Separation.Certificate
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Nat.Order
import Purelib.Tactic.QuotientFreeOmega

/-!
# Comparison of original squarefree root tracks in one ambient box

Strictly nested winding-one owners select the same root of the original
polynomial. Finite winding counts exclude separated later states; a rational
overlap point then gives computed all-input comparisons at the original caches.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot

open Purelib.Data.Rat.Fraction
open Purelib.RootIsolation
open Purelib.Polynomial
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Geometry.Rational
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Data.Nat

/-- Later states of nested original owners cannot separate inside one winding-one box.

Both tracks retain the same polynomial and ambient box. Their squarefree
input computes axis elimination; two separated later winding-one states would
force raw winding at least eight inside the original raw-winding-four owner.
-/
theorem states_not_separated {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    (outer inner : WindingOneTrack polynomial ambient)
    (nested : inner.initial.box.StrictInterior outer.initial.box)
    {outerIndex : Nat} (positive : 0 < outerIndex) (innerIndex : Nat) :
    ¬ (state outer outerIndex).box.Separated (state inner innerIndex).box := by
  intro separated
  have outerStrict : (state outer outerIndex).box.StrictInterior outer.initial.box := by
    cases outerIndex with
    | zero => exact (Nat.not_lt_zero _ positive).elim
    | succ index =>
      have firstStrict : (state outer 1).box.StrictInterior outer.initial.box := outer.strict _ _ _
      exact (Box.Refinement.StrictInterior.of_refines firstStrict)
        (state_refines_of_le outer (Nat.succ_le_succ (Nat.zero_le index)))
  have innerStrict : (state inner innerIndex).box.StrictInterior outer.initial.box :=
    (Box.Refinement.StrictInterior.of_refines nested)
      (state_refines_of_le inner (Nat.zero_le innerIndex))
  let region : Clearance.Box.Region.ClearRegion polynomial ambient :=
    { box := outer.initial.box
      refinesAmbient := outer.initial.refinesAmbient
      proper := outer.initial.proper
      clearance := outer.initial.clearance }
  have winding := State.WindingOne.Count.region_rawWinding_ge_eight_of_separated
    input.degreeAtLeastTwo input.squarefree input.elimination region
      (state outer outerIndex) (state inner innerIndex) outerStrict innerStrict separated
  change 8 ≤ Winding.Box.Basic.quadrupledBoxWinding polynomial outer.initial.box at winding
  rewrite [outer.initial.rawWindingFour] at winding
  omega0

namespace CertifiedName

/-- Compare two actual cached root approximations at strictly nested original owners.

The original source refiners pay one quarter of each requested tolerance.
Every permitted pair of later original boxes overlaps, and the two retained
diagonal bounds control their actual sample distance through an explicit point.
-/
def compare_nested {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box) :
    Equivalence.Equivalent first.approximation second.approximation where
  compare firstStart secondStart target targetPositive := by
    let quarter := target / 4
    have quarterPositive : 0 < quarter := Fraction.Order.Field.div_pos_direct targetPositive (by decide)
    let firstIndex := first.approximation.refineIndex (max firstStart 1) quarter quarterPositive
    let secondIndex := second.approximation.refineIndex secondStart quarter quarterPositive
    have firstStartMax : firstStart ≤ max firstStart 1 := by
      rewrite [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have firstPositive : 0 < firstIndex := by
      have oneLe : 1 ≤ max firstStart 1 := by
        rewrite [Order.max_eq_natMax]
        exact Order.le_max_right _ _
      exact oneLe.trans (first.approximation.refineIndex_ge (max firstStart 1) quarter quarterPositive)
    exact
      { leftIndex := firstIndex
        rightIndex := secondIndex
        left_ge := firstStartMax.trans (first.approximation.refineIndex_ge _ _ _)
        right_ge := second.approximation.refineIndex_ge _ _ _
        close := by
          intro firstLater secondLater firstOrder secondOrder
          have notSeparated := states_not_separated input outer inner nested
            (firstPositive.trans_le firstOrder) secondLater
          let point := Box.overlapPoint (state outer firstLater).box (state inner secondLater).box
          have inside := Box.contains_overlapPoint_of_not_separated notSeparated
          have firstBound := (state outer firstLater).box.normSq_sub_le_diagonalSq
            (state outer firstLater).box.contains_anchor inside.1
          have secondBound := (state inner secondLater).box.normSq_sub_le_diagonalSq
            inside.2 (state inner secondLater).box.contains_anchor
          have firstDiagonal : (state outer firstLater).box.diagonalSq < quarter := by
            have accurate := first.approximation.refineIndex_accurate (max firstStart 1) quarter quarterPositive
            have radius : first.approximation.radiusSq firstIndex =
                Geometric.Basic.quarterRadius (scale outer) firstIndex := by
              rewrite [first.approximation_eq]
              rfl
            rewrite [radius] at accurate
            exact (state_diagonal_le outer firstLater).trans_lt
              ((Geometric.Basic.quarterRadius_antitone (scale_positive outer).le firstOrder).trans_lt accurate)
          have secondDiagonal : (state inner secondLater).box.diagonalSq < quarter := by
            have accurate := second.approximation.refineIndex_accurate secondStart quarter quarterPositive
            have radius : second.approximation.radiusSq secondIndex =
                Geometric.Basic.quarterRadius (scale inner) secondIndex := by
              rewrite [second.approximation_eq]
              rfl
            rewrite [radius] at accurate
            exact (state_diagonal_le inner secondLater).trans_lt
              ((Geometric.Basic.quarterRadius_antitone (scale_positive inner).le secondOrder).trans_lt accurate)
          rewrite [first.approximation_eq, second.approximation_eq, approximation_sample, approximation_sample]
          calc
            normSq ((state outer firstLater).box.anchor - (state inner secondLater).box.anchor) ≤
                2 * (normSq ((state outer firstLater).box.anchor - point) +
                  normSq (point - (state inner secondLater).box.anchor)) :=
              Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
            _ ≤ 2 * ((state outer firstLater).box.diagonalSq + (state inner secondLater).box.diagonalSq) :=
              Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (Order.Arithmetic.add_le_add_direct firstBound secondBound) (by decide)
            _ < 2 * (quarter + quarter) :=
              Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
                (Order.Arithmetic.add_lt_add_direct firstDiagonal secondDiagonal)
            _ = target := by
              dsimp only [quarter]
              rewrite [Purelib.Data.Rat.Bounds.Quarter.two_quarters target, Fraction.Field.mul_comm]
              exact Purelib.Data.Rat.Bounds.Quarter.half_mul_two target }

/-- Paid boxes at two nested original roots give their actual later-sample comparison below the same target.

Both retained squared targets equal one quarter of the displayed tolerance.
The outer selected stage is positive, so every later pair overlaps inside the
original winding-one owner and the retained diagonals bound its distance.
-/
theorem prepared_close {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box) (target : Coordinate)
    {firstStart secondStart : Nat} (firstPaid : Refinement first firstStart)
    (secondPaid : Refinement second secondStart) (firstPositive : 0 < firstPaid.index)
    (firstTarget : firstPaid.targetSq = target / 4) (secondTarget : secondPaid.targetSq = target / 4) :
    ∀ {firstLater secondLater : Nat}, firstPaid.index ≤ firstLater → secondPaid.index ≤ secondLater →
      normSq (first.approximation.sample firstLater - second.approximation.sample secondLater) < target := by
  let quarter := target / 4
  intro firstLater secondLater firstOrder secondOrder
  have notSeparated := states_not_separated input outer inner nested
    (firstPositive.trans_le firstOrder) secondLater
  let point := Box.overlapPoint (state outer firstLater).box (state inner secondLater).box
  have inside := Box.contains_overlapPoint_of_not_separated notSeparated
  have firstBound := (state outer firstLater).box.normSq_sub_le_diagonalSq
    (state outer firstLater).box.contains_anchor inside.1
  have secondBound := (state inner secondLater).box.normSq_sub_le_diagonalSq
    inside.2 (state inner secondLater).box.contains_anchor
  have firstDiagonal : (state outer firstLater).box.diagonalSq < quarter :=
    (firstPaid.later_diagonal_lt firstOrder).trans_eq firstTarget
  have secondDiagonal : (state inner secondLater).box.diagonalSq < quarter :=
    (secondPaid.later_diagonal_lt secondOrder).trans_eq secondTarget
  rewrite [first.approximation_eq, second.approximation_eq, approximation_sample, approximation_sample]
  calc
    normSq ((state outer firstLater).box.anchor - (state inner secondLater).box.anchor) ≤
        2 * (normSq ((state outer firstLater).box.anchor - point) +
          normSq (point - (state inner secondLater).box.anchor)) :=
      Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
    _ ≤ 2 * ((state outer firstLater).box.diagonalSq + (state inner secondLater).box.diagonalSq) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct firstBound secondBound) (by decide)
    _ < 2 * (quarter + quarter) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        (Fraction.Order.Arithmetic.add_lt_add_direct firstDiagonal secondDiagonal)
    _ = target := by
      dsimp only [quarter]
      rewrite [Purelib.Data.Rat.Bounds.Quarter.two_quarters target, Fraction.Field.mul_comm]
      exact Purelib.Data.Rat.Bounds.Quarter.half_mul_two target

/-- Compare original nested-root programs through retained compatible cache requests or their original refiners.

The optional pair retains both actual original paid states. Each requested
floor is promoted to the same retained index; a compatible strict diagonal
check consumes that complete state through `atRequest`. Other requests use
the original bounded cache refinement. The default keeps the whole original
request procedure and comparison indices.
-/
@[expose] def compare_nested_prepared {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box)
    (cached : Option (Refinement.Pair first second) := none) :
    Equivalence.Equivalent first.approximation second.approximation where
  compare firstStart secondStart target targetPositive := by
    let quarter := target / 4
    have quarterPositive : 0 < quarter := Fraction.Order.Field.div_pos_direct targetPositive (by decide)
    let firstFloor := match cached with
      | none => firstStart
      | some retained => max firstStart retained.1.2.index
    let secondFloor := match cached with
      | none => secondStart
      | some retained => max secondStart retained.2.2.index
    let firstPaid : Refinement first (max firstFloor 1) := match cached with
      | none => Refinement.ofTarget first (max firstFloor 1) quarter quarterPositive
      | some retained => retained.1.2.atRequest (max firstFloor 1) quarter quarterPositive
    let secondPaid : Refinement second secondFloor := match cached with
      | none => Refinement.ofTarget second secondFloor quarter quarterPositive
      | some retained => retained.2.2.atRequest secondFloor quarter quarterPositive
    have firstFloorGe : firstStart ≤ firstFloor := by
      cases cached with
      | none => exact Nat.le_refl _
      | some retained =>
          change firstStart ≤ max firstStart retained.1.2.index
          rewrite [Order.max_eq_natMax]
          exact Order.le_max_left _ _
    have secondFloorGe : secondStart ≤ secondFloor := by
      cases cached with
      | none => exact Nat.le_refl _
      | some retained =>
          change secondStart ≤ max secondStart retained.2.2.index
          rewrite [Order.max_eq_natMax]
          exact Order.le_max_left _ _
    have firstStartMax : firstStart ≤ max firstFloor 1 := by
      have floorMax : firstFloor ≤ max firstFloor 1 := by
        rewrite [Order.max_eq_natMax]
        exact Order.le_max_left _ _
      exact firstFloorGe.trans floorMax
    have firstPositive : 0 < firstPaid.index := by
      have oneLe : 1 ≤ max firstFloor 1 := by
        rewrite [Order.max_eq_natMax]
        exact Order.le_max_right _ _
      exact oneLe.trans firstPaid.index_ge
    have firstTarget : firstPaid.targetSq = quarter := by
      cases cached with
      | none => exact Refinement.ofTarget_targetSq first _ quarter quarterPositive
      | some retained => exact retained.1.2.atRequest_targetSq _ quarter quarterPositive
    have secondTarget : secondPaid.targetSq = quarter := by
      cases cached with
      | none => exact Refinement.ofTarget_targetSq second _ quarter quarterPositive
      | some retained => exact retained.2.2.atRequest_targetSq _ quarter quarterPositive
    exact
      { leftIndex := firstPaid.index
        rightIndex := secondPaid.index
        left_ge := firstStartMax.trans firstPaid.index_ge
        right_ge := secondFloorGe.trans secondPaid.index_ge
        close := prepared_close input first second nested target firstPaid secondPaid firstPositive
          firstTarget secondTarget }

/-- The complete default comparison retains both original bounded-refinement indices and all its certificates. -/
theorem compare_nested_prepared_none {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial) {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box)
    (firstStart secondStart : Nat) (target : Coordinate) (positive : 0 < target) :
    let original := (first.compare_nested_prepared input second nested none).compare
      firstStart secondStart target positive
    original =
      { leftIndex := (Refinement.ofTarget first (max firstStart 1) (target / 4)
          (Fraction.Order.Field.div_pos_direct positive (by decide))).index
        rightIndex := (Refinement.ofTarget second secondStart (target / 4)
          (Fraction.Order.Field.div_pos_direct positive (by decide))).index
        left_ge := original.left_ge
        right_ge := original.right_ge
        close := original.close } := rfl

/-- Read both original prepared-comparison indices from their unchanged bounded payments. -/
private theorem prepared_indices {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box)
    (firstStart secondStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    ((first.compare_nested_prepared input second nested).compare
      firstStart secondStart target positive).leftIndex =
        (CoherentRoot.Refinement.ofTarget first (max firstStart 1) (target / 4)
          (Fraction.Order.Field.div_pos_direct positive (by decide))).index ∧
    ((first.compare_nested_prepared input second nested).compare
      firstStart secondStart target positive).rightIndex =
        (CoherentRoot.Refinement.ofTarget second secondStart (target / 4)
          (Fraction.Order.Field.div_pos_direct positive (by decide))).index := ⟨rfl, rfl⟩

/-- Both original prepared-comparison indices are those of the same original paid searches. -/
theorem compare_nested_prepared_indices {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box)
    (firstStart secondStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    ((first.compare_nested_prepared input second nested).compare
      firstStart secondStart target positive).leftIndex =
        (CoherentRoot.Refinement.ofTarget first (max firstStart 1) (target / 4)
          (Fraction.Order.Field.div_pos_direct positive (by decide))).index ∧
    ((first.compare_nested_prepared input second nested).compare
      firstStart secondStart target positive).rightIndex =
        (CoherentRoot.Refinement.ofTarget second secondStart (target / 4)
          (Fraction.Order.Field.div_pos_direct positive (by decide))).index :=
  prepared_indices input first second nested firstStart secondStart target positive

/-- Consume the complete original paid refinements for one nested-root comparison.

Both retained payments are authenticated against the unchanged bounded searches.
The result reads their actual indices; the original comparison supplies its same
all-later bound without executing either search again.
-/
def compareNestedFromPaid {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box)
    (firstStart secondStart : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (firstPaid : CoherentRoot.Refinement first (max firstStart 1))
    (firstSame : firstPaid = CoherentRoot.Refinement.ofTarget first (max firstStart 1) (target / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide)))
    (secondPaid : CoherentRoot.Refinement second secondStart)
    (secondSame : secondPaid = CoherentRoot.Refinement.ofTarget second secondStart (target / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide))) :
    Equivalence.Comparison first.approximation second.approximation firstStart secondStart target where
  leftIndex := firstPaid.index
  rightIndex := secondPaid.index
  left_ge := by
    have starts : firstStart ≤ max firstStart 1 := by
      rewrite [Purelib.Data.Nat.Order.max_eq_natMax]
      exact Purelib.Data.Nat.Order.le_max_left _ _
    exact starts.trans firstPaid.index_ge
  right_ge := secondPaid.index_ge
  close := by
    intro firstLater secondLater firstOrder secondOrder
    let original := (first.compare_nested_prepared input second nested).compare
      firstStart secondStart target positive
    have firstIndex : firstPaid.index = original.leftIndex := by
      rewrite [firstSame]
      rfl
    have secondIndex : secondPaid.index = original.rightIndex := by
      rewrite [secondSame]
      rfl
    exact original.close (firstIndex ▸ firstOrder) (secondIndex ▸ secondOrder)

/-- Supplied original payments preserve the complete original comparison record. -/
private theorem compareNestedFromPaid_readback {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box)
    (firstStart secondStart : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (firstPaid : CoherentRoot.Refinement first (max firstStart 1))
    (firstSame : firstPaid = CoherentRoot.Refinement.ofTarget first (max firstStart 1) (target / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide)))
    (secondPaid : CoherentRoot.Refinement second secondStart)
    (secondSame : secondPaid = CoherentRoot.Refinement.ofTarget second secondStart (target / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide))) :
    first.compareNestedFromPaid input second nested firstStart secondStart target positive
      firstPaid firstSame secondPaid secondSame =
        (first.compare_nested_prepared input second nested).compare firstStart secondStart target positive ∧
      (first.compareNestedFromPaid input second nested firstStart secondStart target positive
        firstPaid firstSame secondPaid secondSame).leftIndex = firstPaid.index ∧
      (first.compareNestedFromPaid input second nested firstStart secondStart target positive
        firstPaid firstSame secondPaid secondSame).rightIndex = secondPaid.index := by
  constructor
  · cases firstSame
    cases secondSame
    rfl
  · exact ⟨rfl, rfl⟩

/-- Supplied original payments preserve the complete original comparison record. -/
theorem compareNestedFromPaid_eq {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box)
    (firstStart secondStart : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (firstPaid : CoherentRoot.Refinement first (max firstStart 1))
    (firstSame : firstPaid = CoherentRoot.Refinement.ofTarget first (max firstStart 1) (target / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide)))
    (secondPaid : CoherentRoot.Refinement second secondStart)
    (secondSame : secondPaid = CoherentRoot.Refinement.ofTarget second secondStart (target / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide))) :
    first.compareNestedFromPaid input second nested firstStart secondStart target positive
      firstPaid firstSame secondPaid secondSame =
        (first.compare_nested_prepared input second nested).compare firstStart secondStart target positive :=
  (compareNestedFromPaid_readback input first second nested firstStart secondStart target positive
    firstPaid firstSame secondPaid secondSame).1

/-- The left comparison index is read from the actual supplied original payment. -/
theorem compareNestedFromPaid_leftIndex {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box)
    (firstStart secondStart : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (firstPaid : CoherentRoot.Refinement first (max firstStart 1))
    (firstSame : firstPaid = CoherentRoot.Refinement.ofTarget first (max firstStart 1) (target / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide)))
    (secondPaid : CoherentRoot.Refinement second secondStart)
    (secondSame : secondPaid = CoherentRoot.Refinement.ofTarget second secondStart (target / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide))) :
    (first.compareNestedFromPaid input second nested firstStart secondStart target positive
      firstPaid firstSame secondPaid secondSame).leftIndex = firstPaid.index :=
  (compareNestedFromPaid_readback input first second nested firstStart secondStart target positive
    firstPaid firstSame secondPaid secondSame).2.1

/-- The right comparison index is read from the actual supplied original payment. -/
theorem compareNestedFromPaid_rightIndex {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box)
    (firstStart secondStart : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (firstPaid : CoherentRoot.Refinement first (max firstStart 1))
    (firstSame : firstPaid = CoherentRoot.Refinement.ofTarget first (max firstStart 1) (target / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide)))
    (secondPaid : CoherentRoot.Refinement second secondStart)
    (secondSame : secondPaid = CoherentRoot.Refinement.ofTarget second secondStart (target / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide))) :
    (first.compareNestedFromPaid input second nested firstStart secondStart target positive
      firstPaid firstSame secondPaid secondSame).rightIndex = secondPaid.index :=
  (compareNestedFromPaid_readback input first second nested firstStart secondStart target positive
    firstPaid firstSame secondPaid secondSame).2.2

/-- The two original coherent channels agree through their actual cached nested-root comparison. -/
def equivalent_nested {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (nested : inner.initial.box.StrictInterior outer.initial.box) :
    Equivalence.NamedEquivalent first.value.name second.value.name := by
  rewrite [first.value_approximation, second.value_approximation]
  exact (first.compare_nested input second nested).toNamed

/-- Compare two retained root programs whose original initial boxes coincide.

Only the second track pays its positive-index state. That actual cached state
initializes one common root cache strictly inside both original boxes. The two
computed nested comparisons share that same cache and compose without reading
any positive-index state of the first track.
-/
def compare_initial {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (same : outer.initial.box = inner.initial.box) :
    Equivalence.Equivalent first.approximation second.approximation :=
  let current := second.stateAt 1
  let common := certifiedName (inner.atState current) second.degreePositive
  have secondNested : current.box.StrictInterior inner.initial.box := by
    dsimp only [current]
    rewrite [second.stateAt_eq]
    exact inner.strict inner.initial _ _
  have firstNested : current.box.StrictInterior outer.initial.box := by
    rewrite [same]
    exact secondNested
  Equivalence.Equivalent.trans (first.compare_nested input common firstNested)
    (Equivalence.Equivalent.symm (second.compare_nested input common secondNested))

/-- Equal original initial boxes identify the two retained coherent root channels.

The comparison consumes the same two root owners and pays only the second
track's initial refinement through the computed common-cache construction.
Neither original owner is replaced by that intermediate root.
-/
def equivalent_initial {polynomial : GaussianPolynomial} {ambient : Box}
    (input : FTA.Squarefree.Input polynomial)
    {outer inner : WindingOneTrack polynomial ambient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (same : outer.initial.box = inner.initial.box) :
    Equivalence.NamedEquivalent first.value.name second.value.name := by
  rewrite [first.value_approximation, second.value_approximation]
  exact (first.compare_initial input second same).toNamed

/-- Transport the original nested cached-root comparison through equal polynomial and ambient indices.

The two original root certificates remain the comparison's inputs. The
supplied equalities identify their mathematical indices; the unchanged
nested comparison pays requests through their same retained sample caches.
An actual retained pair selects the same prepared comparator; absence keeps
the complete original unprepared comparison.
-/
@[expose] def compare_nested_of_eq {firstPolynomial secondPolynomial : GaussianPolynomial}
    {firstAmbient secondAmbient : Box} (input : FTA.Squarefree.Input firstPolynomial)
    {outer : WindingOneTrack firstPolynomial firstAmbient} {inner : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (polynomialEq : secondPolynomial = firstPolynomial) (ambientEq : secondAmbient = firstAmbient)
    (nested : inner.initial.box.StrictInterior outer.initial.box)
    (cached : Option (Refinement.Pair first second) := none) :
    Equivalence.Equivalent first.approximation second.approximation := by
  cases polynomialEq
  cases ambientEq
  exact match cached with
    | none => first.compare_nested input second nested
    | some retained => first.compare_nested_prepared input second nested (some retained)

/-- An absent retained pair preserves the complete original index-transported nested comparison. -/
theorem compare_nested_of_eq_none {firstPolynomial secondPolynomial : GaussianPolynomial}
    {firstAmbient secondAmbient : Box} (input : FTA.Squarefree.Input firstPolynomial)
    {outer : WindingOneTrack firstPolynomial firstAmbient} {inner : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (polynomialEq : secondPolynomial = firstPolynomial) (ambientEq : secondAmbient = firstAmbient)
    (nested : inner.initial.box.StrictInterior outer.initial.box) :
    first.compare_nested_of_eq input second polynomialEq ambientEq nested none = (by
      cases polynomialEq
      cases ambientEq
      exact first.compare_nested input second nested) := by
  cases polynomialEq
  cases ambientEq
  rfl

/-- Equal mathematical indices and original strict nesting identify the same two unchanged numerical root channels. -/
def equivalent_nested_of_eq {firstPolynomial secondPolynomial : GaussianPolynomial}
    {firstAmbient secondAmbient : Box} (input : FTA.Squarefree.Input firstPolynomial)
    {outer : WindingOneTrack firstPolynomial firstAmbient} {inner : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName outer) (second : CertifiedName inner)
    (polynomialEq : secondPolynomial = firstPolynomial) (ambientEq : secondAmbient = firstAmbient)
    (nested : inner.initial.box.StrictInterior outer.initial.box) :
    Equivalence.NamedEquivalent first.value.name second.value.name := by
  cases polynomialEq
  cases ambientEq
  exact first.equivalent_nested input second nested

/-- Present one retained original approximation comparison at the same two original coherent root names. -/
def named_equivalent
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack)
    (comparison : Equivalence.Equivalent first.approximation second.approximation) :
    Equivalence.NamedEquivalent first.value.name second.value.name := by
  rewrite [first.value_approximation, second.value_approximation]
  exact comparison.toNamed true

/-- Recover the actual cached approximation comparison from an original-channel root comparison.

Each root name consumes its retained approximation by its defining equation.
The existing sampler bridges compose with the supplied original name relation;
neither root is reconstructed or replaced by a common owner. A supplied
certified original approximation view is returned literally; its complete
Named conversion must be the same supplied relation.
-/
@[expose] def approximation_equivalent
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack)
    (equivalent : Equivalence.NamedEquivalent first.value.name second.value.name)
    (retained : Option {comparison : Equivalence.Equivalent first.approximation second.approximation //
      first.named_equivalent second comparison = equivalent} := none) :
    Equivalence.Equivalent first.approximation second.approximation :=
  match retained with
  | some comparison => comparison.val
  | none => by
      rewrite [first.value_approximation, second.value_approximation] at equivalent
      exact Equivalence.Equivalent.trans
        (Equivalence.Equivalent.symm (Equivalence.Equivalent.toNamed_sampling first.approximation))
        (Equivalence.Equivalent.trans equivalent (Equivalence.Equivalent.toNamed_sampling second.approximation))

/-- The complete default conversion remains the original two sampler bridges around the supplied name relation. -/
theorem approximation_equivalent_none
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack)
    (equivalent : Equivalence.NamedEquivalent first.value.name second.value.name) :
    first.approximation_equivalent second equivalent none = (by
      rewrite [first.value_approximation, second.value_approximation] at equivalent
      exact Equivalence.Equivalent.trans
        (Equivalence.Equivalent.symm (Equivalence.Equivalent.toNamed_sampling first.approximation))
        (Equivalence.Equivalent.trans equivalent (Equivalence.Equivalent.toNamed_sampling second.approximation))) := rfl

/-- A certified retained approximation view is returned literally, with no sampler round trip. -/
theorem approximation_equivalent_retained
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack)
    (comparison : Equivalence.Equivalent first.approximation second.approximation) :
    first.approximation_equivalent second (first.named_equivalent second comparison)
      (some ⟨comparison, rfl⟩) = comparison := rfl

/-- Every pair of original samples retains the supplied initial-box separation bound.

Both tracks may have different defining polynomials and ambient boxes. Their
own refinement witnesses keep all later samples inside their original initial
boxes, so the actual retained coordinate certificate bounds their distance.
-/
theorem separation_lower
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack)
    (separation : Geometry.Rational.Box.SeparationCertificate firstTrack.initial.box secondTrack.initial.box)
    (firstIndex secondIndex : Nat) :
    separation.gap ^ 2 ≤ normSq (first.approximation.sample firstIndex - second.approximation.sample secondIndex) := by
  have firstInside : firstTrack.initial.box.Contains (first.approximation.sample firstIndex) := by
    rewrite [first.approximation_eq, approximation_sample]
    exact (state_refines_of_le firstTrack (Nat.zero_le firstIndex)).contains
      (state firstTrack firstIndex).box.contains_anchor
  have secondInside : secondTrack.initial.box.Contains (second.approximation.sample secondIndex) := by
    rewrite [second.approximation_eq, approximation_sample]
    exact (state_refines_of_le secondTrack (Nat.zero_le secondIndex)).contains
      (state secondTrack secondIndex).box.contains_anchor
  exact separation.lower firstInside secondInside

/-- A positive initial-box gap certifies that the two original coherent root channels are not equivalent.

The squared retained gap is a positive comparison request. A claimed original
name equivalence would compute actual sample indices below that same gap,
contradicting its quantitative lower bound at those original samples.
-/
theorem not_equivalent_of_separation
    {firstPolynomial secondPolynomial : GaussianPolynomial} {firstAmbient secondAmbient : Box}
    {firstTrack : WindingOneTrack firstPolynomial firstAmbient}
    {secondTrack : WindingOneTrack secondPolynomial secondAmbient}
    (first : CertifiedName firstTrack) (second : CertifiedName secondTrack)
    (separation : Geometry.Rational.Box.SeparationCertificate firstTrack.initial.box secondTrack.initial.box) :
    (Equivalence.NamedEquivalent first.value.name second.value.name → False) := by
  intro equivalent
  let comparison := (first.approximation_equivalent second equivalent).compare 0 0 (separation.gap ^ 2)
    (Order.Arithmetic.pow_pos_direct separation.positive 2)
  have lower := first.separation_lower second separation comparison.leftIndex comparison.rightIndex
  have close := comparison.close (Nat.le_refl comparison.leftIndex) (Nat.le_refl comparison.rightIndex)
  exact (not_lt_of_ge lower) close

end CertifiedName

end Purelib.Riemann.RootContinuation.CoherentRoot

end
