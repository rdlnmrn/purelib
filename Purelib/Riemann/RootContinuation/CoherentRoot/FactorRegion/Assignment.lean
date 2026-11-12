module

public import Purelib.Riemann.RootContinuation.CoherentRoot.FactorRegion
public import Purelib.Riemann.RootContinuation.CoherentRoot.Identification
public import Purelib.RootIsolation.Exact.Partition.Location
public import Purelib.RootIsolation.Exact.Ownership.Radius
public import Purelib.RootIsolation.State.Raw.Interior
public import Purelib.Polynomial.Winding.Box.Region
import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
import Purelib.RootIsolation.State.Raw.FromRegion
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Original factor-channel assignments to retained source partitions -/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.FactorRegion

open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Approximation.Gaussian
open Purelib.Geometry.Rational
open Purelib.Data.Rat

set_option genInjectivity false in
/-- An original factor-root stage assigned to one actual cached owner of a prepared source partition.

The paid ownership request, index and cache read retain the original factor
channel. Its source region and positive winding use that same box, and the
selected bounded index belongs to the original retained source output/cache.
-/
structure Assignment {source factor cofactor : GaussianPolynomial} {factorAmbient sourceAmbient : Box}
    {track : WindingOneTrack factor factorAmbient} {factorRoot : CertifiedName track} {start count : Nat}
    (certificate : FactorRegion factorRoot source cofactor start)
    (output : Exact.Basic.Output source sourceAmbient count) (cache : Family output.tracks) where
  /-- The actual squared ownership-radius request for this original source output. -/
  targetSq : Coordinate
  /-- The request uses the original output and source ambient. -/
  targetSq_eq : targetSq = Exact.Ownership.Radius.assignmentRadius source sourceAmbient output ^ 2
  /-- The original request is positive. -/
  target_positive : 0 < targetSq
  /-- The actual index selected by the original factor refiner after its retained protection stage. -/
  index : Nat
  /-- The original refiner consumes the same retained protection stage and ownership request. -/
  index_eq : index = factorRoot.approximation.refineIndex certificate.index targetSq target_positive
  /-- The assignment follows the same original protected factor stage. -/
  index_ge : certificate.index ≤ index
  /-- The actual original factor state read from its shared cache. -/
  current : WindingOneState factor factorAmbient
  /-- The retained state is the exact original cache read at the assigned stage. -/
  current_eq : current = factorRoot.stateAt index
  /-- The actual original factor state meets this output's ownership budget. -/
  diagonal_lt : current.box.diagonalSq < targetSq
  /-- The source region at this same retained original factor box. -/
  region : Clearance.Box.Region.ClearRegion source sourceAmbient
  /-- The retained source region is precisely the original factor state box. -/
  region_box : region.box = current.box
  /-- The original source has positive unit winding at that same original factor state. -/
  source_winding : Winding.Box.Basic.quadrupledBoxWinding source region.box = 4
  /-- The bounded index of the actual selected original source-output track. -/
  owner : Fin output.tracks.length
  /-- The actual original factor state lies strictly within that same original source owner. -/
  strict : current.box.StrictInterior (output.tracks.get owner).initial.box

constructive_injectivity Assignment

namespace Assignment

/-- Assign an original factor channel using its exact retained ownership refinement.

The payment keeps the original partition radius and sufficient refiner stage.
Its actual state supplies the source region and deterministic partition
location, preserving the original bounded owner and complete assignment.
-/
@[expose] def ofOutputWithRefinement {source factor cofactor : GaussianPolynomial} {factorAmbient sourceAmbient : Box}
    {track : WindingOneTrack factor factorAmbient} {factorRoot : CertifiedName track} {start count : Nat}
    (certificate : FactorRegion factorRoot source cofactor start) (input : FTA.Squarefree.Input source)
    (output : Exact.Basic.Output source sourceAmbient count) (cache : Family output.tracks)
    (supported : track.initial.box.Refines output.support) (paid : Refinement factorRoot certificate.index)
    (request : paid.targetSq = Exact.Ownership.Radius.assignmentRadius source sourceAmbient output ^ 2)
    (maximum : paid.index = paid.maxIndex) : Assignment certificate output cache := by
  let targetSq := paid.targetSq
  have targetPositive : 0 < targetSq := paid.positive
  let index := paid.index
  have indexGe : certificate.index ≤ index := paid.index_ge
  let current := paid.current
  let factorRegion := certificate.regionAtFromState index indexGe current paid.current_eq
  have refined := state_refines_of_le track (Nat.zero_le index)
  rewrite [← factorRoot.stateAt_eq index, ← paid.current_eq] at refined
  have support := refined.trans supported
  let region : Clearance.Box.Region.ClearRegion source sourceAmbient :=
    { box := current.box
      refinesAmbient := support.trans output.support_refinesAmbient
      proper := current.proper
      clearance := factorRegion.clearance }
  have winding : Winding.Box.Basic.quadrupledBoxWinding source region.box = 4 :=
    certificate.regionAtFromState_winding index indexGe current paid.current_eq
  have windingPositive : 0 < Winding.Box.Basic.quadrupledBoxWinding source region.box := by
    rewrite [winding]
    decide
  have windingNonzero : Winding.Box.Basic.quadrupledBoxWinding source region.box ≠ 0 := by
    intro zero
    have impossible := windingPositive
    rewrite [zero] at impossible
    exact (by decide : ¬ (0 : Int) < 0) impossible
  let raw := region.raw windingNonzero
  have diagonal := paid.diagonal_lt.trans_eq request
  let location := Exact.Partition.Location.locatePartition output current.box.anchor
    (support.contains current.box.contains_anchor)
  have inside : location.box.Contains current.box.anchor :=
    Exact.Partition.Location.locatePartition_contains output current.box.anchor
    (support.contains current.box.contains_anchor)
  cases locationEq : location with
  | track owner =>
      have anchorInside : (output.tracks.get owner).initial.box.Contains current.box.anchor := by
        rewrite [locationEq] at inside
        exact inside
      have strict := State.Raw.Interior.strictInterior_of_anchor_mem_of_dominates source raw input.degreePositive
        (output.tracks.get owner).initial.refinesAmbient (output.tracks.get owner).initial.clearance anchorInside
        (Exact.Ownership.Radius.assignment_dominates source sourceAmbient output current.box diagonal.le
          (Exact.Partition.Margin.partitionMargin_le_track output owner))
      exact
        { targetSq := targetSq
          targetSq_eq := request
          target_positive := targetPositive
          index := index
          index_eq := maximum.trans paid.maxIndex_eq
          index_ge := indexGe
          current := current
          current_eq := paid.current_eq
          diagonal_lt := paid.diagonal_lt
          region := region
          region_box := rfl
          source_winding := winding
          owner := owner
          strict := strict }
  | remainder index =>
      let remainder := output.remainder.get index
      have anchorInside : remainder.box.Contains current.box.anchor := by
        rewrite [locationEq] at inside
        exact inside
      have strict := State.Raw.Interior.strictInterior_of_anchor_mem_of_dominates source raw input.degreePositive
        remainder.refinesAmbient remainder.clearance anchorInside
        (Exact.Ownership.Radius.assignment_dominates source sourceAmbient output current.box diagonal.le
          (Exact.Partition.Margin.partitionMargin_le_remainder output index))
      have four := Winding.Box.Region.winding_ge_four_of_positive_region input remainder region windingPositive
        (Box.Refinement.StrictInterior.refines strict)
      have zero := output.remainder_rawWinding_zero remainder (List.get_mem output.remainder index)
      rewrite [zero] at four
      exact ((by decide : ¬ (4 : Int) ≤ 0) four).elim

/-- Assign a supported original factor-root channel to its source output using a computed ownership request.

The actual original sample anchor selects a finite partition location. Source
winding one excludes a zero-winding remainder, while the same scalar ownership
budget proves strict containment in the selected original source track.
-/
@[expose] def ofOutput {source factor cofactor : GaussianPolynomial} {factorAmbient sourceAmbient : Box}
    {track : WindingOneTrack factor factorAmbient} {factorRoot : CertifiedName track} {start count : Nat}
    (certificate : FactorRegion factorRoot source cofactor start) (input : FTA.Squarefree.Input source)
    (output : Exact.Basic.Output source sourceAmbient count) (cache : Family output.tracks)
    (supported : track.initial.box.Refines output.support) : Assignment certificate output cache := by
  let targetSq := Exact.Ownership.Radius.assignmentRadius source sourceAmbient output ^ 2
  have targetPositive : 0 < targetSq := Fraction.Order.Arithmetic.pow_pos_direct
    (Exact.Ownership.Radius.assignmentRadius_pos source sourceAmbient output) 2
  let index := factorRoot.approximation.refineIndex certificate.index targetSq targetPositive
  have indexGe : certificate.index ≤ index := factorRoot.approximation.refineIndex_ge _ _ _
  let current := factorRoot.stateAt index
  have diagonal := factorRoot.stateAt_refineIndex_diagonal_lt certificate.index targetSq targetPositive
  exact ofOutputWithRefinement certificate input output cache supported
    (Refinement.atState factorRoot certificate.index targetSq targetPositive index rfl index indexGe
      (Nat.le_refl index) current rfl diagonal) rfl rfl

/-- The exact retained ownership payment preserves the whole original source assignment.

The requested radius, protected starting stage, actual state, source region,
selected owner and strict containment agree with the default constructor.
-/
theorem ofOutputWithRefinement_eq {source factor cofactor : GaussianPolynomial}
    {factorAmbient sourceAmbient : Box} {track : WindingOneTrack factor factorAmbient}
    {factorRoot : CertifiedName track} {start count : Nat}
    (certificate : FactorRegion factorRoot source cofactor start) (input : FTA.Squarefree.Input source)
    (output : Exact.Basic.Output source sourceAmbient count) (cache : Family output.tracks)
    (supported : track.initial.box.Refines output.support)
    (paid : Refinement factorRoot certificate.index)
    (request : paid.targetSq = Exact.Ownership.Radius.assignmentRadius source sourceAmbient output ^ 2)
    (maximum : paid.index = paid.maxIndex) :
    ofOutputWithRefinement certificate input output cache supported paid request maximum =
      ofOutput certificate input output cache supported := by
  rcases paid with ⟨target, positive, index, maxIndex, maxEq, indexLe, indexGe, current, currentEq, diagonal⟩
  dsimp only [] at request maximum
  cases request
  cases maxEq
  cases maximum
  cases currentEq
  rfl

/-- Restore the complete original assignment from one exact ownership-stage state read.

The original partition computes the same ownership radius and maximum stage.
Its actual supplied state drives both the source region and owner selection;
a reader failure stops the construction without a default refinement.
-/
def ofOutputWithStates {m : Type → Type} [Monad m] {source factor cofactor : GaussianPolynomial}
    {factorAmbient sourceAmbient : Box} {track : WindingOneTrack factor factorAmbient}
    {factorRoot : CertifiedName track} {start count : Nat}
    (certificate : FactorRegion factorRoot source cofactor start) (input : FTA.Squarefree.Input source)
    (output : Exact.Basic.Output source sourceAmbient count) (cache : Family output.tracks)
    (supported : track.initial.box.Refines output.support)
    (states : (index : Nat) → m {current : WindingOneState factor factorAmbient //
      current = factorRoot.stateAt index}) :
    m {assignment : Assignment certificate output cache //
      assignment = ofOutput certificate input output cache supported} := do
  let targetSq := Exact.Ownership.Radius.assignmentRadius source sourceAmbient output ^ 2
  have positive := Fraction.Order.Arithmetic.pow_pos_direct
    (Exact.Ownership.Radius.assignmentRadius_pos source sourceAmbient output) 2
  let index := factorRoot.approximation.refineIndex certificate.index targetSq positive
  let current ← states index
  have accurate : current.val.box.diagonalSq < targetSq := by
    rewrite [current.property]
    exact factorRoot.stateAt_refineIndex_diagonal_lt certificate.index targetSq positive
  let paid := Refinement.atState factorRoot certificate.index targetSq positive index rfl index
    (factorRoot.approximation.refineIndex_ge certificate.index targetSq positive) (Nat.le_refl index)
    current.val current.property accurate
  return ⟨ofOutputWithRefinement certificate input output cache supported paid rfl rfl,
    ofOutputWithRefinement_eq certificate input output cache supported paid rfl rfl⟩

/-- Compare the original factor channel with the same actual cached source owner selected at its retained stage. -/
def equivalent {source factor cofactor : GaussianPolynomial} {factorAmbient sourceAmbient : Box}
    {track : WindingOneTrack factor factorAmbient} {factorRoot : CertifiedName track} {start count : Nat}
    {certificate : FactorRegion factorRoot source cofactor start}
    {output : Exact.Basic.Output source sourceAmbient count} {cache : Family output.tracks}
    (assignment : Assignment certificate output cache) (input : FTA.Squarefree.Input source) :
    Equivalence.NamedEquivalent factorRoot.value.name (cache.get assignment.owner).value.name := by
  let owner := cache.get assignment.owner
  let container : Clearance.Box.Region.ClearRegion source sourceAmbient :=
    { box := (output.tracks.get assignment.owner).initial.box
      refinesAmbient := (output.tracks.get assignment.owner).initial.refinesAmbient
      proper := (output.tracks.get assignment.owner).initial.proper
      clearance := (output.tracks.get assignment.owner).initial.clearance }
  have nested : (factorRoot.stateAt assignment.index).box.Refines container.box := by
    rewrite [← assignment.current_eq]
    exact Box.Refinement.StrictInterior.refines assignment.strict
  let comparison := certificate.compare_in_region input owner container
    (output.tracks.get assignment.owner).initial.rawWindingFour (Box.refines_refl _)
    assignment.index assignment.index_ge nested
  have equivalent : Equivalence.NamedEquivalent owner.value.name factorRoot.value.name := by
    rewrite [owner.value_approximation, factorRoot.value_approximation]
    exact comparison.toNamed
  exact equivalent.symm

/-- Equal source-owner indices compare both original factor channels through the same retained source cache. -/
def sameOwner {source firstFactor firstCofactor secondFactor secondCofactor : GaussianPolynomial}
    {firstAmbient secondAmbient sourceAmbient : Box}
    {firstTrack : WindingOneTrack firstFactor firstAmbient} {secondTrack : WindingOneTrack secondFactor secondAmbient}
    {firstRoot : CertifiedName firstTrack} {secondRoot : CertifiedName secondTrack} {firstStart secondStart count : Nat}
    {firstCertificate : FactorRegion firstRoot source firstCofactor firstStart}
    {secondCertificate : FactorRegion secondRoot source secondCofactor secondStart}
    {output : Exact.Basic.Output source sourceAmbient count} {cache : Family output.tracks}
    (first : Assignment firstCertificate output cache) (second : Assignment secondCertificate output cache)
    (input : FTA.Squarefree.Input source) (same : first.owner = second.owner) :
    Equivalence.NamedEquivalent firstRoot.value.name secondRoot.value.name := by
  have compared := first.equivalent input
  rewrite [same] at compared
  exact compared.trans (second.equivalent input).symm

/-- Distinct source-owner indices supply a computed positive gap between the actual original factor-root cache stages.

The selected source-owner boxes are separated in the same retained partition.
Each original factor state lies strictly inside its selected owner. Their
actual cache-read boxes therefore have a positive gap, paid by their respective
original protection and ownership requests.
-/
@[expose] def distinguish {source firstFactor firstCofactor secondFactor secondCofactor : GaussianPolynomial}
    {firstAmbient secondAmbient sourceAmbient : Box}
    {firstTrack : WindingOneTrack firstFactor firstAmbient} {secondTrack : WindingOneTrack secondFactor secondAmbient}
    {firstRoot : CertifiedName firstTrack} {secondRoot : CertifiedName secondTrack} {firstStart secondStart count : Nat}
    {firstCertificate : FactorRegion firstRoot source firstCofactor firstStart}
    {secondCertificate : FactorRegion secondRoot source secondCofactor secondStart}
    {output : Exact.Basic.Output source sourceAmbient count} {cache : Family output.tracks}
    (first : Assignment firstCertificate output cache) (second : Assignment secondCertificate output cache)
    (different : first.owner ≠ second.owner) : PairSeparation firstRoot secondRoot firstStart secondStart :=
  let separated := (output.tracks_get_separated first.owner second.owner different).of_refines
    (Box.Refinement.StrictInterior.refines first.strict) (Box.Refinement.StrictInterior.refines second.strict)
  { leftTargetSq := first.targetSq
    leftTarget_positive := first.target_positive
    rightTargetSq := second.targetSq
    rightTarget_positive := second.target_positive
    leftRequestStart := firstCertificate.index
    leftRequest_ge := firstCertificate.index_ge
    rightRequestStart := secondCertificate.index
    rightRequest_ge := secondCertificate.index_ge
    leftIndex := first.index
    rightIndex := second.index
    leftIndex_eq := first.index_eq
    rightIndex_eq := second.index_eq
    left_ge := firstCertificate.index_ge.trans first.index_ge
    right_ge := secondCertificate.index_ge.trans second.index_ge
    leftState := first.current
    rightState := second.current
    leftState_eq := first.current_eq
    rightState_eq := second.current_eq
    left_diagonal_lt := first.diagonal_lt
    right_diagonal_lt := second.diagonal_lt
    separation := Box.separationCertificate separated }

set_option genInjectivity false in
/-- A checked original-channel equality or positive original-stage gap for two retained source assignments. -/
inductive Comparison {source firstFactor firstCofactor secondFactor secondCofactor : GaussianPolynomial}
    {firstAmbient secondAmbient sourceAmbient : Box}
    {firstTrack : WindingOneTrack firstFactor firstAmbient} {secondTrack : WindingOneTrack secondFactor secondAmbient}
    {firstRoot : CertifiedName firstTrack} {secondRoot : CertifiedName secondTrack} {firstStart secondStart count : Nat}
    {firstCertificate : FactorRegion firstRoot source firstCofactor firstStart}
    {secondCertificate : FactorRegion secondRoot source secondCofactor secondStart}
    {output : Exact.Basic.Output source sourceAmbient count} {cache : Family output.tracks}
    (first : Assignment firstCertificate output cache) (second : Assignment secondCertificate output cache) :
    Type 1 where
  /-- The retained owner indices coincide and both original channels agree. -/
  | equal (same : first.owner = second.owner)
      (equivalent : Equivalence.NamedEquivalent firstRoot.value.name secondRoot.value.name)
  /-- The retained owner indices differ and the two actual original sample stages are positively separated. -/
  | distinct (different : first.owner ≠ second.owner)
      (separation : PairSeparation firstRoot secondRoot firstStart secondStart)

constructive_injectivity Comparison

/-- Decide the two retained owner indices and return equality or quantitative separation at the original channels. -/
@[expose] def compare {source firstFactor firstCofactor secondFactor secondCofactor : GaussianPolynomial}
    {firstAmbient secondAmbient sourceAmbient : Box}
    {firstTrack : WindingOneTrack firstFactor firstAmbient} {secondTrack : WindingOneTrack secondFactor secondAmbient}
    {firstRoot : CertifiedName firstTrack} {secondRoot : CertifiedName secondTrack} {firstStart secondStart count : Nat}
    {firstCertificate : FactorRegion firstRoot source firstCofactor firstStart}
    {secondCertificate : FactorRegion secondRoot source secondCofactor secondStart}
    {output : Exact.Basic.Output source sourceAmbient count} {cache : Family output.tracks}
    (first : Assignment firstCertificate output cache) (second : Assignment secondCertificate output cache)
    (input : FTA.Squarefree.Input source) : Comparison first second :=
  if same : first.owner = second.owner then
    .equal same (first.sameOwner second input same)
  else
    .distinct same (first.distinguish second same)

end Assignment

end Purelib.Riemann.RootContinuation.CoherentRoot.FactorRegion

end
