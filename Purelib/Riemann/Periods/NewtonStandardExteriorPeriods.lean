module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoExteriorBudget
import Purelib.Tactic.Ring
public import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth
import Purelib.Data.List.Flatten
open Purelib.Data.List

@[expose] public section

/-! The retained Newton exterior pays the original weighted A/B exterior
rows on the same triangle bank as its full-area comparison. -/
namespace Purelib.Riemann.Periods.NewtonStandardExteriorPeriods

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth (ExteriorSourceRequest)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder (ComponentCanonicalPeriodBound)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceComponent)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (PhysicalLoopSplit)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest (Readings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Topology.Surface.Sewing.SewingRetraction in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- The total of paired edge increments is the pair of their two original word values. -/
private theorem paired_word_total {count : Nat} (left right : OrientedEdge count → Gaussian.Basic.Canonical)
    (word : List (OrientedEdge count)) :
    Path.PairedIncrementArea.total (word.map (fun edge => (⟨left edge, right edge⟩ : PrimitivePoint))) =
      (⟨wordValue left word, wordValue right word⟩ : PrimitivePoint) := by
  apply congrArg₂ PrimitivePoint.mk
  · rw [Map.map_map]
    exact Mesh.RetracingWords.sum_map_eq_wordValue left word
  · rw [Map.map_map]
    exact Mesh.RetracingWords.sum_map_eq_wordValue right word

open Purelib.Topology.Surface.Sewing.SewingRetraction in
open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
/-- The sum of actual exterior component word values is the original flattened exterior boundary value.

The retained ordered occurrence and index readbacks identify the sum without discarding repeated edges or their
orientations. -/
private theorem component_words_sum
    {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
      Hyperelliptic.Branches.BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {lifted : LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
    {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
      Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
    {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    (prepared :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains differential)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.components.map (fun component => wordValue value
      component.program.indexed)) =
      wordValue value lifted.exteriorBoundaries.flatten := by
  have sum (components : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
    regular domains differential)) :
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (components.map (fun component => wordValue value
        component.program.indexed)) =
        wordValue value ((components.flatMap (fun component => component.prepared.occurrences)).map
          (fun occurrence => occurrence.placement.indexed)) := by
    induction components with
    | nil => rfl
    | cons head tail ih =>
        rw [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, Flatten.flatMap_cons, Map.map_append,
          Surface.Sewing.SewingRetraction.wordValue_append,
          head.prepared.occurrences_eq, ih]
  exact (sum prepared.components).trans
    ((congrArg (fun occurrences => wordValue value (occurrences.map (fun occurrence => occurrence.placement.indexed)))
      prepared.occurrences_eq.symm).trans (congrArg (wordValue value) prepared.indexed_eq))

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {first second : Fin genus}
  {target radius : Rational} {floor : Nat}

section
open Purelib.Approximation
open Purelib.Data
/-- Allocate a quarter of the count-paid per-component allowance before exterior requests are acquired. -/
def ExteriorPeriodAllowance (prepared : BoundaryPreparation preparation first second target radius floor)
    (requested : Rat.Fraction.Rational) : Rat.Fraction.Rational :=
  Rational.Budget.Aggregate.perTerm requested prepared.exterior.prepared.components.length / 4

/-- A positive exterior target gives a positive per-component allowance. -/
theorem exteriorPeriodAllowance_positive
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {requested : Rat.Fraction.Rational} (positive : 0 < requested) : 0 < ExteriorPeriodAllowance prepared requested :=
  Rat.Fraction.Order.Field.div_pos_direct (Rational.Budget.Aggregate.perTerm_positive positive _) (by decide)

end

open Purelib.Topology.Surface.Sewing.SewingRetraction in
open Purelib.Curves in
open Purelib.Data in
/-- Both retained differential readings of the actual flattened exterior boundary are strictly below the squared-error
target. -/
def ExteriorBoundaryPeriodsSmall
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {index : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
      prepared.domains index}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut
      cache) (requested : Rat.Fraction.Rational) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (wordValue (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
    prepared.lifted.mesh readings.left.values)
    prepared.lifted.exteriorBoundaries.flatten) < requested ∧
  Data.Gaussian.Norm.Basic.normSq (wordValue (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
    prepared.lifted.mesh readings.right.values)
    prepared.lifted.exteriorBoundaries.flatten) < requested

open Purelib.Topology.Surface.Sewing.SewingRetraction in
open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Approximation in
open Purelib.Data in
/-- Pay both original exterior boundary values using the actual retained components.

The source and endpoint requests share the refined depth and supplied numerical bank; their stage floors and count-paid
allowances give a strict aggregate target. -/
theorem ExteriorSourceRequest.boundary_periods_small
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {requested : Rat.Fraction.Rational} (positive : 0 < requested) {minimum : Nat}
    (result : ExteriorSourceRequest prepared (ExteriorPeriodAllowance prepared requested) minimum)
    (endpoints :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.SideRemainderRequest
      (RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
        result.depth).exterior.prepared (RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth
        prepared result.depth).paid.cut.fixed first second
      (ExteriorPeriodAllowance prepared requested))
    {index : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
      prepared.domains index}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings
      (RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).paid.cut cache)
    (later : result.index ≤ index) (endpointLater : endpoints.endpoints.index ≤ index) :
    ExteriorBoundaryPeriodsSmall (RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
      result.depth) readings requested := by
  let refined := RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth
  let left := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation refined.lifted.mesh
    readings.left.values
  let right := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation refined.lifted.mesh
    readings.right.values
  let allowance := Rational.Budget.Aggregate.perTerm requested prepared.exterior.prepared.components.length
  have paid : 2 * (ExteriorPeriodAllowance prepared requested + ExteriorPeriodAllowance prepared requested) = allowance
    := by
    change 2 * (allowance / 4 + allowance / 4) = allowance
    exact (by ring1 : 2 * (allowance / 4 + allowance / 4) = (allowance / 4) * 4).trans
      (Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  have each (i : Fin prepared.exterior.prepared.components.length) :
      Data.Gaussian.Norm.Basic.normSq (wordValue left
        (prepared.exterior.prepared.components[i.val]'i.isLt).program.indexed) ≤ allowance ∧
      Data.Gaussian.Norm.Basic.normSq (wordValue right
        (prepared.exterior.prepared.components[i.val]'i.isLt).program.indexed) ≤ allowance := by
    have bound := RootContinuation.NewtonRequestedExteriorRemainder.ExteriorSourceRequest.canonical_period_bound
      prepared result i endpoints readings later endpointLater
    unfold ComponentCanonicalPeriodBound at bound
    rw [paired_word_total, paid] at bound
    change Gaussian.Basic.Canonical.normSq
        (wordValue left (prepared.exterior.prepared.components[i.val]'i.isLt).program.indexed) ≤ allowance ∧
      Gaussian.Basic.Canonical.normSq
        (wordValue right (prepared.exterior.prepared.components[i.val]'i.isLt).program.indexed) ≤ allowance at bound
    constructor
    · rw [Gaussian.Norm.Basic.normSq_eq_canonical]
      exact bound.1
    · rw [Gaussian.Norm.Basic.normSq_eq_canonical]
      exact bound.2
  have aggregate (value : OrientedEdge prepared.lifted.vertices.count → Gaussian.Basic.Canonical)
      (bounded : ∀ i : Fin prepared.exterior.prepared.components.length,
        Data.Gaussian.Norm.Basic.normSq (wordValue value
          (prepared.exterior.prepared.components[i.val]'i.isLt).program.indexed) ≤ allowance) :
      Data.Gaussian.Norm.Basic.normSq (wordValue value prepared.lifted.exteriorBoundaries.flatten) < requested := by
    have bound := Gaussian.Norm.Sum.Bounds.normSq_sum_le
      (prepared.exterior.prepared.components.map (fun component => wordValue value component.program.indexed)) allowance
        (by
        intro value member
        obtain ⟨component, inComponents, rfl⟩ := List.Map.mem_map.mp member
        obtain ⟨i, inRange, equal⟩ := List.getElem_of_mem inComponents
        exact equal ▸ bounded ⟨i, inRange⟩)
    rw [Map.length_map, component_words_sum] at bound
    exact bound.trans_lt (Rational.Budget.Aggregate.count_mul_perTerm_lt positive _)
  exact ⟨aggregate left (fun i => (each i).1), aggregate right (fun i => (each i).2)⟩

open Purelib.Topology.Surface.Sewing.SewingRetraction in
open Purelib.Curves in
open Purelib.Data in
/-- All four weighted A/B exterior readings satisfy the quarter-target bound.

The two differentials use the same retained bank, while the A and B rows retain their original signed coefficients and
exterior words. -/
def WeightedExteriorPeriodsSmall
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {aRows bRows : List (Int × List (OrientedEdge prepared.lifted.vertices.count))}
    (a : Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit prepared.lifted aRows) (b :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit prepared.lifted bRows)
    {index : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
      prepared.domains index}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings prepared.paid.cut
      cache) (requested : Rat.Fraction.Rational) : Prop :=
  let left := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh
    readings.left.values
  let right := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation prepared.lifted.mesh
    readings.right.values
  (Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (a.exterior.map (fun entry => (entry.1
    : Gaussian.Basic.Canonical) * wordValue left entry.2))) < requested / 4 ∧
   Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (b.exterior.map (fun entry => (entry.1
     : Gaussian.Basic.Canonical) * wordValue left entry.2))) < requested / 4) ∧
  (Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (a.exterior.map (fun entry => (entry.1
    : Gaussian.Basic.Canonical) * wordValue right entry.2))) < requested / 4 ∧
   Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (b.exterior.map (fun entry => (entry.1
     : Gaussian.Basic.Canonical) * wordValue right entry.2))) < requested / 4)

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
/-- Pay both differentials' weighted A/B exterior periods on the retained triangle bank.

The existing two-exterior coefficient budget and origin-order-one evidence transport the actual exterior boundary
estimates to all four original weighted rows. -/
theorem ExteriorSourceRequest.weighted_periods_small
    (prepared : BoundaryPreparation preparation first second target radius floor)
    {aRows bRows : List (Int × List (OrientedEdge prepared.lifted.vertices.count))}
    {a : Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit prepared.lifted aRows} {b :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopSplit prepared.lifted bRows}
    {requested : Rat.Fraction.Rational} (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoExteriorBudget
      a b requested)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) {minimum : Nat}
    (result : ExteriorSourceRequest prepared (ExteriorPeriodAllowance prepared budget.allowance) minimum)
    (endpoints :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.SideRemainderRequest
      (RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
        result.depth).exterior.prepared (RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth
        prepared result.depth).paid.cut.fixed first second
      (ExteriorPeriodAllowance prepared budget.allowance))
    {index : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
      prepared.domains index}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings
      (RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared result.depth).paid.cut cache)
    (later : result.index ≤ index) (endpointLater : endpoints.endpoints.index ≤ index) :
    WeightedExteriorPeriodsSmall (RootContinuation.NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth prepared
      result.depth) a b readings requested := by
  have small := ExteriorSourceRequest.boundary_periods_small
    prepared budget.positive result endpoints readings later endpointLater
  exact ⟨budget.accurate branch _ small.1, budget.accurate branch _ small.2⟩

end Purelib.Riemann.Periods.NewtonStandardExteriorPeriods

