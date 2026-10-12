module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemRequests
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemRequests

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Topology.Mesh.RetracingWords

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-! One finite request pays all actual stem defects in the corrected
ordered boundary identity, including the odd/even terminal excursions. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea (PairedRows CommonLoop)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs (EndingTours PairEnding)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemRequests (StemRequest)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Topology.Mesh.RetracingWords.AreaTerm (total)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
  {domains : FaceDomainBank lifted.frames
    base.faces.regulars} {differential : Differential genus}

namespace Paired.BranchArea.PairedRows

variable {reference : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {sheet : Fin 2}

/-- The ordered branch and opposite-sheet labels of all retained paired rows. -/
def stemLabels : {labels : List
  (BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches)} →
    {prior : BranchArea.CommonLoop lifted sheet} → BranchArea.PairedRows bank reference sheet labels prior → List
      (BranchIsolation.Data.Index branches × Fin 2)
  | _, _, .nil _ => []
  | _, _, .cons (labels := labels) _ tail => (labels.1, sheet) :: (labels.2, BranchCutLifts.otherSheet sheet) ::
    stemLabels tail

/-- The paired-row stem error is exactly the ordered sum of its retained labelled stem errors. -/
theorem stemErrors_eq (value :
  Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical) :
    ∀ {labels : List (BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches)} {prior :
      BranchArea.CommonLoop lifted sheet}
      (rows : BranchArea.PairedRows bank reference sheet labels prior),
      rows.stemErrors value = Data.Gaussian.Norm.Sum.Basic.gaussianSum (rows.stemLabels.map (fun entry =>
        bank.stemError value entry.1 entry.2))
  | _, _, .nil _ => rfl
  | _, _, .cons _ tail => by
      change _ + _ + tail.stemErrors value = _ + (_ + _)
      rw [stemErrors_eq value tail]
      ring1

end Paired.BranchArea.PairedRows

namespace OrderedBranchPairs.EndingTours

variable {sheet : Fin 2}

/-- The original branch-and-sheet labels of the odd or even terminal excursions. -/
def stemLabels : {ending :
  OrderedBranchPairs.PairEnding (BranchIsolation.Data.Index branches)} →
    OrderedBranchPairs.EndingTours bank sheet ending → List (BranchIsolation.Data.Index branches × Fin 2)
  | _, .odd index _ => [(index, sheet)]
  | _, .even index last _ _ => [(index, sheet), (last, BranchCutLifts.otherSheet sheet)]

/-- The terminal stem error is the sum over its exact retained branch-and-sheet labels. -/
theorem stemErrors_eq (value :
  Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    {ending : OrderedBranchPairs.PairEnding (BranchIsolation.Data.Index branches)} (tours :
      OrderedBranchPairs.EndingTours bank sheet ending) :
    tours.stemErrors value = Data.Gaussian.Norm.Sum.Basic.gaussianSum (tours.stemLabels.map (fun entry =>
      bank.stemError value entry.1 entry.2)) := by
  cases tours <;> simp only [EndingTours.stemErrors,
    stemLabels, List.map_cons, List.map_nil,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum] <;> ring1

end OrderedBranchPairs.EndingTours

namespace Paired.StemAggregate

set_option genInjectivity false in
/-- The ordered request bank for all corrected branch stems at one common allowance. -/
inductive StemRequests (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (fixed :
  MagnitudeBank.FaceMagnitudeBank
  domains differential) (target : Fraction.Rational) :
    List (BranchIsolation.Data.Index branches × Fin 2) → Type 2 where
  /-- The empty corrected-stem request bank. -/ | nil :
    StemRequests bank fixed target []
  /-- Extend the bank with the actual request for its first branch and sheet. -/ | cons {entry entries} (head :
    StemRequests.StemRequest bank fixed entry.1 entry.2 target)
      (tail : StemRequests bank fixed target
        entries) : StemRequests bank fixed target
        (entry :: entries)

constructive_injectivity StemRequests

end Paired.StemAggregate

namespace Paired.StemAggregate.StemRequests

variable {fixed : FaceMagnitudeBank domains
  differential} {target : Rational}

/-- Prepare each retained branch-and-sheet stem request in its original order. -/
def build (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (fixed : MagnitudeBank.FaceMagnitudeBank domains
  differential)
    (target : Fraction.Rational) (positive : 0 < target) :
    (entries : List (BranchIsolation.Data.Index branches × Fin 2)) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAggregate.StemRequests bank fixed target entries
  | [] => .nil
  | entry :: entries => .cons (StemRequest.build bank fixed entry.1 entry.2 target positive)
    (build bank fixed target
    positive entries)

/-- The common stage paying every retained stem request, or zero for an empty bank. -/
def index : {entries : List (BranchIsolation.Data.Index branches × Fin 2)} →
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAggregate.StemRequests bank fixed target entries → Nat
  | _, .nil => 0
  | _, .cons head tail => max head.index tail.index

/-- At the paid common stage, every retained stem error obeys the shared allowance. -/
theorem accurate {entries : List (BranchIsolation.Data.Index branches × Fin 2)} (requests :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAggregate.StemRequests bank fixed target entries)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (later : requests.index ≤ stage) :
    ∀ entry ∈ entries, Data.Gaussian.Norm.Basic.normSq (bank.stemError (CanonicalEdgeValues.edgeValuation
      lifted.mesh readings.values) entry.1 entry.2) ≤ target := by
  induction requests with
  | nil => intro entry member; exact (List.not_mem_nil member).elim
  | cons head tail ih =>
      intro entry member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · have h := head.accurate readings ((Data.Nat.Order.le_max_left _ _).trans later)
        change Fraction.Order.Basic.LessEqual _ _ at h
        change Fraction.Order.Basic.LessEqual _ _
        simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
      · exact ih ((Data.Nat.Order.le_max_right _ _).trans later) entry member

end Paired.StemAggregate.StemRequests

namespace Paired

variable {sheet : Fin 2} {ordered :
  Ordered bank
  sheet} {paired : Paired ordered}

namespace PeriodPrograms.Prepared

/-- The complete ordered paired-row and terminal stem labels. -/
def stemLabels (_prepared :
  PeriodPrograms.Prepared paired) : List (BranchIsolation.Data.Index branches × Fin 2) :=
  paired.rows.stemLabels ++ paired.ending.stemLabels

end PeriodPrograms.Prepared

namespace StemAggregate.Prepared

set_option genInjectivity false in
/-- A finite request paying every corrected stem defect, including terminal excursions.

The retained label list preserves multiplicity and sheet choices, and its aggregate allowance determines the actual
per-stem requests. -/
structure StemAggregateRequest (prepared : PeriodPrograms.Prepared paired) (fixed
  : MagnitudeBank.FaceMagnitudeBank
  domains differential) (target : Fraction.Rational) where
  /-- The aggregate squared-norm target is strictly positive. -/ positive : 0 < target
  /-- The cached complete branch-and-sheet label list. -/ labels : List (BranchIsolation.Data.Index branches × Fin 2)
  /-- The label cache contains exactly the retained paired rows and terminal excursions. -/ labels_eq : labels =
    prepared.stemLabels
  /-- The shared per-stem squared-norm allowance. -/ allowance : Fraction.Rational
  /-- The allowance is the aggregate target's finite-count share. -/ allowance_eq : allowance = Aggregate.perTerm target
    labels.length
  /-- The actual ordered stem requests at the retained allowance. -/ requests :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAggregate.StemRequests bank fixed allowance labels
  /-- The common stage paying every retained stem request, or zero for an empty bank. -/ index : Nat
  /-- The cached common stage is the retained request bank's stage. -/ index_eq : index = requests.index

constructive_injectivity StemAggregateRequest

end StemAggregate.Prepared

namespace StemAggregate.Prepared.StemAggregateRequest

variable {prepared : Prepared paired} {fixed :
  FaceMagnitudeBank domains differential} {target :
  Rational}

/-- Allocate the aggregate allowance across the complete retained label list and cache its common request stage. -/
def build (prepared : PeriodPrograms.Prepared paired) (fixed : MagnitudeBank.FaceMagnitudeBank domains differential)
    (target : Fraction.Rational) (positive : 0 < target) :
      StemAggregateRequest
      prepared fixed target :=
  let labels := prepared.stemLabels
  let allowance := Aggregate.perTerm target labels.length
  let requests := Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAggregate.StemRequests.build bank fixed allowance
    (Aggregate.perTerm_positive positive _) labels
  ⟨positive, labels, rfl, allowance, rfl, requests, requests.index, rfl⟩

/-- Both the paired rows and the terminal excursions are paid. No caller supplies a stem-area, endpoint, chart-change,
or magnitude inequality. -/
theorem accurate (request :
  StemAggregateRequest prepared
  fixed target)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (paired.rows.stemErrors (CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.values) +
      paired.ending.stemErrors (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)) < target := by
  rw [paired.rows.stemErrors_eq, paired.ending.stemErrors_eq, ← IncrementArea.sum_append, ← Data.List.Map.map_append]
  change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (prepared.stemLabels.map _)) < target
  rw [← request.labels_eq]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ request.positive
  intro value member
  obtain ⟨entry, inLabels, equal⟩ := Map.mem_map.mp member
  rw [← equal, Data.List.Map.length_map]
  have bound := request.requests.accurate readings (request.index_eq ▸ later) entry inLabels
  rw [request.allowance_eq] at bound
  exact bound

/-- The corrected surface residual now loses all stems at a requested cost. Physical hole areas, their cross term,
exterior terms, and regular face terms remain explicit and are not claimed small by this theorem. -/
theorem surface_accurate (request :
  StemAggregateRequest prepared
  fixed target)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (later : request.index ≤ stage) :
    let value := CanonicalEdgeValues.edgeValuation lifted.mesh readings.values
    Data.Gaussian.Norm.Basic.normSq (BilinearIdentity.surfaceResidual prepared value -
      ((paired.rows.holeAreas value + paired.ending.holeAreas value) +
        BoundaryRibbon.area (SewingRetraction.wordValue value paired.rows.word)
          (-SewingRetraction.wordValue value (paired.reference.hole.liftedBoundary lifted.vertices lifted.edges)) +
        paired.ending.exteriorArea value (SewingRetraction.wordValue value paired.rows.word) +
        AreaTerm.total value ordered.prepared.compiled.areaTerms -
        lifted.edges.chainArea lifted.vertices value base.bank.exterior sheet)) < target := by
  dsimp only
  rw [prepared.surfaceResidual_split]
  convert request.accurate readings later using 1
  congr 1
  ring1

end StemAggregate.Prepared.StemAggregateRequest
end Paired
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
