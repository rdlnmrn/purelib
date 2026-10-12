module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.SquareRoot.Grid.Walk
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
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
public import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.CircuitSewing
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.Topology.Mesh

@[expose] public section

/-! One later numerical threshold pays every original branch stem in the
corrected pairing, including the odd/even terminal excursions. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemAggregate

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests (IncludedStemRequest)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : FramedPuncturedGrid curve branches
    higher}
  {lifted : LiftedPuncturedGrid base} {current : LiftedPuncturedGrid next}
  {bank : BasedBranchBank lifted}
    {included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid}
  {domains : FaceDomainBank current.frames
    next.faces.regulars} {differential : Differential genus}

set_option genInjectivity false in
/-- The ordered request bank for branch stems on a retained coordinate inclusion.

Each indexed branch and initial sheet retains its own excursion-to-boundary comparison on the enlarged mesh. -/
inductive IncludedStemRequests (bank : LiftedPuncturedGrid.BasedBranchBank lifted)
    (included : Extension.CoordinateInclusion base.bank.grid next.bank.grid)
    (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (target : Fraction.Rational) :
    List (BranchIsolation.Data.Index branches × Fin 2) → Type 2 where
  /-- The empty stem request bank. -/ | nil :
    IncludedStemRequests bank included fixed
    target []
  /-- Extend the bank with the request for its actual first branch and sheet. -/ | cons {entry entries} (head :
    StemRequests.IncludedStemRequest bank included fixed entry.1 entry.2 target)
      (tail : IncludedStemRequests bank
        included fixed target entries) :
      IncludedStemRequests bank included fixed
        target (entry :: entries)

constructive_injectivity IncludedStemRequests

namespace IncludedStemRequests

variable {fixed : FaceMagnitudeBank domains
  differential} {target : Rational}

/-- Prepare a stem comparison for every retained branch-and-sheet entry, preserving order and multiplicity. -/
def build (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (included : Extension.CoordinateInclusion base.bank.grid
  next.bank.grid)
    (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (target : Fraction.Rational) (positive : 0 < target)
      :
    (entries : List (BranchIsolation.Data.Index branches × Fin 2)) →
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemAggregate.IncludedStemRequests bank included fixed target
      entries
  | [] => .nil
  | entry :: entries => .cons (IncludedStemRequest.build bank included fixed entry.1 entry.2 target positive)
      (build bank
        included fixed target positive entries)

/-- The maximum stage paying the complete retained stem request bank, or zero for an empty bank. -/
def index : {entries : List (BranchIsolation.Data.Index branches × Fin 2)} →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemAggregate.IncludedStemRequests bank included fixed target
      entries → Nat
  | _, .nil => 0
  | _, .cons head tail => max head.index tail.index

/-- At a paid common stage, each resplit based excursion approximates its boundary lap on the actual arriving sheet. -/
theorem accurate {entries : List (BranchIsolation.Data.Index branches × Fin 2)}
    (requests : Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemAggregate.IncludedStemRequests bank included
      fixed target entries)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
    (later : requests.index ≤ stage) :
    ∀ entry ∈ entries,
      Data.Gaussian.Norm.Basic.normSq (RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh
        readings.values) (current.edges.indexedEdges current.vertices
          (included.resplit (bank.rows.get entry.1).reference.walk (FramedBranchCellBank.baseMember base.bank)) entry.2)
            -
        RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
          (current.edges.indexedEdges current.vertices
          (included.resplit (bank.rows.get entry.1).boundary ((base.bank.cell entry.1).anchor_mem (base.bank.cell_mem
            entry.1)))
          (RootEdgeBank.target current.edges (included.resplit (bank.rows.get entry.1).stem
            ((base.bank.cell entry.1).anchor_mem (base.bank.cell_mem entry.1))) entry.2))) ≤ target := by
  induction requests with
  | nil => intro entry member; cases member
  | cons head tail ih =>
      intro entry member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · have h := head.loop_area_accurate readings ((Data.Nat.Order.le_max_left _ _).trans later)
        change Fraction.Order.Basic.LessEqual _ _ at h
        change Fraction.Order.Basic.LessEqual _ _
        simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using h
      · exact ih ((Data.Nat.Order.le_max_right _ _).trans later) entry member

/-- The per-entry allowance bounds the Gaussian sum of all retained excursion-to-boundary area differences strictly
below the positive target. -/
theorem aggregate_accurate (positive : 0 < target)
    {entries : List (BranchIsolation.Data.Index branches × Fin 2)}
    (requests : Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemAggregate.IncludedStemRequests bank included
      fixed (Aggregate.perTerm target entries.length) entries)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
    (later : requests.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry =>
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
        (current.edges.indexedEdges current.vertices
        (included.resplit (bank.rows.get entry.1).reference.walk (FramedBranchCellBank.baseMember base.bank)) entry.2) -
      RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
        (current.edges.indexedEdges current.vertices
        (included.resplit (bank.rows.get entry.1).boundary ((base.bank.cell entry.1).anchor_mem (base.bank.cell_mem
          entry.1)))
        (RootEdgeBank.target current.edges (included.resplit (bank.rows.get entry.1).stem
          ((base.bank.cell entry.1).anchor_mem (base.bank.cell_mem entry.1))) entry.2))))) < target := by
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro value member
  obtain ⟨entry, inEntries, equal⟩ := Map.mem_map.mp member
  rw [← equal, Data.List.Map.length_map]
  exact requests.accurate readings later entry inEntries

end IncludedStemRequests

namespace Ordered.Paired.Prepared

variable {sheet : Fin 2} {ordered :
  Ordered bank
  sheet} {paired : Paired ordered}

/-- Reuse the retained branch order but start in the newly selected common sheet. The terminal labels are not lost from
the aggregate budget. -/
def includedStemLabels (_prepared : PeriodPrograms.Prepared paired) (newSheet : Fin 2) : List
  (BranchIsolation.Data.Index branches × Fin 2) :=
  paired.split.pairs.flatMap (fun pair => [(pair.1, newSheet), (pair.2, BranchCutLifts.otherSheet newSheet)]) ++
    match paired.split.ending with
    | .odd reference => [(reference, newSheet)]
    | .even reference last => [(reference, newSheet), (last, BranchCutLifts.otherSheet newSheet)]

/-- All retained branch labels occur in their original geometric order. -/
theorem includedStemLabels_labels (prepared : PeriodPrograms.Prepared paired) (newSheet : Fin 2) :
    (includedStemLabels
      prepared newSheet).map Prod.fst = ordered.prepared.labels := by
  have pairs (labels : List (BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches)) :
      (labels.flatMap (fun pair => [(pair.1, newSheet), (pair.2, BranchCutLifts.otherSheet newSheet)])).map Prod.fst =
        labels.flatMap (fun pair => [pair.1, pair.2]) := by
    induction labels with
    | nil => rfl
    | cons pair rest ih =>
        change pair.1 :: pair.2 :: _ = pair.1 :: pair.2 :: _
        exact congrArg (fun tail => pair.1 :: pair.2 :: tail) ih
  rw [includedStemLabels,
    Data.List.Map.map_append, pairs]
  refine (congrArg (fun tail => paired.split.pairs.flatMap (fun pair => [pair.1, pair.2]) ++ tail) ?_).trans
    paired.split.labels_eq.symm
  cases paired.split.ending <;> rfl

/-- The computed aggregate request consumes the actual enlarged mesh and works at every later shared numerical stage; no
stem bound is supplied. -/
theorem included_stems_accurate (prepared : PeriodPrograms.Prepared paired)
    (included : Extension.CoordinateInclusion base.bank.grid next.bank.grid)
    (fixed : MagnitudeBank.FaceMagnitudeBank domains differential) (newSheet : Fin 2) (target : Fraction.Rational)
      (positive : 0 < target) :
    let labels :=
      includedStemLabels
      prepared newSheet
    let requests := Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemAggregate.IncludedStemRequests.build bank
      included fixed (Aggregate.perTerm target labels.length)
      (Aggregate.perTerm_positive positive _) labels
    ∀ stage (shared : PrimitiveData.FacePrimitiveBank differential stage domains) (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh),
      requests.index ≤ stage →
      Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (labels.map (fun entry =>
        RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
          (current.edges.indexedEdges current.vertices
          (included.resplit (bank.rows.get entry.1).reference.walk (FramedBranchCellBank.baseMember base.bank)) entry.2)
            -
        RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
          (current.edges.indexedEdges current.vertices
          (included.resplit (bank.rows.get entry.1).boundary ((base.bank.cell entry.1).anchor_mem (base.bank.cell_mem
            entry.1)))
          (RootEdgeBank.target current.edges (included.resplit (bank.rows.get entry.1).stem
            ((base.bank.cell entry.1).anchor_mem (base.bank.cell_mem entry.1))) entry.2))))) < target := by
  intro labels requests stage shared readings later
  exact requests.aggregate_accurate positive readings later

end Ordered.Paired.Prepared
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemAggregate
