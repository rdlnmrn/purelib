module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.NewtonPairedCutRequests
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests.NewtonPreparation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Path.PairedIncrementArea

open Purelib.Riemann

open Purelib.Riemann.Branches.NewtonPairedCutRequests

open Purelib.Riemann.Periods

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

public section

/-! Paired comparisons consume the original all-hole preparation once, with
one common stage for every retained hole and both standard differentials. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank
    (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests (PairedSewnRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}

section NewtonPreparation.FamilyAreaRequest

variable {request :
  FamilyAreaRequest
  preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {excision : AllHoleExcision request.single.grid lifted}
  {first second : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}

namespace PairedComparison.NewtonPreparation.FamilyAreaRequest

set_option genInjectivity false in
/-- An original prepared annulus and its common sewing request for two standard differentials.

The request uses the same retained face domains and the original outer preparation. -/
structure PairedAnnulus (request : NewtonPreparation.FamilyAreaRequest preparation target radius)
    (lifted : Meshes.LiftedPuncturedGrid request.single.grid.punctured) (first second : Fin genus)
    (domains : DomainBanks.FaceDomainBank lifted.frames request.single.grid.faces.regulars) where
  /-- The original annular entry and its retained outer preparation. -/ source : AnnularEntry.Prepared
    request.single.grid lifted
  /-- The common sewing request for the two original standard differentials. -/ sewn :
    NewtonPairedSewnAreaRequests.PairedSewnRequest request.single source.outer first second domains 0

constructive_injectivity PairedAnnulus

end PairedComparison.NewtonPreparation.FamilyAreaRequest

namespace PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus

/-- Attach the common paired sewing request to the supplied original annular preparation. -/
@[expose] def build (source : AnnularEntry.Prepared request.single.grid lifted)
    (first second : Fin genus) (domains : DomainBanks.FaceDomainBank lifted.frames request.single.grid.faces.regulars) :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus
      request lifted first second domains :=
  ⟨source, PairedSewnRequest.build source.outer first second domains 0⟩

/-- The maximum sewing stage of the retained annular entries, with zero for the empty list. -/
@[expose] def index : List
  (Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus
  request lifted first second domains) → Nat
  | [] => 0
  | entry :: tail => max entry.sewn.sewing.stage
    (index
    tail)

/-- Every retained annulus has sewing stage below the actual list maximum. -/
theorem index_le : ∀ (entries : List
  (Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus
  request lifted first second domains)) (entry),
    entry ∈ entries → entry.sewn.sewing.stage ≤
      index
      entries
  | [], _, member => by cases member
  | head :: tail, entry, member => by
      rcases List.Membership.mem_cons.mp member with rfl | inTail
      · exact Nat.Order.le_max_left _ _
      · exact
          (index_le
          tail entry inTail).trans (Nat.Order.le_max_right _ _)

end PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus

set_option genInjectivity false in
/-- A paired request for every original prepared hole, with a shared cached stage.

The ordered source readback identifies the exact original preparation list; the stage is the maximum of the retained
sewing stages. -/
structure PairedComparison (prepared : (AllHoleExcision.OuterPreparations excision)) (first second : Fin genus)
    (domains : DomainBanks.FaceDomainBank lifted.frames request.single.grid.faces.regulars) where
  /-- The ordered paired annular requests on the original common domain bank. -/ entries : List
    (Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus
    request lifted first second domains)
  /-- The paired entries project to exactly the original retained annular preparations. -/ entries_eq : entries.map
    PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus.source
    = prepared.entries
  /-- The cached common maximum stage of all retained paired annuli. -/ index : Nat
  /-- The cached common stage is the maximum stage of the actual retained paired entries. -/ index_eq : index =
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus.index
    entries

constructive_injectivity PairedComparison

namespace PairedComparison

variable {prepared :
  (Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
  excision)}

/-- Prepare both differentials on every original annular entry and cache their exact common stage. -/
@[expose] def build (prepared : (AllHoleExcision.OuterPreparations excision)) (first second : Fin genus)
    (domains : DomainBanks.FaceDomainBank lifted.frames request.single.grid.faces.regulars) :
    PairedComparison
      prepared first second domains :=
  let entries := prepared.entries.map (fun source =>
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus.build
    source first second domains)
  ⟨entries, by
    dsimp only [entries]
    induction prepared.entries with
    | nil => rfl
    | cons source tail ih => exact congrArg (List.cons source) ih,
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus.index
      entries, rfl⟩

/-- The actual paired entry count is bounded by the original all-hole request count. -/
theorem entries_count (comparison :
  PairedComparison
  prepared first second domains) :
    comparison.entries.length ≤ request.count := by
  have count := congrArg List.length comparison.entries_eq
  have original := congrArg List.length prepared.entries_eq
  rw [List.Map.length_map] at count original
  exact count.le.trans (original.le.trans (request.entries_count excision))

/-- Every retained annulus is ready at a stage above the cached common maximum. -/
theorem later (comparison :
  PairedComparison
  prepared first second domains)
    {stage : Nat} (late : comparison.index ≤ stage)
    (entry :
      Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus
      request lifted first second domains) (member : entry ∈ comparison.entries) :
    entry.sewn.sewing.stage ≤ stage :=

    (NewtonPreparation.FamilyAreaRequest.PairedAnnulus.index_le
    comparison.entries entry member).trans (comparison.index_eq ▸ late)

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

set_option genInjectivity false in
/-- The paired increment-area summary for one actual annular source word.

Both components use the supplied triangle reading banks on the original retained source edges. -/
structure Term {stage : Nat}
    {firstBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential first) stage domains}
    {secondBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential second) stage domains}
    (left : TrianglePrimitiveReadings.TriangleReadings firstBank lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings secondBank lifted.mesh) where
  /-- The actual paired annular request whose original source word is summarized. -/ source :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus
    request lifted first second domains
  /-- The cached paired area summary on the exact original ordered outer source increments. -/ data :
    PairedIncrementArea.Summary (source.source.outer.sources.map (fun edge =>
    (⟨SourceEdge.increment edge left.values, SourceEdge.increment edge right.values⟩ : Stokes.PrimitivePoint)))

constructive_injectivity Term

namespace Term

variable {stage : Nat}
  {firstBank : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential first) stage domains}
  {secondBank : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential second) stage domains}
  {left : TriangleReadings firstBank
    lifted.mesh} {right : TriangleReadings
    secondBank lifted.mesh}

/-- Summarize the paired increments of the supplied reading banks on the original annular outer word. -/
@[expose] def build (left : TrianglePrimitiveReadings.TriangleReadings firstBank lifted.mesh) (right :
  TrianglePrimitiveReadings.TriangleReadings secondBank lifted.mesh)
    (source :
      Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus
      request lifted first second domains) :
      PairedComparison.Term
      left right :=
  ⟨source, Summary.build (source.source.outer.sources.map (fun edge =>
    (⟨SourceEdge.increment edge left.values, SourceEdge.increment edge right.values⟩ : Stokes.PrimitivePoint)))⟩

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
  in
/-- At a stage paying its sewing request, the actual annular paired area satisfies the original per-hole allowance. -/
theorem area_bound (term :
  Term
  left right) (later : term.source.sewn.sewing.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq term.data.areaValue < request.perHole := by
  rw [term.data.area_eq]
  have references := PairedCutRequest.references_later term.source.sewn.sewing later
  exact (AreaRequest.paired_source_area_accurate request.single term.source.sewn.comparison.left
    term.source.sewn.comparison.right references.1 references.2 left right).trans_le request.quarter_le

end Term

set_option genInjectivity false in
/-- The complete cached paired area sum over the original retained annuli.

Each term keeps its source owner and exact area readback; the aggregate is the sum of that same ordered area list. -/
structure Sample (comparison :
  PairedComparison
  prepared first second domains) {stage : Nat}
    {firstBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential first) stage domains}
    {secondBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential second) stage domains}
    (left : TrianglePrimitiveReadings.TriangleReadings firstBank lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings secondBank lifted.mesh) where
  /-- The actual paired annular summaries evaluated on the supplied two triangle reading banks. -/ terms : List
    (Term
    left right)
  /-- The evaluated terms project to exactly the original paired request entries. -/ terms_eq : terms.map
    Term.source
    = comparison.entries
  /-- The cached ordered list of actual annular area values. -/ areas : List Data.Gaussian.Basic.Canonical
  /-- The area list is exactly the list of retained term summaries' area values. -/ areas_eq : areas = terms.map (fun
    term => term.data.areaValue)
  /-- The cached complete sum of the original annular area values. -/ area : Data.Gaussian.Basic.Canonical
  /-- The complete area is the Gaussian sum of its retained original area list. -/ area_eq : area =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum areas

constructive_injectivity Sample

namespace Sample

variable {comparison :
  PairedComparison
  prepared first second domains} {stage : Nat}
  {firstBank : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential first) stage domains}
  {secondBank : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential second) stage domains}
  {left : TriangleReadings firstBank
    lifted.mesh} {right : TriangleReadings
    secondBank lifted.mesh}

/-- Evaluate every original paired annular request and cache the ordered area list and its complete sum. -/
@[expose] def build (comparison :
  PairedComparison
  prepared first second domains)
    (left : TrianglePrimitiveReadings.TriangleReadings firstBank lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings secondBank lifted.mesh) :

      PairedComparison.Sample
      comparison left right :=
  let terms := comparison.entries.map
    (Term.build
    left right)
  let areas := terms.map (fun term => term.data.areaValue)
  ⟨terms, by
    dsimp only [terms]
    induction comparison.entries with
    | nil => rfl
    | cons source tail ih => exact congrArg (List.cons source) ih,
    areas, rfl, Data.Gaussian.Norm.Sum.Basic.gaussianSum areas, rfl⟩

open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
  in
/-- Every retained hole pays its full polygon; no polygon of totals replaces it. -/
theorem area_accurate (sample :
  PairedComparison.Sample
  comparison left right) (later : comparison.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq sample.area < target := by
  have count := congrArg List.length sample.terms_eq
  rw [List.Map.length_map] at count
  have areaCount : sample.areas.length ≤ request.count := by
    rw [sample.areas_eq, List.Map.length_map]
    exact count.le.trans comparison.entries_count
  have bounds : ∀ value ∈ sample.areas, Data.Gaussian.Norm.Basic.normSq value ≤ request.perHole := by
    intro value member
    rw [sample.areas_eq] at member
    obtain ⟨term, inTerms, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    exact (term.area_bound (comparison.later later term.source
      (sample.terms_eq ▸ Map.mem_map_of_mem inTerms))).le
  have estimate := IncrementArea.sum_bound_of_length request.perHole_positive.le bounds areaCount
  rw [request.perHole_eq] at estimate
  rw [sample.area_eq]
  exact estimate.trans_lt ((show (request.count : Fraction.Rational)^2 * Aggregate.perTerm target request.count =
    (request.count : Fraction.Rational) * ((request.count : Fraction.Rational) * Aggregate.perTerm target request.count)
      by ring1).trans_lt
      (Aggregate.count_mul_perTerm_lt request.positive request.count))

/-- The complete cached area equals the sum of the actual original outer source polygons, retaining both increment
coordinates. -/
theorem area_eq_source_polygons (sample :
  PairedComparison.Sample
  comparison left right) :
    sample.area = Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.entries.map (fun entry =>
      PairedIncrementArea.area (entry.outer.sources.map (fun edge =>
        (⟨SourceEdge.increment edge left.values, SourceEdge.increment edge right.values⟩ : Stokes.PrimitivePoint))))) :=
          by
  have first := congrArg (List.map (fun source :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus
    request lifted first second domains =>
    PairedIncrementArea.area (source.source.outer.sources.map (fun edge =>
        (⟨SourceEdge.increment edge left.values, SourceEdge.increment edge right.values⟩ : Stokes.PrimitivePoint)))))
          sample.terms_eq
  have second := congrArg (List.map (fun source : AnnularEntry.Prepared request.single.grid lifted =>
    PairedIncrementArea.area (source.outer.sources.map (fun edge =>
        (⟨SourceEdge.increment edge left.values, SourceEdge.increment edge right.values⟩ : Stokes.PrimitivePoint)))))
          comparison.entries_eq
  simp only [-eq_self, -iff_self, List.Map.map_map, Function.comp_def] at first second
  have values : sample.terms.map (fun term => term.data.areaValue) = sample.terms.map (fun term =>
      PairedIncrementArea.area (term.source.source.outer.sources.map (fun edge =>
        (⟨SourceEdge.increment edge left.values, SourceEdge.increment edge right.values⟩ : Stokes.PrimitivePoint)))) :=
          by
    induction sample.terms with
    | nil => rfl
    | cons term tail ih => exact congrArg₂ List.cons term.data.area_eq ih
  exact sample.area_eq.trans (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.areas_eq.trans
    (values.trans (first.trans second))))

end Sample

end PairedComparison
end NewtonPreparation.FamilyAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles
