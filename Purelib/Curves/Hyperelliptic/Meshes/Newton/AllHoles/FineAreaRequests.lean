module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Decide
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.RequestedSideAreas
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.IncrementArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

public section

/-! The fine boundary allocator feeds the existing all-hole source and
sewing comparison on the literal same grid. Requests follow every retained
annulus and choose one stage before sampling any fine primitive values. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Riemann

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}

set_option genInjectivity false in
/-- A common fine-area allocation for all original annuli on one retained Newton grid.

The original squared outer-count cap determines the per-hole allowance; the nested fine request retains the grid and
common radius used by the source and sewing comparisons. -/
structure FamilyFineAreaRequest (preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation
  original) (target radius : Fraction.Rational) where
  /-- The complete requested all-hole target is strictly positive. -/ positive : 0 < target
  /-- The cached common occurrence cap for the original hole family. -/ count : Nat
  /-- The family count is the square of the retained original outer count. -/ count_eq : count =
    (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation) ^ 2
  /-- The shared area allowance allocated to each original hole. -/ perHole : Fraction.Rational
  /-- The per-hole allowance is the exact count allocation from the complete target. -/ perHole_eq : perHole =
    Rational.Budget.Aggregate.perTerm target count
  /-- The original fine-area request at one quarter of the per-hole allowance. -/ fine :
    Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests.FineAreaRequest preparation (perHole / 4) radius

constructive_injectivity FamilyFineAreaRequest

namespace FamilyFineAreaRequest

/-- Allocate the original all-hole count and construct one fine-area request sharing its retained Newton grid. -/
@[expose] def build (preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original)
  (target radius : Fraction.Rational)
    (positive : 0 < target) (radiusPositive : 0 < radius) :
      Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest preparation target radius :=
  let count := (Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.outerCount preparation) ^ 2
  let perHole := Rational.Budget.Aggregate.perTerm target count
  ⟨positive, count, rfl, perHole, rfl, Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests.FineAreaRequest.build
    preparation (perHole / 4) radius
    (Fraction.Order.Field.div_pos_direct (Rational.Budget.Aggregate.perTerm_positive positive count) (by decide))
      radiusPositive⟩

/-- Repackage the cached grid for every existing source/sewing consumer.
This does not call the Newton-grid constructor a second time. -/
@[expose] def family (allocated : Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest
  preparation target radius) :
    Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest preparation target
      allocated.fine.radiusBudget.size :=
  ⟨allocated.positive, allocated.count, allocated.count_eq, allocated.perHole, allocated.perHole_eq,
    allocated.fine.area⟩

variable (allocated : Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests.FamilyFineAreaRequest
  preparation target radius)
  {lifted : Meshes.LiftedPuncturedGrid allocated.family.single.grid.punctured}
  {excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision allocated.family.single.grid lifted}
  {prepared : (Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
    excision)} {first second : Fin genus}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    allocated.family.single.grid.faces.regulars}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet}
  {meshTarget : Fraction.Rational}
  {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    meshTarget}
  {comparison :
    PairedComparison prepared
    first second domains}

/-- Each slot refers to its original annulus and original source occurrences. -/
@[expose] def SideReference (comparison :
  PairedComparison prepared
  first second domains)
    (traces : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request) (position : Fin
      comparison.entries.length) :=
  let entry := comparison.entries[position.val]'position.isLt
  Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceBank traces
    (allocated.fine.area.grid.bands.entries.get entry.source.entry.hole.index)
    first second (Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences.sideOccurrences entry.source.outer)

set_option genInjectivity false in
/-- Materialized original annular side requests, endpoint allowance and one common comparison threshold.

Every slot remains indexed by the original paired annulus and its exact source occurrence list on the supplied trace
bank. -/
structure SideRequests (comparison :
  PairedComparison prepared
  first second domains)
    (traces : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request) where
  /-- The cached original band-occurrence request at every paired-annulus list position. -/ references :
    Data.Vector.DependentVector (fun position : Fin comparison.entries.length => allocated.SideReference comparison
    traces position)
  /-- The shared endpoint request paid at the retained fine-area component allowance. -/ endpoints :
    PuncturedGrid.PerimeterEndpointRequest fixed first second
    allocated.fine.component
  /-- The cached common stage for side references, endpoints and original comparison. -/ index : Nat
  /-- Every retained side-reference threshold is bounded by the common stage. -/ references_le : ∀ position,
    (references.get position).index ≤ index
  /-- The original endpoint request threshold is bounded by the common stage. -/ endpoints_le : endpoints.index ≤ index
  /-- The retained original paired-comparison threshold is bounded by the common stage. -/ comparison_le :
    comparison.index ≤ index

constructive_injectivity SideRequests

namespace SideRequests
variable {allocated}

/-- Materialize the original annular side references and shared endpoint request, caching their maximum with the
original comparison threshold. -/
@[expose] def build (comparison :
  PairedComparison prepared
  first second domains)
    (traces : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request) :
      allocated.SideRequests comparison traces :=
  let references := Data.Vector.DependentVector.ofFn fun position : Fin comparison.entries.length =>
    Hyperelliptic.Meshes.Newton.Annulus.RequestedSideAreas.sideRequests
      (comparison.entries[position.val]'position.isLt).source.outer traces first second
  let endpoints := allocated.fine.endpoints fixed first second
  let maximum := references.maximum (fun _ reference => reference.index)
  ⟨references, endpoints, max (max maximum endpoints.index) comparison.index,
    fun position => ((references.get_le_maximum (fun _ reference => reference.index) position).trans
      (Data.Nat.Order.le_max_left _ _)).trans (Data.Nat.Order.le_max_left _ _),
    (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _), Data.Nat.Order.le_max_right _ _⟩

variable {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage}

/-- Every occurrence is paid on the shared later bank, including reversals,
repeated source edges and the second lap. -/
theorem entry_accurate (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request
  cache first second) (lengths : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths
  samples)
    (requested : allocated.SideRequests comparison samples.traces)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := request)
      cache.normalize first second)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get first) lifted.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get second)
      lifted.mesh)
    (later : requested.index ≤ stage) (entry :
      Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest.PairedAnnulus
      allocated.family lifted first second domains)
    (member : entry ∈ comparison.entries) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.fineSideArea
      entry.source.outer perimeters - Data.Gaussian.Norm.Sum.Basic.gaussianSum (entry.source.outer.sources.map
      (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right))) <
      allocated.family.perHole := by
  obtain ⟨position, bound, equal⟩ := List.mem_iff_getElem.mp member
  have estimate := allocated.fine.fineSideArea_accurate
    (Fraction.Order.Field.div_pos_direct allocated.family.perHole_positive (by decide : (0 : Fraction.Rational) < 4))
    (comparison.entries[position]'bound).source.outer samples lengths perimeters left right
    (requested.references.get ⟨position, bound⟩) requested.endpoints
    ((requested.references_le ⟨position, bound⟩).trans later) (requested.endpoints_le.trans later)
  exact equal ▸ estimate.trans_le allocated.family.quarter_le

/-- Aggregate the full list from the already prepared source comparison;
no hole is removed or replaced by a polygon of total increments. -/
theorem correction_accurate (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache first second) (lengths :
  Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples)
    (requested : allocated.SideRequests comparison samples.traces)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := request)
      cache.normalize first second)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get first) lifted.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get second)
      lifted.mesh)
    (later : requested.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (comparison.entries.map (fun entry =>
      Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.fineSideArea entry.source.outer perimeters -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (entry.source.outer.sources.map
        (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right)))))
        < target := open Purelib.Integration in by
  let values := comparison.entries.map (fun entry =>
    Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.fineSideArea entry.source.outer perimeters -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entry.source.outer.sources.map
      (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right)))
  have bounded : ∀ value ∈ values, Data.Gaussian.Norm.Basic.normSq value ≤ allocated.family.perHole := by
    intro value member
    obtain ⟨entry, belongs, equal⟩ := Data.List.Map.mem_map.mp member
    exact equal ▸ (requested.entry_accurate samples lengths perimeters left right later entry belongs).le
  have count : values.length ≤ allocated.family.count :=
    (Data.List.Map.length_map ..).le.trans comparison.entries_count
  have estimate := Path.IncrementArea.sum_bound_of_length allocated.family.perHole_positive.le bounded count
  have paid := Rational.Budget.Aggregate.count_mul_perTerm_lt allocated.positive allocated.family.count
  rw [← allocated.family.perHole_eq] at paid
  exact estimate.trans_lt ((show (allocated.family.count : Fraction.Rational)^2 * allocated.family.perHole =
    (allocated.family.count : Fraction.Rational) * ((allocated.family.count : Fraction.Rational) *
      allocated.family.perHole) by ring1).trans_lt paid)

end SideRequests
end FamilyFineAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
