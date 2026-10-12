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
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAggregate
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

public section

/-! Aggregate the corrected single-lap holes against every actual physical
hole exactly once. Starting sheets are retained from the ordered excursions;
the physical comparison is independent of the order used to store holes. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}

namespace Paired.BranchArea.PairedRows

variable {reference : Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {sheet : Fin 2}

/-- The retained paired-row stem labels project to the original ordered branch labels. -/
theorem stemLabels_first : ∀
  {labels : List (Hyperelliptic.Branches.BranchIsolation.Data.Index branches ×
  Hyperelliptic.Branches.BranchIsolation.Data.Index branches)}
    {prior : Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet} (rows :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior),
    rows.stemLabels.map Prod.fst = labels.flatMap (fun pair => [pair.1, pair.2])
  | _, _, .nil _ => rfl
  | _, _, .cons _ tail => congrArg (fun rest => _ :: _ :: rest) (stemLabels_first tail)

/-- The original paired-row hole-area total equals the sum over its retained branch labels and actual arriving sheets.
-/
theorem holeAreas_eq (value :
  Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    ∀ {labels : List (Hyperelliptic.Branches.BranchIsolation.Data.Index branches ×
      Hyperelliptic.Branches.BranchIsolation.Data.Index branches)} {prior :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet}
      (rows : Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior),
      rows.holeAreas value = Geometry.Grid.CellBoundary.sumValues (fun entry => bank.holeArea value entry.1 entry.2)
        rows.stemLabels
  | _, _, .nil _ => rfl
  | _, _, .cons _ tail => by
      change _ + _ + tail.holeAreas value = _ + (_ + _)
      rw [holeAreas_eq value tail]
      ring1

end Paired.BranchArea.PairedRows

namespace OrderedBranchPairs.EndingTours

variable {sheet : Fin 2} {ending : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding
  (Hyperelliptic.Branches.BranchIsolation.Data.Index branches)}

/-- The retained ending-tour stem labels project to the original ending labels. -/
theorem stemLabels_first (tours
  : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending) : tours.stemLabels.map Prod.fst
  = ending.labels := by
  cases tours <;> rfl

/-- The original ending-tour hole-area total equals the sum over its retained branch labels and sheets. -/
theorem holeAreas_eq (value :
  Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (tours :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending) :
    tours.holeAreas value = Geometry.Grid.CellBoundary.sumValues (fun entry => bank.holeArea value entry.1 entry.2)
      tours.stemLabels := by
  cases tours <;> simp only [Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours.holeAreas,
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours.stemLabels, Geometry.Grid.CellBoundary.sumValues]
      <;> ring1

end OrderedBranchPairs.EndingTours

namespace Paired

variable {sheet : Fin 2} {ordered :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet} {paired :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}

namespace PeriodPrograms.Prepared

/-- The complete prepared stem labels project to the original ordered branch-label list. -/
theorem stemLabels_first
    (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) : prepared.stemLabels.map
      Prod.fst = ordered.prepared.labels := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared.stemLabels, Data.List.Map.map_append,
    paired.rows.stemLabels_first, paired.ending.stemLabels_first, ← paired.split.labels_eq]

end PeriodPrograms.Prepared

namespace HoleAggregate.Prepared

set_option genInjectivity false in
/-- A paid aggregate request for the original corrected hole excursions and complete physical-hole list.

It retains every actual starting sheet, the original stem-label order and one dependent physical-hole request bank. -/
structure HoleAggregateRequest (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (target :
  Fraction.Rational) where
  /-- The requested whole hole-area target is positive. -/ positive : 0 < target
  /-- The retained branch labels with their actual starting sheets. -/ labels : List
    (Hyperelliptic.Branches.BranchIsolation.Data.Index branches × Fin 2)
  /-- The labels are exactly the original prepared stem labels. -/ labels_eq : labels = prepared.stemLabels
  /-- The common local hole-area allowance. -/ allowance : Fraction.Rational
  /-- The allowance pays both count factors for the actual retained label list. -/ allowance_eq : allowance =
    Rational.Budget.Aggregate.perTerm target labels.length
  /-- The dependent bank of original physical-hole requests at that allowance. -/ holes :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRequestBank fixed allowance
  /-- The cached common sufficient stage. -/ index : Nat
  /-- The stage is exactly the retained hole bank's stage. -/ index_eq : index = holes.index

constructive_injectivity HoleAggregateRequest

end HoleAggregate.Prepared

namespace HoleAggregate.Prepared.HoleAggregateRequest

variable {prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired} {fixed :
  Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential} {target :
  Fraction.Rational}

/-- Prepare the original per-hole request bank with the aggregate allowance and cache its common sufficient stage. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (fixed :
  Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential)
    (target : Fraction.Rational) (positive : 0 < target) :
      HoleAggregateRequest prepared
      fixed target :=
  let labels := prepared.stemLabels
  let allowance := Rational.Budget.Aggregate.perTerm target labels.length
  let holes := Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank.HoleRequestBank.build fixed allowance
    (Rational.Budget.Aggregate.perTerm_positive positive _)
  ⟨positive, labels, rfl, allowance, rfl, holes, holes.index, rfl⟩

/-- The physical sum contains every retained hole exactly once, while the
single-lap terms use the actual sheet of each corrected excursion. -/
theorem accurate (request :
  HoleAggregateRequest prepared fixed
  target)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains} (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      lifted.mesh)
    (later : request.index ≤ stage) :
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.values
    let single := paired.rows.holeAreas value + paired.ending.holeAreas value
    Data.Gaussian.Norm.Basic.normSq (single + single + Geometry.Grid.CellBoundary.sumValues
      (fun hole => Topology.Mesh.RetracingWords.wordArea value (hole.liftedBoundary lifted.vertices lifted.edges))
        base.faces.holes) < target := by
  let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.values
  let errors := request.labels.map (fun entry => bank.holeArea value entry.1 entry.2 + bank.holeArea value entry.1
    entry.2 +
    request.holes.physicalArea value entry.1)
  have estimate : Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum errors) < target := by
    apply Gaussian.Budget.Aggregate.normSq_sum_lt _ request.positive
    intro error member
    obtain ⟨entry, _, equal⟩ := Data.List.Map.mem_map.mp member
    rw [← equal, Data.List.Map.length_map]
    have bound := (request.holes.rows.get entry.1).accurate bank entry.2 readings
      ((request.holes.index_ge entry.1).trans (request.index_eq ▸ later))
    exact bound.trans_eq request.allowance_eq
  have holes : Geometry.Grid.CellBoundary.sumValues (fun entry => bank.holeArea value entry.1 entry.2) request.labels =
      paired.rows.holeAreas value + paired.ending.holeAreas value := by
    rw [request.labels_eq, Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared.stemLabels,
      Geometry.Grid.CellBoundary.sumValues_append, ← paired.rows.holeAreas_eq, ← paired.ending.holeAreas_eq]
  have physical : Geometry.Grid.CellBoundary.sumValues (fun entry => request.holes.physicalArea value entry.1)
    request.labels =
      Geometry.Grid.CellBoundary.sumValues (fun hole => Topology.Mesh.RetracingWords.wordArea value (hole.liftedBoundary
        lifted.vertices lifted.edges)) base.faces.holes := by
    rw [← Geometry.Grid.CellBoundary.sumValues_map (request.holes.physicalArea value) Prod.fst, request.labels_eq,
      prepared.stemLabels_first]
    exact request.holes.physical_sum value ordered
  change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (request.labels.map _)) < target
    at estimate
  rw [← Geometry.Grid.CellBoundary.sumValues_eq_gaussianSum_map, Geometry.Grid.CellBoundary.sumValues_add,
    Geometry.Grid.CellBoundary.sumValues_add, holes, physical] at estimate
  exact estimate

end HoleAggregate.Prepared.HoleAggregateRequest
end Paired
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
