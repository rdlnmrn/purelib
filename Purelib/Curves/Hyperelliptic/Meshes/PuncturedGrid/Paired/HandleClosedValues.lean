module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleLoopReduction
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWordReduction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib.Topology.Surface.Sewing

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

open Purelib

@[expose] public section

/-! Evaluate ordered cycles on finite valuations closed on faces and physical boundary loops. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains

local notation "vget" => Data.Vector.get

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    PeriodPrograms.Prepared paired}

variable {cut : PeriodCoordinates.CutBank prepared} (chains :
  HandleChains cut)

namespace LoopReduction

/-- A finite integer-weighted collection of original boundary loops has zero total valuation when each loop does. -/
private theorem loopSum_zero {vertices : Nat} (rows : List (Int × List (Topology.Polygon.Stokes.OrientedEdge vertices)))
    (value : Topology.Polygon.Stokes.OrientedEdge vertices → Gaussian.Basic.Canonical)
    (zero : ∀ entry ∈ rows, SewingRetraction.wordValue value entry.2 = 0) :
    Gaussian.Norm.Sum.Basic.gaussianSum
      (rows.map (fun entry => (entry.1 : Gaussian.Basic.Canonical) * SewingRetraction.wordValue
        value entry.2)) = 0 := by
  induction rows with
  | nil => rfl
  | cons entry rest ih =>
      change (entry.1 : Gaussian.Basic.Canonical) * SewingRetraction.wordValue value entry.2 +
        Gaussian.Norm.Sum.Basic.gaussianSum (rest.map _) = 0
      rw [zero entry List.mem_cons_self, mul_zero,
        ih (fun other member => zero other (List.mem_cons_of_mem _ member)), zero_add]

variable {chains} (data : LoopReduction
  chains)
  (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
  (boundaryZero : ∀ word ∈ lifted.boundaryLoops, SewingRetraction.wordValue value word = 0)

include boundaryZero

/-- The retained radical component has zero valuation when every original physical boundary loop has zero valuation. -/
theorem radicalValue_zero (weights : HandleCoordinates.CutBank.HandleVector
  cut) : data.radicalValue weights value = 0 := open Algebra in by
  apply (FiniteSum.Fin.sumFin_congr ?_).trans FiniteSum.Fin.sumFin_zero
  intro index
  have zero : (data.remainders.get index).value value = 0 := by
    cases data.remainders.get index with
    | handle => rfl
    | physical unused row =>
        apply LoopReduction.loopSum_zero
        intro entry member
        apply boundaryZero entry.2
        rw [← data.original.canonical, ← row.words_eq]
        exact List.Map.mem_map_of_mem member
  exact (congrArg (((vget weights index : Int) : Gaussian.Basic.Canonical) * ·) zero).trans (mul_zero _)

/-- The retained original a-row physical correction has zero valuation when every physical boundary loop does. -/
theorem aPhysicalValue_zero {index : Fin genus} (row :
  HandleCoordinates.CutBank.HandleRow cut index) : data.aPhysicalValue row
  value = 0 := by
  have zero : Gaussian.Norm.Sum.Basic.gaussianSum ((data.original.rows.get index).a.rows.map
      (fun entry => (entry.1 : Gaussian.Basic.Canonical) * SewingRetraction.wordValue value
        entry.2)) = 0 := by
    apply LoopReduction.loopSum_zero
    intro entry member
    apply boundaryZero entry.2
    rw [← data.original.a_words_eq index]
    exact List.Map.mem_map_of_mem member
  exact (congrArg₂ (· + ·) (data.radicalValue_zero value boundaryZero row.a) zero).trans (zero_add _)

/-- The retained original b-row physical correction has zero valuation when every physical boundary loop does. -/
theorem bPhysicalValue_zero {index : Fin genus} (row :
  HandleCoordinates.CutBank.HandleRow cut index) : data.bPhysicalValue row
  value = 0 := by
  have zero : Gaussian.Norm.Sum.Basic.gaussianSum ((data.original.rows.get index).b.rows.map
      (fun entry => (entry.1 : Gaussian.Basic.Canonical) * SewingRetraction.wordValue value
        entry.2)) = 0 := by
    apply LoopReduction.loopSum_zero
    intro entry member
    apply boundaryZero entry.2
    rw [← data.original.b_words_eq index]
    exact List.Map.mem_map_of_mem member
  exact (congrArg₂ (· + ·) (data.radicalValue_zero value boundaryZero row.b) zero).trans (zero_add _)

include data

/-- The original a-period word equals its handle valuation plus its retained face correction when physical boundary
values vanish. -/
theorem a_word_handle_of_boundary_zero {index : Fin genus} (row :
  HandleCoordinates.CutBank.HandleRow cut index)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value (prepared.aWord index) = chains.handleValue row.a value +
      SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
        index).a.route.correction := by
  rw [data.a_word_value row value anti, data.aPhysicalValue_zero value boundaryZero row, add_zero]

/-- The original b-period word equals its handle valuation plus its retained face correction when physical boundary
values vanish. -/
theorem b_word_handle_of_boundary_zero {index : Fin genus} (row :
  HandleCoordinates.CutBank.HandleRow cut index)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value (prepared.bWord index) = chains.handleValue row.b value +
      SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
        index).b.route.correction := by
  rw [data.b_word_value row value anti, data.bPhysicalValue_zero value boundaryZero row, add_zero]

omit boundaryZero data in
/-- The original finite face correction has zero valuation when each retained triangle boundary does. -/
private theorem faceValue_zero
    (closed : ∀ face, SewingRetraction.wordValue value (lifted.mesh.triangulation.faces
      face).boundary = 0)
    (correction : List (SewingRetraction.FaceTerm lifted.mesh.triangles.length)) :
    SewingRetraction.faceValue lifted.mesh.triangulation.faces value correction = 0 := by
  induction correction with
  | nil => rfl
  | cons term rest ih =>
      change (term.1 : Gaussian.Basic.Canonical) * SewingRetraction.wordValue value
        (lifted.mesh.triangulation.faces term.2).boundary + _ = 0
      rw [closed term.2, mul_zero, ih, zero_add]

/-- An antisymmetric valuation closed on the original faces and boundary loops reads the original a-period word as its
retained handle value. -/
theorem a_word_handle_of_closed {index : Fin genus} (row :
  HandleCoordinates.CutBank.HandleRow cut index)
    (anti : ∀ edge, value edge.reverse = -value edge)
    (closed : ∀ face, SewingRetraction.wordValue value (lifted.mesh.triangulation.faces
      face).boundary = 0) :
    SewingRetraction.wordValue value (prepared.aWord index) = chains.handleValue row.a value :=
      by
  rw [data.a_word_handle_of_boundary_zero value boundaryZero row anti,
    LoopReduction.faceValue_zero value
    closed, add_zero]

/-- An antisymmetric valuation closed on the original faces and boundary loops reads the original b-period word as its
retained handle value. -/
theorem b_word_handle_of_closed {index : Fin genus} (row :
  HandleCoordinates.CutBank.HandleRow cut index)
    (anti : ∀ edge, value edge.reverse = -value edge)
    (closed : ∀ face, SewingRetraction.wordValue value (lifted.mesh.triangulation.faces
      face).boundary = 0) :
    SewingRetraction.wordValue value (prepared.bWord index) = chains.handleValue row.b value :=
      by
  rw [data.b_word_handle_of_boundary_zero value boundaryZero row anti,
    LoopReduction.faceValue_zero value
    closed, add_zero]

end LoopReduction
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleWords.CutBank.HandleChains
