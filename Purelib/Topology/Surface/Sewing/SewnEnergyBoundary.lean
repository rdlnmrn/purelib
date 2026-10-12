module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Energy.Polygon

public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Vector.Dependent
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Data

open Purelib.Integration.Energy

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Topology.Surface.Cut.WordArea

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Word

@[expose] public section

/-! Exact physical and word readbacks for the homogeneous sewn energy.
All pair defects, jumps and closed-word corrections are retained. -/
namespace Purelib.Topology.Surface.Sewing.SewnEnergyBoundary

open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnEnergyCombination (EnergySurfaces EnergyPairs combinedValues energyBoundary)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub sumFin_succ)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Basic (conj_add conj_mul)

variable {vertexCount faceCount genus : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {patch : SewingTree.SewnPatch faces} {localValues : Fin genus → Fin faceCount → PrimitiveSewing.PrimitiveValues 3}

/-- Gaussian conjugation commutes with the original finite sum. -/
private theorem conjugate_sum {count : Nat} (values : Fin count → Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.conj (FiniteSum.Fin.sumFin values) = FiniteSum.Fin.sumFin (fun index =>
      Data.Gaussian.Basic.conj (values index)) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ, Gaussian.Basic.conj_add, ih]

/-- The pair used in the energy comparison is the Hermitian pair of the actual combined scalar primitive, not an
independent bilinear valuation. -/
theorem combinedValues_energy (surfaces : SewnEnergyCombination.EnergySurfaces patch localValues)
    (coefficients : Fin genus → Gaussian.Basic.Canonical) (vertex : Fin patch.cut.count) :
    SewnEnergyCombination.combinedValues surfaces coefficients vertex = Polygon.energyPrimitivePoint
      (FiniteSum.Fin.sumFin (fun basis => coefficients basis *
        ((surfaces.get basis).sewn.values vertex - (surfaces.get basis).sewn.values patch.cut.anchor))) := by
  unfold SewnEnergyCombination.combinedValues Polygon.energyPrimitivePoint
  apply congrArg (fun left => (⟨left, _⟩ : Stokes.PrimitivePoint))
  rw [conjugate_sum]
  exact FiniteSum.Fin.sumFin_congr fun basis => (Gaussian.Basic.conj_mul _ _).symm

/-- The retained homogeneous energy primitive has conjugate left and right coordinates. -/
theorem combinedValues_conjugate (surfaces : SewnEnergyCombination.EnergySurfaces patch localValues)
    (coefficients : Fin genus → Gaussian.Basic.Canonical) (vertex : Fin patch.cut.count) :
    (PrimitivePoint.Conjugate (SewnEnergyCombination.combinedValues surfaces coefficients vertex)) := by
  rw [combinedValues_energy]
  rfl

/-- Centering changes no edge increment; the right component reads the weighted increments of the same retained scalar
sewn samples. -/
theorem combinedValues_increment (surfaces : SewnEnergyCombination.EnergySurfaces patch localValues)
    (coefficients : Fin genus → Gaussian.Basic.Canonical) (edge : Stokes.OrientedEdge patch.cut.count) :
    (SewnEnergyCombination.combinedValues surfaces coefficients edge.finish).right -
      (SewnEnergyCombination.combinedValues surfaces coefficients edge.start).right =
      FiniteSum.Fin.sumFin (fun basis => coefficients basis *
        ((surfaces.get basis).sewn.values edge.finish - (surfaces.get basis).sewn.values edge.start)) := by
  change FiniteSum.Fin.sumFin _ - FiniteSum.Fin.sumFin _ = _
  rw [← FiniteSum.Fin.sumFin_sub]
  apply FiniteSum.Fin.sumFin_congr
  intro basis
  ring1

/-- The physical boundary, jumps and pair defects belong to the very homogeneous energy boundary controlled by the
shared sewing request. -/
theorem energyBoundary_decomposition (surfaces : SewnEnergyCombination.EnergySurfaces patch localValues)
    (coefficients : Fin genus → Gaussian.Basic.Canonical)
    {pairing : ProjectedEdgePairs.ProjectedEdgePairing patch.cut.vertexLabels patch.cut.boundary}
    (boundary : ProjectedEdgePairing.PrimitiveSample pairing (SewnEnergyCombination.combinedValues surfaces
      coefficients)) :
    SewnEnergyCombination.energyBoundary surfaces coefficients = boundary.boundaryArea + boundary.jumpSum +
      boundary.defectSum :=
  boundary.boundary_decomposition

/-- The complete corrected word contraction is retained, including its closed correction; it is not identified with a
bare commutator area. -/
theorem energyBoundary_word (surfaces : SewnEnergyCombination.EnergySurfaces patch localValues)
    (coefficients : Fin genus → Gaussian.Basic.Canonical)
    {word : BoundaryWord.CutBoundaryWord patch.cut.vertexLabels patch.cut.boundary}
    (area : CutBoundaryWord.AreaSample word (SewnEnergyCombination.combinedValues surfaces coefficients)
      (SewnEnergyCombination.combinedValues surfaces coefficients patch.cut.anchor)) :
    SewnEnergyCombination.energyBoundary surfaces coefficients =
      Pairing.contract (fun row column => word.signature.matrix row column) area.values + area.closedCorrection :=
  area.closed_area_eq patch.cut.closed

end Purelib.Topology.Surface.Sewing.SewnEnergyBoundary
