module
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemArea
import Purelib.Topology.Surface.Boundary.PolarizedWordArea
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Integration.Path

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary.PolarizedWordArea

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-! The ordered based excursion has a paired boundary area and two explicit
stem defects, obtained by polarizing its exact resplit word identity. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearStemArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
  (resplit_loop_area)
open Purelib.Integration.Path.PairedIncrementArea (area)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Basic (conj_add)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} (bank :
    BasedBranchBank lifted)
  {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial
    (Ambient curve)}
  (included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion base.bank.grid grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid)
  (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
    Purelib.Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)

include reference

/-- Polarization retains the entire stem-area difference and the two-component stem-total defect with its actual
boundary multiplier. -/
theorem resplit_paired_loop_area (index : BranchIsolation.Data.Index branches) (sheet : Fin 2)
    (first second : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical)
    (firstAnti : ∀ edge, first edge.reverse = -first edge) (secondAnti : ∀ edge, second edge.reverse = -second edge) :
    let stem := included.resplit (bank.rows.get index).stem ((base.bank.cell index).anchor_mem (base.bank.cell_mem
      index))
    let hole := included.resplit (bank.rows.get index).boundary ((base.bank.cell index).anchor_mem (base.bank.cell_mem
      index))
    let outward := edges.indexedEdges vertices stem sheet
    let other := edges.indexedEdges vertices stem (BranchCutLifts.otherSheet sheet)
    let boundary := edges.indexedEdges vertices hole (RootEdgeBank.target edges stem sheet)
    let polygon := fun word => PairedIncrementArea.area (word.map (fun edge => (⟨first edge, second edge⟩ :
      Stokes.PrimitivePoint)))
    polygon (edges.indexedEdges vertices (included.resplit (bank.rows.get index).reference.walk
      (FramedBranchCellBank.baseMember base.bank)) sheet) =
      polygon boundary + (polygon outward - polygon other) +
        Stokes.edgeArea ⟨wordValue first outward + SewingRetraction.wordValue first boundary, SewingRetraction.wordValue
          second outward + SewingRetraction.wordValue second boundary⟩
          ⟨-(SewingRetraction.wordValue first outward + SewingRetraction.wordValue first other),
            -(SewingRetraction.wordValue second outward + SewingRetraction.wordValue second other)⟩ := by
  intro stem hole outward other boundary polygon
  have expanded := BilinearPolarization.extract_congr (fun coefficient => bank.resplit_loop_area included edges vertices
    reference index sheet
    (BilinearPolarization.mix first second coefficient) (BilinearPolarization.mix_reverse first second firstAnti
      secondAnti coefficient))
  have distribute : BilinearPolarization.extract (fun coefficient =>
      RetracingWords.wordArea (BilinearPolarization.mix first second coefficient) boundary +
        (RetracingWords.wordArea (BilinearPolarization.mix first second coefficient) outward - RetracingWords.wordArea
          (BilinearPolarization.mix first second coefficient) other) +
        BoundaryRibbon.area (SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) outward +
          SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) boundary)
          (-(SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) outward +
            SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) other))) =
      BilinearPolarization.extract (fun coefficient => RetracingWords.wordArea (BilinearPolarization.mix first second
        coefficient) boundary) +
        (BilinearPolarization.extract (fun coefficient => RetracingWords.wordArea (BilinearPolarization.mix first second
          coefficient) outward) -
          BilinearPolarization.extract (fun coefficient => RetracingWords.wordArea (BilinearPolarization.mix first
            second coefficient) other)) +
        BilinearPolarization.extract (fun coefficient => BoundaryRibbon.area
          (SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) outward +
            SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) boundary)
          (-(SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) outward +
            SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) other))) := by
    unfold BilinearPolarization.extract
    ring1
  have crossed : BilinearPolarization.extract (fun coefficient => BoundaryRibbon.area
      (SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) outward +
        SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) boundary)
      (-(SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) outward +
        SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) other))) =
      Stokes.edgeArea ⟨wordValue first outward + SewingRetraction.wordValue first boundary, SewingRetraction.wordValue
        second outward + SewingRetraction.wordValue second boundary⟩
        ⟨-(SewingRetraction.wordValue first outward + SewingRetraction.wordValue first other),
          -(SewingRetraction.wordValue second outward + SewingRetraction.wordValue second other)⟩ := by
    refine (BilinearPolarization.extract_congr (fun coefficient => ?_)).trans
      (BilinearPolarization.extract_area (SewingRetraction.wordValue first outward + SewingRetraction.wordValue first
        boundary) (-(SewingRetraction.wordValue first outward + SewingRetraction.wordValue first other))
        (SewingRetraction.wordValue second outward + SewingRetraction.wordValue second boundary)
          (-(SewingRetraction.wordValue second outward + SewingRetraction.wordValue second other)))
    rw [BilinearPolarization.word_mix, BilinearPolarization.word_mix, BilinearPolarization.word_mix]
    rw [Data.Gaussian.Basic.conj_add, show Data.Gaussian.Basic.conj (-(SewingRetraction.wordValue first outward
      + SewingRetraction.wordValue first other)) =
      -Data.Gaussian.Basic.conj (SewingRetraction.wordValue first outward + SewingRetraction.wordValue first
        other) from rfl, Data.Gaussian.Basic.conj_add]
    apply congrArg₂ BoundaryRibbon.area <;> ring1
  have identity := expanded.trans distribute
  rw [BilinearPolarization.extract_wordArea_mix, BilinearPolarization.extract_wordArea_mix,
    BilinearPolarization.extract_wordArea_mix, BilinearPolarization.extract_wordArea_mix, crossed] at identity
  exact identity

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearStemArea
