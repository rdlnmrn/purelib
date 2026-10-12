module
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowRootTransport

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Integration.Path

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.Topology.Mesh

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-!
# The actual return stem and its opposite-sheet defects

The winding-one excursion determines the return sheet through the cached
transport bijections. No root equality is inferred from coordinate equality.
Both defects are expressed on the two forward stems, so paired edge
comparisons can control them without preparing an independent return path.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Mesh.RetracingWords (wordArea wordArea_reverse)
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (stemError)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_reverse)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base}

/-- The actual return stem is the reversed original forward stem on the opposite sheet, using the retained transport
bijections. -/
theorem
  returnWord_reverse
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted)
    (index : BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    bank.returnWord index sheet = CutPath.reverse (bank.stemWord index (BranchCutLifts.otherSheet sheet)) := by
  let entry := bank.rows.get index
  let reference := fun point member => (BranchCellBank.referenceAt base.bank.toBranchCellBank point member).toLoop
  have returned := RootEdgeBank.target_odd lifted.edges entry.reference.walk (FramedBranchCellBank.baseMember base.bank)
    0
    (entry.reference.winding.trans (by decide)) sheet
  rw [entry.reference_eq, RootEdgeBank.target_append lifted.edges, RootEdgeBank.target_append lifted.edges] at returned
  have arrival : RootEdgeBank.target lifted.edges entry.boundary (RootEdgeBank.target lifted.edges entry.stem sheet) =
      RootEdgeBank.target lifted.edges entry.stem (BranchCutLifts.otherSheet sheet) := by
    apply lifted.edges.target_injective reference entry.stem.reverse
    rw [returned, lifted.edges.target_reverse reference entry.stem]
  change lifted.edges.indexedEdges lifted.vertices entry.stem.reverse
    (RootEdgeBank.target lifted.edges entry.boundary (RootEdgeBank.target lifted.edges entry.stem sheet)) = _
  rw [arrival, lifted.edges.indexedEdges_reverse lifted.vertices reference]
  rfl

/-- Reuse the forward paired face placements for the return leg, with the actual opposite sheet and reversed edge order.
-/
theorem
  returnWord_sources
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted)
    (index : BranchIsolation.Data.Index branches) (sheet : Fin 2)
    (paired : WalkOccurrences.PairedWalk lifted.mesh (bank.rows.get index).stem) :
    bank.returnWord index sheet = CutPath.reverse
      ((paired.sources (BranchCutLifts.otherSheet sheet)).map
        (fun source => source.project lifted.mesh.triangulation.faces)) := by
  rw [paired.sources_project, bank.returnWord_reverse]
  rfl

/-- The area difference and the opposite-sheet increment sum are distinct obligations. In particular a vanishing sum
alone does not erase the area. -/
theorem
  stemError_opposite
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted)
    (value : OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge)
    (index : BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    bank.stemError value index sheet =
      RetracingWords.wordArea value (bank.stemWord index sheet) - RetracingWords.wordArea value (bank.stemWord index
        (BranchCutLifts.otherSheet sheet)) +
      BoundaryRibbon.area (SewingRetraction.wordValue value (bank.stemWord index sheet) + SewingRetraction.wordValue
        value (bank.holeWord index sheet))
        (-(SewingRetraction.wordValue value (bank.stemWord index sheet) + SewingRetraction.wordValue value
          (bank.stemWord index (BranchCutLifts.otherSheet sheet)))) := by
  rw [BasedBranchBank.stemError, bank.returnWord_reverse, RetracingWords.wordArea_reverse value anti,
    SewingRetraction.wordValue_reverse value anti]
  rw [show -SewingRetraction.wordValue value (bank.stemWord index (BranchCutLifts.otherSheet sheet)) -
      SewingRetraction.wordValue value (bank.stemWord index sheet) =
      -(SewingRetraction.wordValue value (bank.stemWord index sheet) + SewingRetraction.wordValue value (bank.stemWord
        index (BranchCutLifts.otherSheet sheet))) by ring1]
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
