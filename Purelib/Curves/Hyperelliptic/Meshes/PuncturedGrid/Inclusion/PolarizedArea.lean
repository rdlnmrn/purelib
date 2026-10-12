module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Paired.Increments
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearArea
import Purelib.Topology.Surface.Boundary.PolarizedWordArea
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib.Integration.Path

open Purelib.Integration.Path.Paired

open Purelib.Topology.Mesh

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-! The resplit ordered residual in two-differential physical word areas.
The terminal/reference cross and the internal branch excursions are retained.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea (resplitInternalArea resplitReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BilinearArea (resplitResidual)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
open Purelib.Topology.Surface.Boundary.PolarizedWordArea

open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial
    (Ambient curve)}
  (included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion base.bank.grid grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid)

/-- Polarizing the internal area retains both single-branch excursions for every ordered pair, on their actual incoming
sheets. -/
theorem resplitInternalArea_extract (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (newSheet : Fin 2)
    (first second : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical)
    (labels : List (BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches)) :
    let pairedArea := fun word : List (Stokes.OrientedEdge vertices.count) =>
      PairedIncrementArea.area (word.map (fun edge => (⟨first edge, second edge⟩ : Stokes.PrimitivePoint)))
    BilinearPolarization.extract (fun coefficient => PairedArea.resplitInternalArea included edges vertices bank
      newSheet
      (BilinearPolarization.mix first second coefficient) labels) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (labels.map (fun pair =>
        pairedArea (edges.indexedEdges vertices
          (included.resplit (bank.rows.get pair.1).reference.walk (FramedBranchCellBank.baseMember base.bank)) newSheet)
            +
        pairedArea (edges.indexedEdges vertices
          (included.resplit (bank.rows.get pair.2).reference.walk (FramedBranchCellBank.baseMember base.bank))
          (BranchCutLifts.otherSheet newSheet)))) := by
  intro pairedArea
  induction labels with
  | nil =>
    change (⟨1 / 4, 0⟩ : Data.Gaussian.Basic.Canonical) * (0 - 0 - BilinearPolarization.imaginary * (0 - 0)) = 0
    ring1
  | cons pair rest ih =>
    let firstWord := edges.indexedEdges vertices
      (included.resplit (bank.rows.get pair.1).reference.walk (FramedBranchCellBank.baseMember base.bank)) newSheet
    let secondWord := edges.indexedEdges vertices
      (included.resplit (bank.rows.get pair.2).reference.walk (FramedBranchCellBank.baseMember base.bank))
      (BranchCutLifts.otherSheet newSheet)
    have split : BilinearPolarization.extract (fun coefficient => PairedArea.resplitInternalArea included edges vertices
      bank newSheet
        (BilinearPolarization.mix first second coefficient) (pair :: rest)) =
        (BilinearPolarization.extract (fun coefficient => RetracingWords.wordArea (BilinearPolarization.mix first second
          coefficient) firstWord) +
          BilinearPolarization.extract (fun coefficient => RetracingWords.wordArea (BilinearPolarization.mix first
            second coefficient) secondWord)) +
        BilinearPolarization.extract (fun coefficient => PairedArea.resplitInternalArea included edges vertices bank
          newSheet
          (BilinearPolarization.mix first second coefficient) rest) := by
      unfold BilinearPolarization.extract
      dsimp only [PairedArea.resplitInternalArea, List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
        firstWord, secondWord]
      ring1
    rw [split, BilinearPolarization.extract_wordArea_mix, BilinearPolarization.extract_wordArea_mix, ih]
    rfl

namespace Ordered.Paired.Prepared

variable {ordered :
  Ordered bank
  sheet} {paired : Paired ordered}

/-- The whole resplit residual, in the physical two-differential area convention. The ending word is arbitrary: this
statement does not discard its area or its reference cross, even when a total increment vanishes. -/
theorem resplitResidual_extract (newSheet : Fin 2)
    (first second : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical)
    (ending : List (Stokes.OrientedEdge vertices.count)) :
    let pairedArea := fun word : List (Stokes.OrientedEdge vertices.count) =>
      PairedIncrementArea.area (word.map (fun edge => (⟨first edge, second edge⟩ : Stokes.PrimitivePoint)))
    let priorWord := edges.indexedEdges vertices
      (included.resplit (bank.loopProduct (paired.split.pairs.flatMap (fun pair => [pair.1, pair.2])))
        (FramedBranchCellBank.baseMember base.bank)) newSheet
    let reference := edges.indexedEdges vertices
      (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk (FramedBranchCellBank.baseMember
        base.bank))
      (BranchCutLifts.otherSheet newSheet)
    BilinearPolarization.extract (fun coefficient =>
      BilinearArea.resplitResidual (paired := paired) included edges vertices newSheet
        (BilinearPolarization.mix first second coefficient) ending) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (paired.split.pairs.map (fun pair =>
        pairedArea (edges.indexedEdges vertices
          (included.resplit (bank.rows.get pair.1).reference.walk (FramedBranchCellBank.baseMember base.bank)) newSheet)
            +
        pairedArea (edges.indexedEdges vertices
          (included.resplit (bank.rows.get pair.2).reference.walk (FramedBranchCellBank.baseMember base.bank))
          (BranchCutLifts.otherSheet newSheet)))) + pairedArea ending +
      (SewingRetraction.wordValue first priorWord * (SewingRetraction.wordValue second ending +
        SewingRetraction.wordValue second reference) -
        (SewingRetraction.wordValue first ending + SewingRetraction.wordValue first reference) *
          SewingRetraction.wordValue second priorWord) -
      pairedArea (priorWord ++ ending) := by
  intro pairedArea priorWord reference
  have cross (coefficient : Data.Gaussian.Basic.Canonical) :
      BoundaryRibbon.area
        (Increments.total (PairedArea.resplitReadings included edges vertices bank newSheet
          (BilinearPolarization.mix first second coefficient) paired.split.pairs))
        (SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) ending +
          SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) reference) =
      BoundaryRibbon.area
        (Data.Gaussian.Basic.conj (SewingRetraction.wordValue first priorWord) + coefficient *
          SewingRetraction.wordValue second priorWord)
        (Data.Gaussian.Basic.conj (SewingRetraction.wordValue first ending + SewingRetraction.wordValue first
          reference) +
          coefficient * (SewingRetraction.wordValue second ending + SewingRetraction.wordValue second reference)) := by
    rw [← bank.resplit_pairs_value included edges vertices]
    rw [BilinearPolarization.word_mix, BilinearPolarization.word_mix, BilinearPolarization.word_mix]
    rw [Data.Gaussian.Basic.conj_add]
    congr 1
    ring1
  have split : BilinearPolarization.extract (fun coefficient =>
      BilinearArea.resplitResidual (paired := paired) included edges vertices newSheet
        (BilinearPolarization.mix first second coefficient) ending) =
      BilinearPolarization.extract (fun coefficient => PairedArea.resplitInternalArea included edges vertices bank
        newSheet
        (BilinearPolarization.mix first second coefficient) paired.split.pairs) +
      BilinearPolarization.extract (fun coefficient => RetracingWords.wordArea (BilinearPolarization.mix first second
        coefficient) ending) +
      BilinearPolarization.extract (fun coefficient => BoundaryRibbon.area
        (Increments.total (PairedArea.resplitReadings included edges vertices bank newSheet
          (BilinearPolarization.mix first second coefficient) paired.split.pairs))
        (SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) ending +
          SewingRetraction.wordValue (BilinearPolarization.mix first second coefficient) reference)) -
      BilinearPolarization.extract (fun coefficient => RetracingWords.wordArea (BilinearPolarization.mix first second
        coefficient)
        (priorWord ++ ending)) := by
    unfold BilinearPolarization.extract BilinearArea.resplitResidual
    ring1
  rw [split, Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedArea.resplitInternalArea_extract,
    BilinearPolarization.extract_wordArea_mix,
    BilinearPolarization.extract_wordArea_mix,
    BilinearPolarization.extract_congr cross, BilinearPolarization.extract_area]

end Ordered.Paired.Prepared
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedArea
