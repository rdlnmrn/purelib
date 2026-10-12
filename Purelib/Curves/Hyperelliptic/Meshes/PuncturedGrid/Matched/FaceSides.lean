module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.ObservationSides
public import Purelib.Riemann.Readings.RectangularObservationEndpoints
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Riemann.Readings.RectangularMatchedObservationSides

@[expose] public section

/-! Physical neighboring faces determine the retained boundary intervals. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FaceSides

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List
    (Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace bank)} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}
  {cuts : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
    {target : Purelib.Data.Rat.Fraction.Rational}

variable (request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet
  => Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target)

/-- Match the actual top and bottom observation boundaries of two vertically adjacent retained faces.

The supplied horizontal interval equalities and physical adjacency retain both original sheet-specific meshes and their
boundary-row identities. -/
def matchedTopBottom (firstSheet lastSheet : Fin 2) (first last : Fin faces.length)
    (lowerEq : faces[first.val].cell.box.xLower = faces[last.val].cell.box.xLower)
    (upperEq : faces[first.val].cell.box.xUpper = faces[last.val].cell.box.xUpper)
    (adjacent : faces[first.val].cell.box.yUpper = faces[last.val].cell.box.yLower) :
    let firstMesh := (request.entries.get firstSheet).meshes.entries.get first
    let lastMesh := (request.entries.get lastSheet).meshes.entries.get last
    ObservationMesh.MatchedHorizontalSide firstMesh lastMesh
      (Fin.cast firstMesh.boundaryRows_eq (Fin.last firstMesh.boundaryRows))
      (Fin.cast lastMesh.boundaryRows_eq 0) faces[first.val].cell.box.yUpper := by
  let firstMesh := (request.entries.get firstSheet).meshes.entries.get first
  let lastMesh := (request.entries.get lastSheet).meshes.entries.get last
  apply ObservationSides.matchedHorizontalSide request
    firstSheet lastSheet first last lowerEq upperEq
  · have equal := firstMesh.y_last
    exact ⟨(firstMesh.partition.y.intervals[Fin.cast firstMesh.boundaryRows_eq
      (Fin.last firstMesh.boundaryRows)]).ordered.le.trans equal.le, equal.ge⟩
  · have equal := lastMesh.y_first
    have endpointEq := equal.trans adjacent.symm
    exact ⟨endpointEq.le, endpointEq.symm.le.trans
      (lastMesh.partition.y.intervals[Fin.cast lastMesh.boundaryRows_eq 0]).ordered.le⟩

/-- Match the actual right and left observation boundaries of two horizontally adjacent retained faces.

The supplied vertical interval equalities and physical adjacency retain both original sheet-specific meshes and their
boundary-column identities. -/
def matchedRightLeft (firstSheet lastSheet : Fin 2) (first last : Fin faces.length)
    (lowerEq : faces[first.val].cell.box.yLower = faces[last.val].cell.box.yLower)
    (upperEq : faces[first.val].cell.box.yUpper = faces[last.val].cell.box.yUpper)
    (adjacent : faces[first.val].cell.box.xUpper = faces[last.val].cell.box.xLower) :
    let firstMesh := (request.entries.get firstSheet).meshes.entries.get first
    let lastMesh := (request.entries.get lastSheet).meshes.entries.get last
    ObservationMesh.MatchedVerticalSide firstMesh lastMesh
      (Fin.cast firstMesh.boundaryColumns_eq (Fin.last firstMesh.boundaryColumns))
      (Fin.cast lastMesh.boundaryColumns_eq 0) faces[first.val].cell.box.xUpper := by
  let firstMesh := (request.entries.get firstSheet).meshes.entries.get first
  let lastMesh := (request.entries.get lastSheet).meshes.entries.get last
  apply ObservationSides.matchedVerticalSide request
    firstSheet lastSheet first last lowerEq upperEq
  · have equal := firstMesh.x_last
    exact ⟨(firstMesh.partition.x.intervals[Fin.cast firstMesh.boundaryColumns_eq
      (Fin.last firstMesh.boundaryColumns)]).ordered.le.trans equal.le, equal.ge⟩
  · have equal := lastMesh.x_first
    have endpointEq := equal.trans adjacent.symm
    exact ⟨endpointEq.le, endpointEq.symm.le.trans
      (lastMesh.partition.x.intervals[Fin.cast lastMesh.boundaryColumns_eq 0]).ordered.le⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FaceSides
