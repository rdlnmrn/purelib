module
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
public import Purelib.Riemann.Paths.RectangularHorizontalTraceLengths
public import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Riemann.Paths.RectangularVerticalTraceLengths
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation
import Purelib.Riemann.Integration.RectangularPerimeterLengths
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib.Curves

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! Automatic comparison geometry on the retained perimeter indices. The
local owner supplies containment; each side's coordinate identity supplies
its straight segments, including all coincident junctions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation

open Purelib.Riemann.Paths.RectangularHorizontalTraceLengths
open Purelib.Riemann.Paths.RectangularVerticalTraceLengths

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : Meshes.PuncturedGridFaces.RegularFace bank}
      {models
    : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face}
  {sheet : Fin 2} (domain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain models sheet)
  {cuts : Paths.RectangularSegmentSplitting.GridCuts domain.geometry}
  {mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts face.cell.box}

namespace SideGeometry

/-- Prepare the original bottom perimeter geometry from its retained local owners and exact straight-coordinate
identity. -/
def bottom (traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh) :
    Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry models (fun vertex => traces.bottom.point
      (traces.bottom.vertices.indexed vertex)) :=
  .horizontal models _ (fun vertex =>
    let owner := traces.bottom.leftOwner (traces.bottom.vertices.indexed vertex)
    (domain.patch.cell_refines owner.column owner.row).contains owner.contains)
    (fun vertex => Paths.RectangularHorizontalTraceLengths.point_height traces.bottom (traces.bottom.vertices.indexed
      vertex))

/-- Prepare the original top perimeter geometry from its retained local owners and exact straight-coordinate identity.
-/
def top (traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh) :
    Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry models (fun vertex => traces.top.point
      (traces.top.vertices.indexed vertex)) :=
  .horizontal models _ (fun vertex =>
    let owner := traces.top.leftOwner (traces.top.vertices.indexed vertex)
    (domain.patch.cell_refines owner.column owner.row).contains owner.contains)
    (fun vertex => Paths.RectangularHorizontalTraceLengths.point_height traces.top (traces.top.vertices.indexed vertex))

/-- Prepare the original left perimeter geometry from its retained local owners and exact straight-coordinate identity.
-/
def left (traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh) :
    Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry models (fun vertex => traces.left.point
      (traces.left.vertices.indexed vertex)) :=
  .vertical models _ (fun vertex =>
    let owner := traces.left.leftOwner (traces.left.vertices.indexed vertex)
    (domain.patch.cell_refines owner.column owner.row).contains owner.contains)
    (fun vertex => Paths.RectangularVerticalTraceLengths.point_horizontal traces.left (traces.left.vertices.indexed
      vertex))

/-- Prepare the original right perimeter geometry from its retained local owners and exact straight-coordinate identity.
-/
def right (traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh) :
    Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation.SideGeometry models (fun vertex => traces.right.point
      (traces.right.vertices.indexed vertex)) :=
  .vertical models _ (fun vertex =>
    let owner := traces.right.leftOwner (traces.right.vertices.indexed vertex)
    (domain.patch.cell_refines owner.column owner.row).contains owner.contains)
    (fun vertex => Paths.RectangularVerticalTraceLengths.point_horizontal traces.right (traces.right.vertices.indexed
      vertex))

end SideGeometry
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SidePreparation
