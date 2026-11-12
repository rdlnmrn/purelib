module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
public import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # Cached classification of the original located primitive fragments

The original splitting, parent and cell-location spines remain inputs.
Each actual located cell is looked up once in the same retained face bank.
Regular and hole outcomes keep their original payloads and positions; a
hole is not promoted to a regular face or discarded from the ordered word.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces LocatedCell)

variable {genus : Nat} {curve : HyperellipticCurve genus}
variable {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {differential : Differential genus} {axes : PrimitiveAxes bank.grid}

namespace PrimitiveFragmentCells

variable {parent : CenteredEdge curve differential}
variable {partition : Geometry.Rectangle.AxisPartition 0 1 (axes.parameters parent)}

/-- One original regular-or-hole payload for every actual retained fragment cell, in unchanged interval order. -/
@[expose] def Classifications (faces : PuncturedFaces bank) :
    {intervals : List PreparedAxisPartitions.Interval} →
    PrimitiveFragmentCells axes parent partition intervals → Type
  | _, .nil => PUnit
  | _, .cons first remaining =>
      LocatedCell faces.regulars faces.holes first.cell × Classifications faces remaining

/-- Classify each already located cell once without reconstructing its source fragment or midpoint location. -/
def classify (faces : PuncturedFaces bank) :
    {intervals : List PreparedAxisPartitions.Interval} →
    (located : PrimitiveFragmentCells axes parent partition intervals) → Classifications faces located
  | _, .nil => PUnit.unit
  | _, .cons first remaining =>
      ⟨faces.locateCell first.cell first.cell_member, classify faces remaining⟩

end PrimitiveFragmentCells

namespace LocatedPrimitiveSplits

/-- Retain every actual original parent and interval while storing its regular-or-hole cell classification. -/
@[expose] def Classifications (faces : PuncturedFaces bank) :
    {parents : List (CenteredEdge curve differential)} → {splits : PrimitiveSplits axes parents} →
    LocatedPrimitiveSplits axes splits → Type
  | _, _, .nil => PUnit
  | _, _, .cons first remaining =>
      PrimitiveFragmentCells.Classifications faces first × Classifications faces remaining

/-- Classify the same complete located splitting once, preserving all original parent and interval occurrences. -/
def classify (faces : PuncturedFaces bank) :
    {parents : List (CenteredEdge curve differential)} → {splits : PrimitiveSplits axes parents} →
    (located : LocatedPrimitiveSplits axes splits) → Classifications faces located
  | _, _, .nil => PUnit.unit
  | _, _, .cons first remaining =>
      ⟨PrimitiveFragmentCells.classify faces first, classify faces remaining⟩

end LocatedPrimitiveSplits

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells

end
