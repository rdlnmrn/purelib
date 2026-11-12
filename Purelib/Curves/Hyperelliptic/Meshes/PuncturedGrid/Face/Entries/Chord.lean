module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Transport
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Data.Int.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedPathWinding

/-! # Original face entries along actual one-link physical crops

The actual OwnerPath retains its two nominal Owners and one target
occurrence. Its source segment determines the integer winding, including
stationary crops. The same original clear face then propagates the Entry;
no Point, owner selector, trace or root comparison is acquired.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Riemann
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {frames : RootFrames bank.grid} {face : RegularFace bank} {models : FaceModels frames face}

/-- Follow the actual one-target OwnerPath along its original contained axis segment.

The retained vertex equation computes this path's winding. The original
segment and whole-face clearance derive the required endpoint potential
difference; no same-sheet or operational root relation is supplied.
-/
def followSegment {ambient : Box} {first last : Canonical}
    {source : Owner (curve.polynomial.eval first)} {target : Owner (curve.polynomial.eval last)}
    (entry : Entry models first source) (segment : ClearSegment curve.polynomial ambient first last)
    (moving : OwnerPath curve.polynomial first source last target) (vertices : moving.vertices = [last])
    (firstInside : face.cell.box.Contains first) (lastInside : face.cell.box.Contains last) :
    Entry models last target := by
  have actual := congrArg (chainRaw curve.polynomial first) vertices
  change chainRaw curve.polynomial first moving.vertices =
    Paths.PreparedPathWinding.ClearSegment.rawWinding segment + 0 at actual
  have winding := Paths.ClearBoxPathWinding.ClearBoxPaths.segment_winding face.clearance
    (BranchIsolation.degreePositive curve) segment firstInside lastInside
  let raw := Paths.PreparedPathWinding.ClearSegment.rawWinding segment
  have removeZero := (Data.Int.Arithmetic.add_comm raw 0).trans (Data.Int.Arithmetic.zero_add raw)
  exact ⟨entry.sheet, entry.reached.append ⟨moving, actual.trans (removeZero.trans winding)⟩⟩

/-- The actual segment propagation retains the original face sheet. -/
theorem followSegment_sheet {ambient : Box} {first last : Canonical}
    {source : Owner (curve.polynomial.eval first)} {target : Owner (curve.polynomial.eval last)}
    (entry : Entry models first source) (segment : ClearSegment curve.polynomial ambient first last)
    (moving : OwnerPath curve.polynomial first source last target) (vertices : moving.vertices = [last])
    (firstInside : face.cell.box.Contains first) (lastInside : face.cell.box.Contains last) :
    (entry.followSegment segment moving vertices firstInside lastInside).sheet = entry.sheet := by
  unfold followSegment
  rfl

/-- Follow the actual query crop of one retained prepared parent.

The same original local segment is restricted at the supplied fractions.
Its actual unit containment and one-target crop equation construct the
Entry propagation internally, without preparing another parent or Query.
-/
def followQueryCrop {basis : Differential genus} (parent : PreparedEdge curve basis)
    (lower upper : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    {source : Owner (curve.polynomial.eval (parent.point lower))}
    {target : Owner (curve.polynomial.eval (parent.point upper))}
    (entry : Entry models (parent.point lower) source)
    (moving : OwnerPath curve.polynomial (parent.point lower) source (parent.point upper) target)
    (vertices : moving.vertices = [parent.point upper])
    (firstInside : face.cell.box.Contains (parent.point lower))
    (lastInside : face.cell.box.Contains (parent.point upper)) : Entry models (parent.point upper) target :=
  let localInside :=
    Eq.mp (congrArg parent.ambient.Contains parent.localSegment.pointAt_zero)
      (parent.point_contains 0 parent.baseInside)
  let within := parent.localSegment.withinAmbient_of_start localInside
  let restricted := parent.localSegment.restrict within lower upper lowerInside upperInside
  entry.followSegment restricted moving vertices firstInside lastInside

/-- The actual prepared-parent crop retains the same original face sheet. -/
theorem followQueryCrop_sheet {basis : Differential genus} (parent : PreparedEdge curve basis)
    (lower upper : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    {source : Owner (curve.polynomial.eval (parent.point lower))}
    {target : Owner (curve.polynomial.eval (parent.point upper))}
    (entry : Entry models (parent.point lower) source)
    (moving : OwnerPath curve.polynomial (parent.point lower) source (parent.point upper) target)
    (vertices : moving.vertices = [parent.point upper])
    (firstInside : face.cell.box.Contains (parent.point lower))
    (lastInside : face.cell.box.Contains (parent.point upper)) :
    (entry.followQueryCrop parent lower upper lowerInside upperInside moving vertices firstInside lastInside).sheet =
      entry.sheet := by
  unfold followQueryCrop
  exact followSegment_sheet _ _ _ _ _ _

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry

end
