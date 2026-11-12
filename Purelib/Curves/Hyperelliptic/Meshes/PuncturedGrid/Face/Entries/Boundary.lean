module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
public import Purelib.Polynomial.Geometry.Grid.CellContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.RootContinuation.RootPathTransport
public import Purelib.Riemann.Paths.ClearBoxPaths.Parameter
public import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Tactic.Ring

/-! # Original grid-side positions and retained face-entry rows at a contact

A true side incidence gives an exact parameter on that original oriented
full grid side. The row dispatcher reads only the already retained Entry
acquisition: outward on bottom, right and left, inward on top. Inward keeps
its actual point-to-anchor orientation; no reversed trace is fabricated.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.EdgePoint

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Polynomial.Geometry.Grid.Walks (Edge)

variable {genus : Nat} {curve : HyperellipticCurve genus} {ambient : Geometry.Rational.Box}
variable {grid : ClearGrid curve.polynomial ambient} {start finish point : Canonical}
variable {edge : Edge grid start finish}

/-- Reverse the original containing edge and complement its retained closed-unit parameter. -/
@[expose] def reverse (location : EdgePoint edge point) : EdgePoint (.reverse edge) point := by
  have upper := Fraction.Order.Arithmetic.sub_le_sub_left_direct location.inside.1 1
  have upperBound : 1 - location.parameter ≤ 1 :=
    upper.trans_eq (by ring1)
  refine ⟨1 - location.parameter,
    ⟨Fraction.Order.Arithmetic.sub_nonneg_direct location.inside.2, upperBound⟩, ?_⟩
  change (ClearSegment.reverse edge.segment).pointAt (1 - location.parameter) = point
  rewrite [ClearSegment.reverse_pointAt, show 1 - (1 - location.parameter) = location.parameter by ring1]
  exact location.point_eq

/-- Reversal retains exactly the complementary parameter on the same original edge occurrence. -/
theorem reverse_parameter (location : EdgePoint edge point) :
    location.reverse.parameter = 1 - location.parameter := rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces.EdgePoint

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (EdgePoint FragmentGridEdge)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell Interval)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}

/-- Locate a contained boundary point on the actual oriented full side of the same regular face.

All interval and line payloads come from the face's original cell membership.
Top and left reverse that same complete edge and its rational parameter.
-/
@[expose] def boundaryPoint (face : RegularFace bank) (side : GridSide) (point : Canonical)
    (inside : face.cell.box.Contains point) (onSide : face.cell.OnSide point side) :
    EdgePoint (face.side side) point := by
  let intervals := FragmentGridEdge.cell_intervals face.member
  cases side with
  | bottom =>
      exact EdgePoint.horizontal face.cell.horizontal intervals.1 face.cell.vertical.lower
        (Interval.endpoints_mem _ bank.grid.horizontal_ordered intervals.2).1 point
        ⟨inside.1, inside.2.1⟩ onSide
  | right =>
      exact EdgePoint.vertical face.cell.vertical intervals.2 face.cell.horizontal.upper
        (Interval.endpoints_mem _ bank.grid.vertical_ordered intervals.1).2 point inside.2.2 onSide
  | top =>
      exact (EdgePoint.horizontal face.cell.horizontal intervals.1 face.cell.vertical.upper
        (Interval.endpoints_mem _ bank.grid.horizontal_ordered intervals.2).2 point
        ⟨inside.1, inside.2.1⟩ onSide).reverse
  | left =>
      exact (EdgePoint.vertical face.cell.vertical intervals.2 face.cell.horizontal.lower
        (Interval.endpoints_mem _ bank.grid.vertical_ordered intervals.1).1 point inside.2.2 onSide).reverse

end Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (EdgePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.RootContinuation.RootPathTransport (PathTransport)
open Purelib.Riemann.Paths
open Purelib.Geometry.Rational.Box.Boundary (OnBoxBoundary)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : RegularFace bank}
variable {models : FaceModels frames face} {point : Canonical}
variable {inside : face.cell.box.Contains point} {owner : Owner (curve.polynomial.eval point)}

/-- Read an original retained two-way transport bank in the direction selected for a boundary side.

The left and bottom cases use outward. Right uses outward's bottom then
right legs; top uses inward's top then left legs. The latter is kept in its
actual inward orientation, with both retained row caches unchanged.
-/
@[expose] def boundaryTransport (acquired : Acquisition models inside owner) (side : GridSide) :
    PathTransport acquired.outward.path models.frame acquired.pointFrame ⊕
      PathTransport acquired.inward.path acquired.pointFrame models.frame :=
  match side with
  | .top => .inr acquired.backward
  | .bottom | .right | .left => .inl acquired.forward

/-- The bottom case reads the complete retained forward bank. -/
theorem boundaryTransport_bottom (acquired : Acquisition models inside owner) :
    acquired.boundaryTransport .bottom = .inl acquired.forward := rfl

/-- The right case reads the complete retained forward bank. -/
theorem boundaryTransport_right (acquired : Acquisition models inside owner) :
    acquired.boundaryTransport .right = .inl acquired.forward := rfl

/-- The left case reads the complete retained forward bank, including an empty anchor route. -/
theorem boundaryTransport_left (acquired : Acquisition models inside owner) :
    acquired.boundaryTransport .left = .inl acquired.forward := rfl

/-- The top case reads the complete retained backward bank without reversing or replaying it. -/
theorem boundaryTransport_top (acquired : Acquisition models inside owner) :
    acquired.boundaryTransport .top = .inr acquired.backward := rfl

/-- The selected actual retained route stays on the same face boundary at every unit parameter.

Top reads the original inward route; all other sides read outward. The
proof uses the original build's zero/one/two-edge coordinate laws and the
same cached whole-route equations, not a new path or boundary observer.
-/
theorem boundary_path (acquired : Acquisition models inside owner) (side : GridSide)
    (onSide : face.cell.OnSide point side) (time : Data.Rat.Fraction.Rational)
    (timeInside : 0 ≤ time ∧ time ≤ 1) :
    match side with
    | .top => OnBoxBoundary face.cell.box (acquired.inward.pointAt time)
    | .bottom | .right | .left =>
        OnBoxBoundary face.cell.box (acquired.outward.pointAt time) := by
  cases side with
  | bottom =>
      have fixed := ClearBoxPaths.Route.build_pointAt_horizontal face.clearance
        face.cell.box.anchor point face.cell.box.contains_anchor inside onSide.symm time
      rewrite [← acquired.outward_eq] at fixed
      exact ⟨acquired.outward.pointAt_contains face.cell.box.contains_anchor timeInside,
        Or.inr (Or.inr (Or.inl fixed))⟩
  | right =>
      have axes := ClearBoxPaths.Route.build_pointAt_axes face.clearance
        face.cell.box.anchor point face.cell.box.contains_anchor inside time
      rewrite [← acquired.outward_eq] at axes
      refine ⟨acquired.outward.pointAt_contains face.cell.box.contains_anchor timeInside, ?_⟩
      rcases axes with bottom | right
      · exact Or.inr (Or.inr (Or.inl bottom))
      · exact Or.inr (Or.inl (right.trans onSide))
  | top =>
      have axes := ClearBoxPaths.Route.build_pointAt_axes face.clearance
        point face.cell.box.anchor inside face.cell.box.contains_anchor time
      rewrite [← acquired.inward_eq] at axes
      refine ⟨acquired.inward.pointAt_contains inside timeInside, ?_⟩
      rcases axes with top | left
      · exact Or.inr (Or.inr (Or.inr (top.trans onSide)))
      · exact Or.inl left
  | left =>
      have fixed := ClearBoxPaths.Route.build_pointAt_vertical face.clearance
        face.cell.box.anchor point face.cell.box.contains_anchor inside onSide.symm time
      rewrite [← acquired.outward_eq] at fixed
      exact ⟨acquired.outward.pointAt_contains face.cell.box.contains_anchor timeInside, Or.inl fixed⟩

section Pair

variable {otherFace : RegularFace bank} {otherModels : FaceModels frames otherFace}
variable {otherInside : otherFace.cell.box.Contains point}
variable {otherOwner : Owner (curve.polynomial.eval point)}
variable (left : Acquisition models inside owner)
variable (right : Acquisition otherModels otherInside otherOwner)

/-- The exact same-cell or paired-side result over both original retained acquisitions.

A nontrivial case retains both original side positions and both complete
transport banks. A corner remains a corner because the two axis flags stay
in the supplied original Contacts value, rather than being erased to a
claim that the selected full sides coincide.
-/
@[expose] def ContactRows (contact : Cell.Contacts face.cell otherFace.cell point) : Type :=
  match contact.sides with
  | none => Unit
  | some sides =>
      (EdgePoint (face.side sides.1) point ×
        (PathTransport left.outward.path models.frame left.pointFrame ⊕
          PathTransport left.inward.path left.pointFrame models.frame)) ×
      (EdgePoint (otherFace.side sides.2) point ×
        (PathTransport right.outward.path otherModels.frame right.pointFrame ⊕
          PathTransport right.inward.path right.pointFrame otherModels.frame))

/-- Dispatch the actual shared-point geometry and read both retained acquisition banks once.

The same-cell case has no crossing. Each contact case derives its two real
full-side positions internally from the original cell containment and
contact proof; the banks are exact getters on left and right.
-/
def contactRows (contact : Cell.Contacts face.cell otherFace.cell point) : ContactRows left right contact := by
  unfold ContactRows
  cases selected : contact.sides with
  | none => exact ()
  | some sides =>
      have incidence := contact.sides_spec
      rewrite [selected] at incidence
      change face.cell.OnSide point sides.1 ∧ otherFace.cell.OnSide point sides.2 at incidence
      exact ⟨⟨face.boundaryPoint sides.1 point inside incidence.1, left.boundaryTransport sides.1⟩,
        ⟨otherFace.boundaryPoint sides.2 point otherInside incidence.2, right.boundaryTransport sides.2⟩⟩

/-- Produce contact from the actual two regular cell occurrences and retain the whole dispatch result.

The only new computation is the finite scalar contact test. No Entry frame,
transport, query, primitive observation or paid source execution is rebuilt.
-/
def atContact :
    Σ contact : {value : Cell.Contacts face.cell otherFace.cell point //
      value = Cell.contactAt face.cell otherFace.cell face.member otherFace.member point inside otherInside},
      {value : ContactRows left right contact.val // value = contactRows left right contact.val} :=
  let contact := Cell.contactAt face.cell otherFace.cell face.member otherFace.member point inside otherInside
  let rows := contactRows left right contact
  ⟨⟨contact, rfl⟩, ⟨rows, rfl⟩⟩

/-- The retained geometry is exactly the actual two-cell contact factory result. -/
theorem atContact_geometry : (atContact left right).1.val =
    Cell.contactAt face.cell otherFace.cell face.member otherFace.member point inside otherInside :=
  (atContact left right).1.property

/-- The whole retained dispatch is exactly the reader of those same two acquisition caches. -/
theorem atContact_rows : (atContact left right).2.val = contactRows left right (atContact left right).1.val :=
  (atContact left right).2.property

end Pair
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

end
