module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Source
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace
public import Purelib.Polynomial.Geometry.ClearPath.Region
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # The actual ramified-coordinate trace on a retained physical cap segment

The original q=wP clearance supplies an actual w clearance on the same box.
Its identical oriented axis segment is re-cleared by the existing operation.
An original trace budget and checked dyadic preparation construct the whole
w-owner path from the retained quotient t owner, including its actual new
preparation work. No endpoint or pathwise q/P comparison is assumed.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint)
open Purelib.Riemann.Paths renaming PreparedTraceBudget -> TraceBudget
open Purelib.Riemann.Paths.PreparedSubdivisionTrace hiding Box
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)

variable {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {ambient box : Box} {first last : Canonical}

/-- The same physical segment and original complete traced subdivision retain their original factories.

The origin is exactly the supplied overlap's attached t owner after its
proven parameter-index transport. The returned terminal owner is selected
by the actual original continuation algorithm; it is not identified with
an independently attached endpoint quotient by a coordinate equality.
-/
@[expose] def CoordinateTrace
    (original : ClearSegment (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) ambient first last)
    (clearance : RegionClearance (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) box)
    (firstInside : box.Contains first) (lastInside : box.Contains last) (left right : Endpoint)
    (ordered : left.parameter ≤ right.parameter)
    {origin : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval
      (original.pointAt left.parameter))}
    (overlap : Cap.RootCoordinates.Overlap cap (original.pointAt left.parameter) origin) : Type _ :=
  (cleared : { actual : RegionClearance coordinate box //
    actual = coordinateClearance (frame := frame) (cap := cap) clearance }) ×
  (segment : { actual : ClearSegment coordinate box first last //
    actual = original.reclear cleared.val firstInside lastInside ∧ actual.WithinAmbient }) ×
  (budget : { actual : TraceBudget segment.val left right //
    actual = TraceBudget.build segment.val left right }) ×
  { traced : PreparedTraceBudget.TracedSubdivision budget.val segment.property.2 (coordinateOwner overlap) //
    traced = PreparedTraceBudget.traced budget.val segment.property.2 (coordinateOwner overlap) ordered }

/-- Construct the original w continuation on the same physical axis from the same retained operational t owner.

The finite factor-clearance transfer, original re-clearance, trace budget
and original traced-subdivision constructor are each computed once. The
last retains its actual preparation, fit proof, path and vertex readback.
All new source handoffs, root readings and endpoint retention remain the
actual original trace work; no old acquisition is described as reused.
-/
def coordinateTrace
    (original : ClearSegment (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) ambient first last)
    (clearance : RegionClearance (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) box)
    (firstInside : box.Contains first) (lastInside : box.Contains last) (left right : Endpoint)
    (ordered : left.parameter ≤ right.parameter)
    {origin : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval
      (original.pointAt left.parameter))}
    (overlap : Cap.RootCoordinates.Overlap cap (original.pointAt left.parameter) origin) :
    CoordinateTrace original clearance firstInside lastInside left right ordered overlap :=
  let cleared := coordinateClearance (frame := frame) (cap := cap) clearance
  let segment := original.reclear cleared firstInside lastInside
  have within : segment.WithinAmbient := original.reclear_withinAmbient cleared firstInside lastInside
  let budget := TraceBudget.build segment left right
  let traced := PreparedTraceBudget.traced budget within (coordinateOwner overlap) ordered
  ⟨⟨cleared, rfl⟩, ⟨segment, rfl, within⟩, ⟨budget, rfl⟩, ⟨traced, rfl⟩⟩

/-- The whole physical trace factory retains all four actual original operations and their complete returned caches. -/
private theorem packaged_coordinateTrace_factory
    (original : ClearSegment (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) ambient first last)
    (clearance : RegionClearance (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) box)
    (firstInside : box.Contains first) (lastInside : box.Contains last) (left right : Endpoint)
    (ordered : left.parameter ≤ right.parameter)
    {origin : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval
      (original.pointAt left.parameter))}
    (overlap : Cap.RootCoordinates.Overlap cap (original.pointAt left.parameter) origin) :
    coordinateTrace original clearance firstInside lastInside left right ordered overlap =
      (let cleared := coordinateClearance (frame := frame) (cap := cap) clearance
       let segment := original.reclear cleared firstInside lastInside
       have within : segment.WithinAmbient := original.reclear_withinAmbient cleared firstInside lastInside
       let budget := TraceBudget.build segment left right
       let traced := PreparedTraceBudget.traced budget within (coordinateOwner overlap) ordered
       ⟨⟨cleared, rfl⟩, ⟨segment, rfl, within⟩, ⟨budget, rfl⟩, ⟨traced, rfl⟩⟩ :
        CoordinateTrace original clearance firstInside lastInside left right ordered overlap) := by rfl

/-- The whole physical trace factory retains all four actual original operations and their complete returned caches. -/
theorem coordinateTrace_factory
    (original : ClearSegment (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) ambient first last)
    (clearance : RegionClearance (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) box)
    (firstInside : box.Contains first) (lastInside : box.Contains last) (left right : Endpoint)
    (ordered : left.parameter ≤ right.parameter)
    {origin : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval
      (original.pointAt left.parameter))}
    (overlap : Cap.RootCoordinates.Overlap cap (original.pointAt left.parameter) origin) :
    coordinateTrace original clearance firstInside lastInside left right ordered overlap =
      (let cleared := coordinateClearance (frame := frame) (cap := cap) clearance
       let segment := original.reclear cleared firstInside lastInside
       have within : segment.WithinAmbient := original.reclear_withinAmbient cleared firstInside lastInside
       let budget := TraceBudget.build segment left right
       let traced := PreparedTraceBudget.traced budget within (coordinateOwner overlap) ordered
       ⟨⟨cleared, rfl⟩, ⟨segment, rfl, within⟩, ⟨budget, rfl⟩, ⟨traced, rfl⟩⟩ :
        CoordinateTrace original clearance firstInside lastInside left right ordered overlap) :=
  packaged_coordinateTrace_factory original clearance firstInside lastInside left right ordered overlap

namespace CoordinateTrace

variable {original : ClearSegment (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) ambient first last}
    {clearance : RegionClearance (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) box}
    {firstInside : box.Contains first} {lastInside : box.Contains last} {left right : Endpoint}
    {ordered : left.parameter ≤ right.parameter}
    {origin : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval
      (original.pointAt left.parameter))}
    {overlap : Cap.RootCoordinates.Overlap cap (original.pointAt left.parameter) origin}

/-- Read the same complete cached owner path without rerunning the preparation or trace constructor. -/
def path (retained : CoordinateTrace original clearance firstInside lastInside left right ordered overlap) :
    OwnerPath coordinate (retained.2.1.val.pointAt left.parameter) (coordinateOwner overlap)
      (retained.2.1.val.pointAt retained.2.2.2.val.subdivision.endpoint.parameter)
      retained.2.2.2.val.subdivision.terminalOwner :=
  retained.2.2.2.val.path

/-- Every actual re-cleared path parameter is the original physical point with its original orientation. -/
theorem pointAt (retained : CoordinateTrace original clearance firstInside lastInside left right ordered overlap)
    (time : Data.Rat.Fraction.Rational) : retained.2.1.val.pointAt time = original.pointAt time := by
  exact (congrArg (fun segment : ClearSegment coordinate box first last => segment.pointAt time)
    retained.2.1.property.1).trans (original.reclear_pointAt retained.1.val firstInside lastInside time)

/-- The exact actual prepared request list, including repeated handoffs, determines the retained trace vertices. -/
private theorem packaged_vertices
    (retained : CoordinateTrace original clearance firstInside lastInside left right ordered overlap) :
    retained.path.vertices =
      PreparedTraceBudget.traceVertices retained.2.1.val
        left retained.2.2.2.val.subdivision.requests := retained.2.2.2.val.vertices_eq

/-- The exact actual prepared request list, including repeated handoffs, determines the retained trace vertices. -/
theorem vertices (retained : CoordinateTrace original clearance firstInside lastInside left right ordered overlap) :
    retained.path.vertices =
      PreparedTraceBudget.traceVertices retained.2.1.val
        left retained.2.2.2.val.subdivision.requests := packaged_vertices retained

end CoordinateTrace

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential

end
