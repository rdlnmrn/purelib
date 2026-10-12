module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.RectangularPerimeterTraces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleLiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAdjacentFaces.FramedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Gaussian.Norm.Sum

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Riemann

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularCenteredPerimeter

open Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.RectangularPerimeterTraces

public section

/-! Center the full physical hole remainder on its actual fine side traces.
All four sides, both transported sheets, and every hole are paid. Centered
areas remain explicit for the Newton primitive comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (faceValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (holeAreaRemainder
  rootedHoleCorrection_eq_remainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder (sideCenteredArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas (physicalTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection (holeCorrection
  physicalCorrection_eq_holes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection (holeCorrection_eq_fourSides)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection (HoleSideLifts rootedHoleCorrection_eq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection (physicalComponentCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters (physicalPerimeter)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {target : Rational} {i j : Fin genus} {stage : Nat} {cache :
    Numerics domains stage}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed target}

set_option genInjectivity false in
/-- Keep the trace geometry and centered samples of the supplied bank. -/
structure CenteredPerimeters
    (request : TwoSheetBilinearRequest.TwoSheetRequest (fun sheet => RegularMeshes.build domains cuts sheet coarseDepth)
      fixed target)
    {stage : Nat} (cache : RegularMeshes.Numerics domains stage) (i j : Fin genus) where
  /-- The retained original perimeter trace geometry at each face and sheet. -/ traces : Data.Vector.DependentVector
    (fun position : Fin base.faces.regulars.length =>
    Data.Vector.DependentVector (fun sheet : Fin 2 => RectangularPerimeterTraces.PerimeterTraces ((request.entries.get
      sheet).meshes.entries.get position)))
  /-- The centered samples on those exact traces using the supplied shared face values. -/ samples :
    Data.Vector.DependentVector (fun position : Fin base.faces.regulars.length => Data.Vector.DependentVector (fun sheet
    : Fin 2 =>
    RectangularCenteredPerimeter.Centered ((traces.get position).get sheet) (FacePerimeters.faceValues cache.normalize i
      j position sheet)))

constructive_injectivity CenteredPerimeters

namespace CenteredPerimeters

/-- Build the original face-and-sheet traces once and retain their centered samples on the same shared numerical cache.
-/
@[expose] def build (request : TwoSheetBilinearRequest.TwoSheetRequest (fun sheet => RegularMeshes.build domains cuts
  sheet coarseDepth) fixed target)
    (cache : RegularMeshes.Numerics domains stage) (i j : Fin genus) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j :=
  let traces := DependentVector.ofFn fun position : Fin base.faces.regulars.length =>
    DependentVector.ofFn fun sheet : Fin 2 => PerimeterTraces.build ((request.entries.get sheet).meshes.entries.get
      position)
  ⟨traces, DependentVector.ofFn fun position => DependentVector.ofFn fun sheet =>
    Centered.build ((traces.get position).get sheet) (FacePerimeters.faceValues cache.normalize i j position sheet)⟩

variable {hole : Fin base.faces.holes.length}
  {adjacent : HoleAdjacentFaces
    base (base.faces.holes[hole.val]'hole.isLt)}

/-- The signed centered area of the actual four hole-adjacent sides on both retained sheets. -/
@[expose] def holeArea (samples : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache i j) (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent) : Gaussian :=
  FiniteSum.Fin.sumFin fun sheet =>
    SideCenteredRemainder.sideCenteredArea ((samples.samples.get adjacent.left.position).get (sides.left.get
      sheet).selected.sheet) .right -
    SideCenteredRemainder.sideCenteredArea ((samples.samples.get adjacent.right.position).get (sides.right.get
      sheet).selected.sheet) .left -
    (SideCenteredRemainder.sideCenteredArea ((samples.samples.get adjacent.bottom.position).get (sides.bottom.get
      sheet).selected.sheet) .top -
      SideCenteredRemainder.sideCenteredArea ((samples.samples.get adjacent.top.position).get (sides.top.get
        sheet).selected.sheet) .bottom)

/-- Four squared-norm errors bounded by one allowance give a signed four-term bound of sixteen times that allowance. -/
private theorem four_errors {bound : Fraction.Rational} {x y z w : Data.Gaussian.Basic.Canonical}
    (hx : Data.Gaussian.Norm.Basic.normSq x ≤ bound) (hy : Data.Gaussian.Norm.Basic.normSq y ≤ bound)
      (hz : Data.Gaussian.Norm.Basic.normSq z ≤ bound) (hw : Data.Gaussian.Norm.Basic.normSq w ≤
      bound) :
    Data.Gaussian.Norm.Basic.normSq (x - y - (z - w)) ≤ 16 * bound := by
  have pair {left right : Data.Gaussian.Basic.Canonical} (hl : Data.Gaussian.Norm.Basic.normSq left ≤ bound)
    (hr : Data.Gaussian.Norm.Basic.normSq right ≤ bound) :
      Data.Gaussian.Norm.Basic.normSq (left - right) ≤ 4 * bound :=
    (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct hl hr) (by decide)).trans_eq (by ring1))
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (pair hx hy) (pair hz hw)) (by decide)).trans_eq (by ring1))

/-- The actual hole-area remainder differs from its retained centered side area by at most sixty-four endpoint
allowances. -/
theorem hole_error_bound (samples : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters
  request cache i j) (sides : HoleRootedCorrection.HoleSideLifts lifted adjacent)
    {endpointTarget : Fraction.Rational} (allocated : PerimeterEndpointRequest fixed i j
      endpointTarget)
    (later : allocated.index ≤ stage) (perimeters : Matched.FacePerimeters (request := request) cache.normalize i
      j) :
    Data.Gaussian.Norm.Basic.normSq
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder.holeAreaRemainder perimeters sides -
      samples.holeArea sides) ≤ 64 * endpointTarget := by
  have entry (sheet : Fin 2) :=
    four_errors
    (allocated.bound later ((samples.samples.get adjacent.left.position).get (sides.left.get sheet).selected.sheet)
      perimeters .right)
    (allocated.bound later ((samples.samples.get adjacent.right.position).get (sides.right.get sheet).selected.sheet)
      perimeters .left)
    (allocated.bound later ((samples.samples.get adjacent.bottom.position).get (sides.bottom.get sheet).selected.sheet)
      perimeters .top)
    (allocated.bound later ((samples.samples.get adjacent.top.position).get (sides.top.get sheet).selected.sheet)
      perimeters .bottom)
  have rewrite_error (a b c d x y z w : Data.Gaussian.Basic.Canonical) :
      (a - b - (c - d)) - (x - y - (z - w)) = (a - x) - (b - y) - ((c - z) - (d - w)) := by ring1
  unfold HoleAreaRemainder.holeAreaRemainder RequestedHoleCentering.CenteredPerimeters.holeArea
  rw [← FiniteSum.Fin.sumFin_sub]
  refine (Indexed.normSq_sumFin_le _ (16 * endpointTarget) ?_).trans_eq ?_
  · intro sheet
    rw [rewrite_error]
    exact entry sheet
  · ring1

end CenteredPerimeters

set_option genInjectivity false in
/-- Endpoint requests are independent of the final trace subdivision count. -/
structure HoleCenteringRequest (lifted : Meshes.LiftedPuncturedGrid base)
    (fixed : (sheet : Fin 2) → RegularMeshes.Preflights domains sheet) (i j : Fin genus) (target : Fraction.Rational)
      where
  /-- The requested aggregate hole-centering target is strictly positive. -/ positive : 0 < target
  /-- The retained allowance per original physical hole. -/ perHole : Fraction.Rational
  /-- The per-hole allowance is the exact count-weighted allocation of the aggregate target. -/ perHole_eq : perHole =
    Aggregate.perTerm target base.faces.holes.length
  /-- The original perimeter endpoint request paying one sixty-fourth of the retained per-hole allowance. -/ endpoints :
    PerimeterEndpointRequest fixed i j (perHole / 64)
  /-- The certified four adjacent regular faces for every original physical-hole index. -/ adjacent :
    Data.Vector.DependentVector (fun hole : Fin base.faces.holes.length =>
    HoleAdjacentFaces base (base.faces.holes[hole.val]'hole.isLt))
  /-- The actual two-sheet root lifts of those exact adjacent faces. -/ sides : Data.Vector.DependentVector (fun hole :
    Fin base.faces.holes.length => HoleRootedCorrection.HoleSideLifts lifted (adjacent.get hole))

constructive_injectivity HoleCenteringRequest

namespace HoleCenteringRequest

variable {error : Rational}

/-- Allocate the aggregate target over the original holes and retain their adjacent faces, sheet lifts and paid endpoint
request. -/
@[expose] def build (lifted : Meshes.LiftedPuncturedGrid base) (fixed : (sheet : Fin 2) → RegularMeshes.Preflights
  domains sheet)
    (i j : Fin genus) (target : Fraction.Rational) (positive : 0 < target) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.HoleCenteringRequest lifted fixed i j target :=
  let perHole := Aggregate.perTerm target base.faces.holes.length
  let endpoints := PerimeterEndpointRequest.build fixed i j (perHole / 64)
    (Fraction.Order.Field.div_pos_direct (Aggregate.perTerm_positive positive _) (by decide +kernel))
  let adjacent := DependentVector.ofFn fun hole : Fin base.faces.holes.length =>
    HoleAdjacentFaces.build base (base.faces.holes[hole.val]'hole.isLt)
  ⟨positive, perHole, rfl, endpoints, adjacent,
    DependentVector.ofFn fun hole => HoleSideLifts.build lifted (adjacent.get hole)⟩

/-- The sum of centered side areas over the original indexed physical holes. -/
@[expose] def centeredTotal (allocated :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.HoleCenteringRequest lifted fixed i j error)
    (samples : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j) :
      Gaussian :=
  FiniteSum.Fin.sumFin fun hole => samples.holeArea (allocated.sides.get hole)

/-- This compares the actual global hole correction, not an independently chosen polygon of endpoint increments. Every
fine excursion is retained. -/
theorem total_accurate (allocated :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.HoleCenteringRequest lifted fixed i j error)
    (samples : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j)
      (later : allocated.endpoints.index ≤ stage)
    (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun hole => HoleComponentCorrection.holeCorrection
      perimeters left right hole) - allocated.centeredTotal samples) < error := by
  have perHole (hole : Fin base.faces.holes.length) :
      Data.Gaussian.Norm.Basic.normSq (HoleComponentCorrection.holeCorrection perimeters left right hole -
        samples.holeArea (allocated.sides.get hole)) ≤ allocated.perHole := by
    rw [HoleFourSideCorrection.holeCorrection_eq_fourSides perimeters left right hole (allocated.adjacent.get hole),
      ← HoleRootedCorrection.rootedHoleCorrection_eq perimeters left right (allocated.sides.get hole),
      HoleAreaRemainder.rootedHoleCorrection_eq_remainder perimeters left right (allocated.sides.get hole)]
    exact (samples.hole_error_bound (allocated.sides.get hole) allocated.endpoints later perimeters).trans_eq
      ((show 64 * (allocated.perHole / 64) = allocated.perHole / 64 * 64 by ring1).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)))
  unfold RequestedHoleCentering.HoleCenteringRequest.centeredTotal
  rw [← FiniteSum.Fin.sumFin_sub]
  have estimate := Indexed.normSq_sumFin_le _ allocated.perHole perHole
  rw [allocated.perHole_eq] at estimate
  exact estimate.trans_lt ((show (base.faces.holes.length : Fraction.Rational)^2 *
      Aggregate.perTerm error base.faces.holes.length =
      (base.faces.holes.length : Fraction.Rational) * ((base.faces.holes.length : Fraction.Rational) *
        Aggregate.perTerm error base.faces.holes.length) by ring1).trans_lt
    (Aggregate.count_mul_perTerm_lt allocated.positive _))

/-- Replace only the hole endpoint corrections in the retained global physical term. The finite outer interface is
unchanged and remains explicit. -/
theorem physical_accurate (allocated :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.HoleCenteringRequest lifted fixed i j error)
    (samples : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j)
      (later : allocated.endpoints.index ≤ stage)
    (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    (neighbors : PuncturedFaces.NeighborBank base.faces)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq ((FacePerimeters.physicalPerimeter perimeters neighbors -
      CrossingTriangleAreas.physicalTriangleArea neighbors left right) -
      (PhysicalComponentCorrection.physicalComponentCorrection perimeters neighbors left right .exterior +
        allocated.centeredTotal samples)) < error := by
  rw [HoleComponentCorrection.physicalCorrection_eq_holes perimeters neighbors left right]
  have cancel (a b c : Data.Gaussian.Basic.Canonical) : (a + b) - (a + c) = b - c := by ring1
  rw [cancel]
  exact allocated.total_accurate samples later perimeters left right

/-- Retain the sampled traces and their centered total, together with the certificate for these exact global physical
readings. -/
@[expose] def readAt (allocated : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.HoleCenteringRequest
  lifted fixed i j error)
    (later : allocated.endpoints.index ≤ stage)
    (perimeters : Matched.FacePerimeters (request := request) cache.normalize i j)
    (neighbors : PuncturedFaces.NeighborBank base.faces)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh) :
    (samples : Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j) ×
    { value : Data.Gaussian.Basic.Canonical // value = allocated.centeredTotal samples ∧
      Data.Gaussian.Norm.Basic.normSq ((FacePerimeters.physicalPerimeter perimeters neighbors -
        CrossingTriangleAreas.physicalTriangleArea neighbors left right) -
        (PhysicalComponentCorrection.physicalComponentCorrection perimeters neighbors left right .exterior + value)) <
          error } :=
  let samples := Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters.build request cache
    i j
  ⟨samples, allocated.centeredTotal samples, rfl, allocated.physical_accurate samples later perimeters neighbors left
    right⟩

end HoleCenteringRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
