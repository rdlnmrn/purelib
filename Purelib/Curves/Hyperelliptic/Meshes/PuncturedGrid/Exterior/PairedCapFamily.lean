module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann

open Purelib

@[expose] public section

/-! One request for the entire retained reciprocal cap family. Every cap
uses the shared parameter mesh and retains its actual paired boundary area. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily

open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {attached :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared}
  {index otherIndex : Nat} {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other otherIndex otherBox}

set_option genInjectivity false in
/-- One positive allowance and shared refinement request for every original attached reciprocal cap triangle.

The finite count-squared charge is paid before evaluating the retained paired polynomial samples. -/
structure PairedFamilyRequest (attached :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
    (left : Charts.Reciprocal.Cap.EnergyBounds sample) (right :
      Charts.Reciprocal.Cap.EnergyBounds otherSample) (target : Fraction.Rational) (minimum :
      Nat) where
  /-- The retained count of original attached cap triangles. -/ count : Nat
  /-- The count is the length of the original attached cap list. -/ count_eq : count = attached.caps.length
  /-- The positive local error allowance shared by all original cap triangles. -/ allowance : Fraction.Rational
  /-- The allowance is the target divided by count squared plus one. -/ allowance_eq : allowance = target / ((count :
    Fraction.Rational)^2 + 1)
  /-- The retained local allowance is positive. -/ positive : 0 < allowance
  /-- The original count-squared aggregate charge is strictly below the target. -/ paid : (count : Fraction.Rational)^2
    * allowance < target
  /-- The shared paired polynomial refinement request at the retained local allowance. -/ localRequest :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.PairedRequest left right allowance minimum

constructive_injectivity PairedFamilyRequest

namespace PairedFamilyRequest
variable {left : Charts.Reciprocal.Cap.EnergyBounds sample} {right :
  Charts.Reciprocal.Cap.EnergyBounds otherSample} {target : Fraction.Rational} {minimum :
  Nat}

/-- Allocate the positive target over the actual original cap count and retain one sufficient paired refinement request.
-/
def build (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared)
  (left : Charts.Reciprocal.Cap.EnergyBounds sample) (right :
  Charts.Reciprocal.Cap.EnergyBounds otherSample)
    (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest attached left right target minimum
      := by
  let count := attached.caps.length
  let allowance := target / ((count : Fraction.Rational)^2 + 1)
  have denominator : 0 < (count : Fraction.Rational)^2 + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by decide)
  have allowancePositive : 0 < allowance := Fraction.Order.Field.div_pos_direct positive denominator
  have paid : (count : Fraction.Rational)^2 * allowance < target := by
    have increase := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (show (count : Fraction.Rational)^2 < (count : Fraction.Rational)^2 + 1 from by
        have translated := Fraction.Order.Arithmetic.add_lt_add_right_direct
          (by decide : (0 : Fraction.Rational) < 1) ((count : Fraction.Rational)^2)
        exact (Fraction.zero_add _).symm.trans_lt
          (translated.trans_eq (Fraction.add_comm _ _))) allowancePositive
    exact increase.trans_eq ((Fraction.Field.mul_comm _ _).trans (Fraction.Field.div_mul_cancel_of_ne _ _
      denominator.ne'))
  exact ⟨count, rfl, allowance, rfl, allowancePositive, paid,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.PairedRequest.build left right allowance allowancePositive
      minimum⟩

set_option genInjectivity false in
/-- One original attached cap triangle and its actual paired polynomial sample on the shared requested refinement. -/
structure Entry (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest attached left
  right target minimum) (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  where
  /-- The original coarse cap triangle. -/ coarse : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count +
    attached.words.length)
  /-- The retained triangle belongs to the original attached cap list. -/ member : coarse ∈ attached.caps
  /-- The actual paired polynomial sample on this triangle and shared request. -/ evaluated :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.PairedRequest.Evaluation request.localRequest geometry
    coarse

constructive_injectivity Entry

/-- Evaluate the supplied original cap triangles in order on the same retained request. -/
def buildEntries (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest attached
  left right target minimum) (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached) :
    (coarses : List (Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length))) →
    (∀ coarse ∈ coarses, coarse ∈ attached.caps) → List
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Entry request geometry)
  | [], _ => []
  | coarse :: rest, within =>
      ⟨coarse, within coarse (List.Mem.head _),
        request.localRequest.evaluate geometry coarse (within coarse (List.Mem.head _))⟩ ::
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.buildEntries
        request geometry rest (fun other member => within other (List.Mem.tail coarse member))

/-- The sampled entries retain exactly the supplied original ordered coarse triangles. -/
theorem buildEntries_coarses (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest
  attached left right target minimum) (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached) :
    (coarses : List (Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length))) →
    (within : ∀ coarse ∈ coarses, coarse ∈ attached.caps) →
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.buildEntries request geometry
      coarses within).map Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Entry.coarse =
      coarses
  | [], _ => rfl
  | coarse :: rest, within => congrArg (List.cons coarse)

        (buildEntries_coarses
        request geometry rest (fun other member => within other (List.Mem.tail coarse member)))

set_option genInjectivity false in
/-- The aggregate caches all samples and the sum of their complete oriented
boundaries. The ownership equation covers every cap, in its original order. -/
structure Evaluation (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest attached
  left right target minimum) (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  where
  /-- The actual retained samples of all original attached cap triangles. -/ entries : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Entry request geometry)
  /-- The samples retain exactly the original cap list in order. -/ coarses_eq : entries.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Entry.coarse = attached.caps
  /-- The cached sum of actual paired boundary areas. -/ area : Gaussian.Basic.Canonical
  /-- The cached area equals the sum of the retained sample areas. -/ area_eq : area =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.sampled.area))
  /-- The squared norm of the actual total area is strictly below the requested target. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq area < target

constructive_injectivity Evaluation

/-- Cache the total actual paired boundary area from the retained entries and certify its original count-squared error
bound. -/
public def ofEntries (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest
  attached left right target minimum) (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Entry request
      geometry)) (coarses : entries.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Entry.coarse = attached.caps) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation request geometry := by
  let area := Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.sampled.area))
  have bound := Gaussian.Norm.Sum.Bounds.normSq_sum_le (entries.map (fun entry => entry.evaluated.sampled.area))
    request.allowance (by
      intro value member
      obtain ⟨entry, _, rfl⟩ := Data.List.Map.mem_map.mp member
      exact entry.evaluated.accurate.le)
  have length : entries.length = request.count := by
    have equal := congrArg List.length coarses
    rw [Data.List.Map.length_map] at equal
    exact equal.trans request.count_eq.symm
  rw [Data.List.Map.length_map, length] at bound
  exact ⟨entries, coarses, area, rfl, bound.trans_lt
    ((by ring1 : (request.count : Fraction.Rational) * ((request.count : Fraction.Rational) * request.allowance) =
      (request.count : Fraction.Rational)^2 * request.allowance).trans_lt request.paid)⟩

/-- Evaluate every original attached cap triangle once and combine their actual paired boundary areas. -/
def evaluate (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest attached left
  right target minimum) (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation request geometry :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.ofEntries request geometry
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.buildEntries request geometry
    attached.caps (fun _ member => member))
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.buildEntries_coarses request
      geometry attached.caps (fun _ member => member))

end PairedFamilyRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation
