module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.NatCast
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
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
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement
public import Purelib.Riemann.Periods.ReciprocalCapBilinearBounds
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
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-! The actual reciprocal fan refinement supplies both polynomial readings.
Finite Stokes pays its boundary by a vanishing two-differential face bound. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear

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
  {geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached} {coarse : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length)}
  {depth index otherIndex : Nat} {box otherBox : Rational.Box}
  {parameters : Path.Dyadic.RadialTriangles.Parameters depth}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other otherIndex otherBox}

/-- The rational sum of a constant over Fin count equals count times that constant. -/
private theorem sum_constant (count : Nat) (value : Fraction.Rational) : Purelib.Algebra.FiniteSum.Fin.sumFin (fun _ :
  Fin count => value) = (count : Fraction.Rational) * value := open Purelib.Algebra in by
  induction count with
  | zero => change 0 = 0 * value; ring1
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ, ih, Nat.cast_succ]; ring1

/-- The actual paired polynomial boundary area of the retained cap refinement satisfies its geometric quarter-radius
bound. -/
theorem Refinement.paired_boundary_bound (refinement :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse parameters)
    (member : coarse ∈ attached.caps) (left : Charts.Reciprocal.Cap.EnergyBounds sample)
      (right : Charts.Reciprocal.Cap.EnergyBounds otherSample) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.edgeListArea (fun vertex =>
      Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample (refinement.coordinates vertex))
      parameters.mesh.mesh.triangulation.boundary) ≤
        Rational.Geometric.Basic.quarterRadius (128^2 * 64 * Periods.ReciprocalCapBilinearBounds.bilinearScale left
          right) depth := by
  have nonnegative : (0 : Fraction.Rational) ≤ 64 := by decide +kernel
  have localBound (face : Fin (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
    parameters.mesh.partition.leaves).length) :
      Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.triangleWedgeArea
        (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample (refinement.coordinates
          (parameters.mesh.mesh.triangulation.faces face).first))
        (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample (refinement.coordinates
          (parameters.mesh.mesh.triangulation.faces face).second))
        (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample (refinement.coordinates
          (parameters.mesh.mesh.triangulation.faces face).third))) ≤
      Periods.ReciprocalCapBilinearBounds.bilinearScale left right * (Rational.Geometric.Basic.quarterRadius 64 depth)^3
        := by
    have inside := refinement.inside face
    have distance := refinement.distances member face
    exact Periods.ReciprocalCapBilinearBounds.bilinear_triangle_bound left right
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox_contains inside.1)
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox_contains inside.2.1)
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox_contains inside.2.2)
      (Rational.Geometric.Basic.quarterRadius_nonneg nonnegative depth)
      (Rational.Geometric.Basic.quarterRadius_le_scale nonnegative depth) distance.1 distance.2
  rw [← parameters.mesh.mesh.triangulation.wedgeSum_eq_boundaryArea]
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin _ _ localBound
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.sum_constant] at estimate
  have count : (((Rectangle.Partition.PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length :
    Nat) : Fraction.Rational) *
      Rational.Geometric.Basic.quarterRadius 64 depth = 128 := by
    rw [parameters.mesh.faceCount_eq, Algebra.NatCast.mul, Algebra.NatCast.pow, Nat.cast_ofNat, Nat.cast_ofNat,
      Rational.Geometric.Basic.quarterRadius]
    have denominator : (4 : Fraction.Rational)^depth ≠ 0 := (Fraction.Order.Arithmetic.pow_pos_direct (by decide)
      depth).ne'
    calc
      _ = 2 * ((64 / (4 : Fraction.Rational)^depth) * (4 : Fraction.Rational)^depth) := by ring1
      _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ denominator]; decide +kernel
  apply estimate.trans_eq
  calc
    _ = ((((Rectangle.Partition.PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length : Nat) :
      Fraction.Rational) *
        Rational.Geometric.Basic.quarterRadius 64 depth)^2 * Periods.ReciprocalCapBilinearBounds.bilinearScale left
          right * Rational.Geometric.Basic.quarterRadius 64 depth := by ring1
    _ = 128^2 * Periods.ReciprocalCapBilinearBounds.bilinearScale left right * Rational.Geometric.Basic.quarterRadius 64
      depth := by
      rw [count]
    _ = _ := by
      simp only [Rational.Geometric.Basic.quarterRadius, Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self];
      ring1

set_option genInjectivity false in
/-- Cache the actual paired vertex readings and the oriented boundary area
of this retained refinement, with its proved finite error bound. -/
structure PairedPolynomialSample (refinement : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement
  geometry coarse parameters)
    (left : Charts.Reciprocal.Cap.EnergyBounds sample) (right :
      Charts.Reciprocal.Cap.EnergyBounds otherSample) where
  /-- The cached paired polynomial readings at every retained fine vertex. -/ values : Data.Vector
    Topology.Polygon.Stokes.PrimitivePoint parameters.mesh.mesh.vertices.length
  /-- Each cached value is the paired reading at the original refined coordinate. -/ values_eq : ∀ vertex, values vertex
    = Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample (refinement.coordinates vertex)
  /-- The cached oriented area of the original fine boundary. -/ area : Gaussian.Basic.Canonical
  /-- The cached area equals the boundary edge-list area of the retained values. -/ area_eq : area =
    Topology.Polygon.Stokes.edgeListArea values parameters.mesh.mesh.triangulation.boundary
  /-- The computed finite squared-norm error bound. -/ error : Fraction.Rational
  /-- The error is the original geometric quarter-radius expression at the retained depth. -/ error_eq : error =
    Rational.Geometric.Basic.quarterRadius (128^2 * 64 * Periods.ReciprocalCapBilinearBounds.bilinearScale left right)
    depth
  /-- The squared norm of the cached boundary area fits the computed error. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq area ≤ error

constructive_injectivity PairedPolynomialSample

namespace PairedPolynomialSample

/-- Pointwise equal retained vertex readings give equal area on the same ordered boundary edge list. -/
public theorem boundary_congr {count : Nat} {left right : Fin count → Topology.Polygon.Stokes.PrimitivePoint}
    (equal : ∀ vertex, left vertex = right vertex) (edges : List (Topology.Polygon.Stokes.OrientedEdge count)) :
    Topology.Polygon.Stokes.edgeListArea left edges = Topology.Polygon.Stokes.edgeListArea right edges := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      change Topology.Polygon.Stokes.edgeArea (left edge.start) (left edge.finish) + _ =
        Topology.Polygon.Stokes.edgeArea (right edge.start) (right edge.finish) + _
      rw [equal, equal, ih]

/-- Cache both actual polynomial readings on the retained fine vertices and their exact oriented boundary area with its
proved error bound. -/
def build (refinement : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse parameters)
  (member : coarse ∈ attached.caps)
    (left : Charts.Reciprocal.Cap.EnergyBounds sample) (right :
      Charts.Reciprocal.Cap.EnergyBounds otherSample) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.PairedPolynomialSample refinement left right := by
  let values := Data.Vector.Basic.vectorOfFn (fun vertex => Periods.ReciprocalCapBilinearBounds.pairedValue sample
    otherSample (refinement.coordinates vertex))
  have valuesEq (vertex) : values vertex = Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample
    (refinement.coordinates vertex) := Data.Vector.Basic.vectorOfFn_apply _ vertex
  let area := Topology.Polygon.Stokes.edgeListArea values parameters.mesh.mesh.triangulation.boundary
  refine ⟨values, valuesEq, area, rfl, Rational.Geometric.Basic.quarterRadius (128^2 * 64 *
    Periods.ReciprocalCapBilinearBounds.bilinearScale left right) depth, rfl, ?_⟩
  have equal : area = Topology.Polygon.Stokes.edgeListArea (fun vertex =>
    Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample (refinement.coordinates vertex))
      parameters.mesh.mesh.triangulation.boundary := by
    exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.PairedPolynomialSample.boundary_congr valuesEq
      _
  rw [equal]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.Refinement.paired_boundary_bound refinement member left
    right

end PairedPolynomialSample

set_option genInjectivity false in
/-- A single sufficient depth and parameter mesh serve every retained fan
triangle for this pair of actual reciprocal polynomial samples. -/
structure PairedRequest (left : Charts.Reciprocal.Cap.EnergyBounds sample) (right :
  Charts.Reciprocal.Cap.EnergyBounds otherSample)
    (target : Fraction.Rational) (minimum : Nat) where
  /-- The original scale for the paired cap polynomial bound. -/ scale : Fraction.Rational
  /-- The scale is the prescribed factor times the two-sample bilinear scale. -/ scale_eq : scale = 128^2 * 64 *
    Periods.ReciprocalCapBilinearBounds.bilinearScale left right
  /-- The retained sufficient spatial refinement depth. -/ depth : Nat
  /-- The depth is the first permitted quarter-radius depth below the requested target. -/ depth_eq : depth =
    Rational.Geometric.Search.firstQuarterBelow scale minimum target
  /-- The retained depth meets the supplied minimum. -/ minimum_le : minimum ≤ depth
  /-- The shared radial mesh parameters at the retained depth. -/ parameters : Path.Dyadic.RadialTriangles.Parameters
    depth
  /-- The computed error at the retained depth. -/ error : Fraction.Rational
  /-- The computed error equals the scaled quarter radius. -/ error_eq : error = Rational.Geometric.Basic.quarterRadius
    scale depth
  /-- The computed error is strictly below the supplied target. -/ accurate : error < target

constructive_injectivity PairedRequest

namespace PairedRequest
variable {left : Charts.Reciprocal.Cap.EnergyBounds sample} {right :
  Charts.Reciprocal.Cap.EnergyBounds otherSample} {target : Fraction.Rational} {minimum :
  Nat}

/-- Choose a sufficient quarter-radius depth above the requested floor and retain the corresponding mesh parameters and
strict error bound. -/
def build (left : Charts.Reciprocal.Cap.EnergyBounds sample) (right :
  Charts.Reciprocal.Cap.EnergyBounds otherSample)
    (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.PairedRequest left right target minimum := by
  let scale := 128^2 * 64 * Periods.ReciprocalCapBilinearBounds.bilinearScale left right
  have sixtyFour : (0 : Fraction.Rational) ≤ 64 := by decide +kernel
  have nonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _) sixtyFour)
      (Periods.ReciprocalCapBilinearBounds.bilinearScale_nonnegative left right)
  let depth := Rational.Geometric.Search.firstQuarterBelow scale minimum target
  exact ⟨scale, rfl, depth, rfl, Rational.Geometric.Search.firstQuarterBelow_ge scale minimum target,
    Path.Dyadic.RadialTriangles.Parameters.build depth, Rational.Geometric.Basic.quarterRadius scale depth, rfl,
    Rational.Geometric.Search.firstQuarterBelow_accurate scale nonnegative minimum target positive⟩

set_option genInjectivity false in
/-- The actual original cap triangle refinement and cached paired polynomial sample meeting the supplied request. -/
structure Evaluation (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.PairedRequest left right target
  minimum)
    (geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
      attached) (coarse : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length))
      where
  /-- The actual inverse-arc refinement of the original coarse cap triangle. -/ refinement :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse request.parameters
  /-- The cached paired polynomial readings on that exact refinement. -/ sampled :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.PairedPolynomialSample refinement left right
  /-- The squared norm of the actual sampled boundary area is below the requested target. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq sampled.area < target

constructive_injectivity Evaluation

/-- Build the actual inverse-arc refinement, cache both polynomials on its
vertices, and certify its oriented boundary below the supplied request. -/
def evaluate (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.PairedRequest left right target minimum)
  (geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
  attached)
    (coarse : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length)) (member : coarse
      ∈ attached.caps) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.PairedRequest.Evaluation request geometry coarse := by
  let refinement := Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement.build geometry coarse member
    request.parameters
  let sampled := Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.PairedPolynomialSample.build refinement member
    left right
  refine ⟨refinement, sampled, sampled.bounded.trans_lt ?_⟩
  rw [sampled.error_eq, ← request.scale_eq, ← request.error_eq]
  exact request.accurate

end PairedRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear
