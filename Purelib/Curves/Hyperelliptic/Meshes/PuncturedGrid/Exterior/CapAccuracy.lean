module
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Integration.Path.Dyadic.RadialTriangles
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
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

public section

/-!
# Requested energy control on the complete regular reciprocal cap

The original shared polynomial determines a certified finite depth. Every
coarse cap triangle is evaluated on the retained refinement, and the sum of
its actual computed face errors is below the request. The retained
refinement follows the actual inverse source arcs. Exact identification
of the aggregate arc boundary is supplied by `GridExteriorCapBoundary`.
-/

section

open Purelib.Curves
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)

open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Topology.PreparedSurfaceCoercivity (computedAffineTriangleError)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    AllSurfacePreparation
    regular domains differential} {attached :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared}
  {geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached} {coarse : OrientedTriangle (lifted.vertices.count + attached.words.length)}
  {minimum : Nat} {index : Nat} {box : Rational.Box} {sample :
    Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularPolynomialSample

/-- The actual cached affine error budget on one original cap triangle fits the retained coefficient and epsilon bound.
-/
theorem error_le
  (bounds : Charts.Reciprocal.Cap.EnergyBounds sample) {count : Nat} {target :
  Fraction.Rational}
    (request : Charts.Reciprocal.Cap.EnergyRequest bounds count target minimum) {parameters
      : Path.Dyadic.RadialTriangles.Parameters request.depth}
    {refinement : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse parameters}
      (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularPolynomialSample refinement sample
      request.radius)
    (member : coarse ∈ attached.caps) :
    evaluated.surface.errorBudget ≤ 128 * (2 * bounds.coefficient + 4) * request.epsilon := open Purelib.Algebra in by
  let errors (face : Fin (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
    parameters.mesh.partition.leaves).length) :=
    computedAffineTriangleError (evaluated.coefficients face)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).second)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).third)
      (evaluated.values (parameters.mesh.mesh.triangulation.faces face).first)
      (evaluated.values (parameters.mesh.mesh.triangulation.faces face).second)
      (evaluated.values (parameters.mesh.mesh.triangulation.faces face).third) request.radius evaluated.radius_positive
  have localBound (face : Fin (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
    parameters.mesh.partition.leaves).length) :
      (errors face).totalBudget ≤ (2 * bounds.coefficient + 4) * request.radius := by
    have inside := refinement.inside face
    have distance := refinement.distances member face
    rw [← request.diameter_eq] at distance
    dsimp only [errors]
    rw [evaluated.coefficients_eq, evaluated.values_eq, evaluated.values_eq, evaluated.values_eq]
    exact bounds.triangle_budget_le _ _ _ (Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox_contains
      inside.1)
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox_contains inside.2.1)
      (Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox_contains inside.2.2) request.epsilon
        request.diameter request.radius
      request.epsilon_positive request.epsilon_le_one request.diameter_positive evaluated.radius_positive
        request.radius_eq
      distance.1 distance.2 request.taylor
  have aggregate := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun face => (errors face).totalBudget)
    (fun _ => (2 * bounds.coefficient + 4) * request.radius) localBound
  rw [FiniteSum.Fin.Rational.sum_constant] at aggregate
  rw [evaluated.surface_eq]
  change FiniteSum.Fin.sumFin (fun face => (errors face).totalBudget) ≤ _
  apply aggregate.trans_eq
  rw [parameters.mesh.faceCount_eq, request.radius_eq]
  calc
    _ = (((2 * 4 ^ request.depth : Nat) : Fraction.Rational) * request.diameter) *
        ((2 * bounds.coefficient + 4) * request.epsilon) := by ring1
    _ = _ := by rw [request.face_count_cancel]; ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularPolynomialSample

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapAccuracy

open Purelib.Algebra.FiniteSum.Rational in
/-- The sum of the actual retained cap-face errors fits the original face-count bound. -/
private theorem entries_error_le (bounds : Charts.Reciprocal.Cap.EnergyBounds sample) {count
  : Nat} {target : Fraction.Rational}
    (request : Charts.Reciprocal.Cap.EnergyRequest bounds count target minimum) {parameters
      : Path.Dyadic.RadialTriangles.Parameters request.depth}
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample geometry parameters sample
      request.radius)) :
    Purelib.Algebra.FiniteSum.Rational.Squares.coordinateSum (entries.map (fun entry =>
      entry.evaluated.surface.errorBudget)) ≤
      (entries.length : Fraction.Rational) * (128 * (2 * bounds.coefficient + 4) * request.epsilon) := by
  induction entries with
  | nil => change 0 ≤ 0 * _; rw [Fraction.Field.zero_mul_direct]
  | cons head tail ih =>
      have bound := Fraction.Order.Arithmetic.add_le_add_direct (head.evaluated.error_le bounds request head.coarse_mem)
        ih
      simp only [List.map_cons, Squares.coordinateSum, List.length_cons, Nat.cast_succ]
      exact bound.trans_eq (by ring1)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapAccuracy

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy

/-- The complete cached cap error fits the original finite request's paid total. -/
theorem error_le (bounds :
  Charts.Reciprocal.Cap.EnergyBounds sample) {target : Fraction.Rational}
    (request : Charts.Reciprocal.Cap.EnergyRequest bounds attached.caps.length target
      minimum) {parameters : Path.Dyadic.RadialTriangles.Parameters request.depth}
    (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy geometry parameters sample
      request.radius) : evaluated.error ≤ request.total := by
  have estimate := Exterior.CapAccuracy.entries_error_le bounds request evaluated.entries
  have length := congrArg List.length evaluated.coarses_eq
  rw [Data.List.Map.length_map] at length
  rw [length] at estimate
  rw [evaluated.error_eq]
  apply estimate.trans_eq
  rw [request.total_eq, request.scale_eq]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapAccuracy

set_option genInjectivity false in
/-- A successful finite cap request retains the bounds, both selected
depths, the actual mesh and sampled energies, and the proved requested total. -/
structure RequestedRegularEnergy (geometry
  : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (target :
      Fraction.Rational) (minimum : Nat) where
  /-- The original reciprocal polynomial's retained finite energy bounds. -/ bounds :
    Charts.Reciprocal.Cap.EnergyBounds sample
  /-- The actual energy request paying every original attached cap triangle. -/ request :
    Charts.Reciprocal.Cap.EnergyRequest bounds attached.caps.length target minimum
  /-- The retained radial mesh at the request's selected depth. -/ parameters : Path.Dyadic.RadialTriangles.Parameters
    request.depth
  /-- The complete cached cap energy sample on that exact retained mesh. -/ evaluated :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy geometry parameters sample request.radius
  /-- The actual computed error fits the request's retained paid total. -/ error_le : evaluated.error ≤ request.total
  /-- The actual computed error is strictly below the supplied target. -/ error_lt : evaluated.error < target
  /-- The actual total boundary energy exceeds the negative requested target. -/ lower : -target < evaluated.area.im / 4

constructive_injectivity RequestedRegularEnergy

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapAccuracy

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapAccuracy.RequestedRegularEnergy

/-- Choose the original sufficient cap depth, sample every actual even-degree cap triangle and retain the proved strict
requested energy bound. -/
@[expose] def build
  (geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
  attached) (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (bounds : Charts.Reciprocal.Cap.EnergyBounds sample) (degree : curve.polynomial.natDegree
      = 2 * genus + 2)
    (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
    CapAccuracy.RequestedRegularEnergy geometry sample target minimum := by
  let request := Charts.Reciprocal.Cap.EnergyRequest.build bounds attached.caps.length
    target positive minimum
  let parameters := Path.Dyadic.RadialTriangles.Parameters.build request.depth
  let evaluated := Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy.ofEvenDegree geometry parameters
    sample degree request.radius request.radius_positive
  have bounded := evaluated.error_le bounds request
  have accurate : evaluated.error < target := bounded.trans_lt request.accurate
  refine ⟨bounds, request, parameters, evaluated, bounded, accurate, ?_⟩
  exact (Fraction.Order.Arithmetic.neg_lt_neg_direct accurate).trans_le evaluated.lower

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapAccuracy.RequestedRegularEnergy

end
end
