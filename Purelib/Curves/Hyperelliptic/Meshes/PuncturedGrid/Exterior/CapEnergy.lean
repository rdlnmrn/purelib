module
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
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
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse

public section

/-!
# Actual polynomial energy on the regular reciprocal cap refinement

The shared cap polynomial is evaluated once at each retained fine vertex.
The existing affine-error constructor computes every face budget and caches
their sum with the exact Stokes boundary area. Nonnegative coordinate area
then bounds the possible energy loss by this computed budget. Requested
depth selection is supplied by `GridExteriorCapAccuracy`. The exact inverse-arc
boundary and cancellation of radial contributions are supplied by
`GridExteriorCapBoundary`; chart-reading comparison remains separate.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
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
  {depth : Nat} {parameters : Path.Dyadic.RadialTriangles.Parameters depth}
  {index : Nat} {box : Rational.Box}

set_option genInjectivity false in
/-- The intrinsic regular-chart equality is retained explicitly. In odd
degree the primitive is a polynomial in t, so evaluating it at w would not
be the cap primitive and is not offered by this constructor. -/
structure RegularPolynomialSample (refinement : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement
  geometry coarse parameters)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (radius :
      Fraction.Rational) where
  /-- The reciprocal chart has origin order zero. -/ regular_chart :
    Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0
  /-- The original affine error radius is positive. -/ radius_positive : 0 < radius
  /-- The cached primitive polynomial values on the retained fine vertices. -/ values : Data.Vector
    Gaussian.Basic.Canonical parameters.mesh.mesh.vertices.length
  /-- Each cached vertex value is the original primitive polynomial evaluation. -/ values_eq : ∀ vertex, values vertex =
    sample.primitive.value.eval (refinement.coordinates vertex)
  /-- The cached coefficient polynomial values at the first vertex of every retained fine face. -/ coefficients :
    Data.Vector Gaussian.Basic.Canonical (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
    parameters.mesh.partition.leaves).length
  /-- Each cached face coefficient is the actual coefficient evaluation at its retained first vertex. -/ coefficients_eq
    : ∀ face, coefficients face = sample.coefficient.eval (refinement.coordinates
    (parameters.mesh.mesh.triangulation.faces face).first)
  /-- The cached affine surface sample on the original refined triangulation. -/ surface :
    Topology.PreparedSurfaceCoercivity.AffineSurfaceSample parameters.mesh.mesh.vertices.length
    (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length
  /-- The surface sample is constructed from these exact coordinates, values, coefficients and positive radius. -/
    surface_eq : surface = Topology.PreparedSurfaceCoercivity.AffineSurfaceSample.ofVertices
    parameters.mesh.mesh.triangulation
    refinement.coordinates values coefficients radius radius_positive
  /-- The cached affine energy is nonnegative on the original oriented refinement. -/ affine_nonnegative : 0 ≤
    surface.affineEnergy
  /-- The cached boundary energy is bounded below by the negative finite error budget. -/ lower : -surface.errorBudget ≤
    surface.boundaryArea.im / 4

constructive_injectivity RegularPolynomialSample

namespace RegularPolynomialSample

/-- Evaluate the actual regular reciprocal polynomial and coefficient once on each retained fine vertex and face, then
cache their affine surface energy bound. -/
@[expose] def build (refinement : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse
  parameters)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (regularChart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (radius : Fraction.Rational) (radiusPositive : 0 < radius) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularPolynomialSample refinement sample radius := by
  let values := Data.Vector.Basic.vectorOfFn (fun vertex => sample.primitive.value.eval (refinement.coordinates vertex))
  let coefficients := Data.Vector.Basic.vectorOfFn (fun face => sample.coefficient.eval (refinement.coordinates
    (parameters.mesh.mesh.triangulation.faces face).first))
  let surface := Topology.PreparedSurfaceCoercivity.AffineSurfaceSample.ofVertices parameters.mesh.mesh.triangulation
    refinement.coordinates values coefficients radius radiusPositive
  have nonnegative : 0 ≤ surface.affineEnergy := by
    change 0 ≤ FiniteSum.Fin.sumFin (fun face => Energy.AffineTriangle.coordinateTriangleArea
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).second)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).third) *
        Data.Gaussian.Norm.Basic.normSq (coefficients face))
    have estimate := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 : Fraction.Rational)) _
      (fun face => Fraction.Order.Arithmetic.mul_nonneg_direct (refinement.nonnegative face)
        (Gaussian.Norm.Basic.normSq_nonneg (coefficients face)))
    exact (FiniteSum.Fin.sumFin_zero).symm.trans_le estimate
  have lower : -surface.errorBudget ≤ surface.boundaryArea.im / 4 := by
    have monotone := Fraction.Order.Arithmetic.sub_le_sub_direct nonnegative (le_rfl (a := surface.errorBudget))
    rw [zero_sub] at monotone
    exact monotone.trans surface.affineEnergy_sub_errorBudget_le_boundaryEnergy
  exact ⟨regularChart, radiusPositive, values, Data.Vector.Basic.vectorOfFn_apply _, coefficients,
    Data.Vector.Basic.vectorOfFn_apply _, surface, rfl, nonnegative, lower⟩

/-- The cached coefficient is the actual regular reciprocal differential,
with its inversion sign and reversed differential index. -/
theorem coefficient_readback {refinement : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry
  coarse parameters}
    {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {radius :
      Fraction.Rational}
    (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularPolynomialSample refinement sample radius)
      (face : Fin (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length) :
    evaluated.coefficients face = -(refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first) ^
      (Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.reversedDifferential differential).exponent *
        sample.inverse.value.eval (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first) := by
  rw [evaluated.coefficients_eq, sample.coefficient_eq, sample.pulledInverse_eq]
  simp only [Hyperelliptic.Charts.Reciprocal.Cap.Primitives.coefficient,
    Hyperelliptic.Charts.Reciprocal.Cap.Primitives.point, Hyperelliptic.Charts.Reciprocal.Cap.Primitives.degree,
    evaluated.regular_chart, Nat.zero_add, Nat.one_mul, Nat.cast_one, pow_one, -eq_self, -iff_self]
  ring1

end RegularPolynomialSample

set_option genInjectivity false in
/-- One original cap triangle together with its retained fine sample. -/
structure RegularFaceSample (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  (parameters : Path.Dyadic.RadialTriangles.Parameters depth)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (radius :
      Fraction.Rational) where
  /-- The original coarse triangle in the attached cap. -/ coarse : Topology.Polygon.Stokes.OrientedTriangle
    (lifted.vertices.count + attached.words.length)
  /-- The retained coarse triangle belongs to the original cap list. -/ coarse_mem : coarse ∈ attached.caps
  /-- The actual radial refinement of that retained coarse triangle. -/ refinement :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse parameters
  /-- The cached regular polynomial energy sample on that exact refinement. -/ evaluated :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularPolynomialSample refinement sample radius

constructive_injectivity RegularFaceSample

namespace RegularFaceSample

/-- Refine and sample every supplied original cap triangle in order, retaining its membership in the attached cap list.
-/
@[expose] def buildMany (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  (parameters : Path.Dyadic.RadialTriangles.Parameters depth)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (regularChart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (radius : Fraction.Rational) (radiusPositive : 0 < radius) :
    (coarses : List (Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length))) →
    (∀ coarse ∈ coarses, coarse ∈ attached.caps) → List
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample geometry parameters sample radius)
  | [], _ => []
  | coarse :: coarses, within =>
      let refined := Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement.build geometry coarse (within
        coarse List.mem_cons_self) parameters
      ⟨coarse, within coarse List.mem_cons_self, refined,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularPolynomialSample.build refined sample regularChart
        radius radiusPositive⟩ ::
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample.buildMany geometry
          parameters sample regularChart radius radiusPositive coarses
          (fun other member => within other (List.mem_cons_of_mem coarse member))

/-- Reading back coarse triangles from the constructed samples recovers the exact original ordered list. -/
theorem buildMany_coarses (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  (parameters : Path.Dyadic.RadialTriangles.Parameters depth)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (regularChart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (radius : Fraction.Rational) (radiusPositive : 0 < radius) :
    (coarses : List (Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length))) →
    (within : ∀ coarse ∈ coarses, coarse ∈ attached.caps) →
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample.buildMany geometry parameters sample
      regularChart radius radiusPositive coarses within).map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample.coarse = coarses
  | [], _ => rfl
  | coarse :: coarses, within => congrArg (List.cons coarse)
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample.buildMany_coarses geometry
        parameters sample regularChart radius radiusPositive coarses
        (fun other member => within other (List.mem_cons_of_mem coarse member)))

/-- The total cached boundary energy is bounded below by the negative sum of the retained face error budgets. -/
theorem sum_lower {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {radius :
  Fraction.Rational}
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample geometry parameters sample
      radius)) :
    -FiniteSum.Rational.Squares.coordinateSum (entries.map (fun entry => entry.evaluated.surface.errorBudget)) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.surface.boundaryArea))).im /
        4 := by
  induction entries with
  | nil => change (0 : Fraction.Rational) ≤ 0 / 4; decide
  | cons head tail ih =>
      have bound := Fraction.Order.Arithmetic.add_le_add_direct head.evaluated.lower ih
      simp only [List.map_cons, FiniteSum.Rational.Squares.coordinateSum, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
        Gaussian.Basic.add_im]
      exact (by ring1 : -(head.evaluated.surface.errorBudget + FiniteSum.Rational.Squares.coordinateSum (tail.map (fun
        entry => entry.evaluated.surface.errorBudget))) =
        -head.evaluated.surface.errorBudget + -FiniteSum.Rational.Squares.coordinateSum (tail.map (fun entry =>
          entry.evaluated.surface.errorBudget))).trans_le
          (bound.trans_eq (by simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1))

end RegularFaceSample

set_option genInjectivity false in
/-- The complete regular cap, with all coarse fan triangles and every fine
face count paid in the cached sum. The error is an established finite bound,
not a claim that a requested tolerance has already been reached. -/
structure RegularEnergy (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  (parameters : Path.Dyadic.RadialTriangles.Parameters depth)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (radius :
      Fraction.Rational) where
  /-- The reciprocal chart has origin order zero. -/ regular_chart :
    Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0
  /-- The original affine error radius is positive. -/ radius_positive : 0 < radius
  /-- The actual retained regular samples of all original coarse cap triangles. -/ entries : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample geometry parameters sample radius)
  /-- The retained coarse triangles equal the original attached cap list in order. -/ coarses_eq : entries.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample.coarse = attached.caps
  /-- The cached total number of fine faces. -/ count : Nat
  /-- The count is the original sample count times the shared refinement face count. -/ count_eq : count =
    entries.length * (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles parameters.mesh.partition.leaves).length
  /-- The cached total oriented cap boundary area. -/ area : Gaussian.Basic.Canonical
  /-- The total area is the sum of the retained sample boundary areas. -/ area_eq : area =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.surface.boundaryArea))
  /-- The cached sum of all retained finite error budgets. -/ error : Fraction.Rational
  /-- The total error is exactly the sum of the retained face error budgets. -/ error_eq : error =
    FiniteSum.Rational.Squares.coordinateSum (entries.map (fun entry => entry.evaluated.surface.errorBudget))
  /-- The total boundary energy is bounded below by the negative cached error. -/ lower : -error ≤ area.im / 4

constructive_injectivity RegularEnergy

namespace RegularEnergy

/-- Combine the retained face samples into the exact total cap area, face count and summed error bound. -/
@[expose] def ofEntries (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  (parameters : Path.Dyadic.RadialTriangles.Parameters depth)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (regularChart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (radius : Fraction.Rational) (radiusPositive : 0 < radius)
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample geometry parameters sample
      radius))
    (coarses : entries.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample.coarse =
      attached.caps) : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy geometry parameters sample
      radius := by
  have lower := @Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample.sum_lower genus curve branches
    higher base lifted differential collar cap regular
    domains prepared attached geometry depth parameters index box sample radius entries
  refine ⟨regularChart, radiusPositive, entries, coarses,
    entries.length * (Rectangle.Partition.PreparedBoxTriangulation.boxTriangles
      parameters.mesh.partition.leaves).length, rfl,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.surface.boundaryArea)), rfl,
    FiniteSum.Rational.Squares.coordinateSum (entries.map (fun entry => entry.evaluated.surface.errorBudget)), rfl,
    ?_⟩
  exact lower

/-- Refine every original attached cap triangle and combine its actual cached regular polynomial energy sample. -/
@[expose] def build (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  (parameters : Path.Dyadic.RadialTriangles.Parameters depth)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (regularChart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (radius : Fraction.Rational) (radiusPositive : 0 < radius) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy geometry parameters sample radius :=
  let entries := Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample.buildMany geometry parameters
    sample regularChart radius radiusPositive attached.caps (fun _ member => member)
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy.ofEntries geometry parameters sample regularChart
    radius radiusPositive entries
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularFaceSample.buildMany_coarses geometry parameters
      sample regularChart radius radiusPositive attached.caps (fun _ member => member))

/-- Construct the regular cap energy sample from the curve's even-degree identity and the supplied positive affine
radius. -/
@[expose] def ofEvenDegree (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  (parameters : Path.Dyadic.RadialTriangles.Parameters depth)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (radius : Fraction.Rational) (radiusPositive : 0 < radius) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy geometry parameters sample radius := by
  have balance := Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.degree_balance curve
  rw [degree] at balance
  have chart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0 := by
    have transported := congrArg (fun value : Nat => value - (2 * genus + 2)) (balance :
      (2 * genus + 2) + Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = (2 * genus + 2) + 0)
    rewrite [Data.Nat.Subtraction.add_sub_cancel_left] at transported
    exact transported.trans (Data.Nat.Subtraction.add_sub_cancel_left (2 * genus + 2) 0)
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy.build geometry parameters sample chart
    radius radiusPositive

/-- The cached fine-face count is the number of original cap triangles times two times four to the retained depth. -/
theorem count_refined {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {radius : Fraction.Rational}
    (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy geometry parameters sample radius)
      : evaluated.count = attached.caps.length * (2 * 4 ^ depth) := by
  have length := congrArg List.length evaluated.coarses_eq
  rw [Data.List.Map.length_map] at length
  rw [evaluated.count_eq, length, parameters.mesh.faceCount_eq]

end RegularEnergy
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy
