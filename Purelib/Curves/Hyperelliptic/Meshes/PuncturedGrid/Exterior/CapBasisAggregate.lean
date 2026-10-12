module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCaps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBoundary
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Polynomial

open Purelib.Riemann

public section

/-! Homogeneous energy and exact radial cancellation on the complete regular cap. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate

open Purelib.Topology.Polygon.Stokes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment (vertex apex)
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

open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

set_option genInjectivity false in
/-- One original cap triangle with its actual reciprocal refinement and retained regular basis sample. -/
structure RegularBasisFace (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  (parameters : Path.Dyadic.RadialTriangles.Parameters depth)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      where
  /-- The original coarse cap triangle. -/ coarse : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count +
    attached.words.length)
  /-- The triangle belongs to the original attached cap. -/ member : coarse ∈ attached.caps
  /-- The actual reciprocal refinement of that same triangle. -/ refinement :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse parameters
  /-- The retained regular basis sample on that refinement. -/ sample :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisSample refinement polynomials

constructive_injectivity RegularBasisFace

namespace RegularBasisFace

/-- Refine and sample every supplied original cap triangle in order with shared basis polynomials and parameters. -/
@[expose] def buildMany (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  (parameters : Path.Dyadic.RadialTriangles.Parameters depth)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (regularChart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (radius : Fraction.Rational) (positive : 0 < radius) :
    (coarses : List (Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length))) →
    (∀ coarse ∈ coarses, coarse ∈ attached.caps) → List
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisFace geometry parameters polynomials)
  | [], _ => []
  | coarse :: coarses, within =>
      let refinement := Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement.build geometry coarse
        (within coarse List.mem_cons_self) parameters
      ⟨coarse, within coarse List.mem_cons_self, refinement,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisSample.build refinement polynomials
        regularChart radius positive⟩ ::
        buildMany geometry
          parameters polynomials regularChart radius positive coarses
          (fun other member => within other (List.mem_cons_of_mem coarse member))

/-- The retained sampled faces have exactly the supplied original coarse triangle list. -/
theorem buildMany_coarses (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  (parameters : Path.Dyadic.RadialTriangles.Parameters depth)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (regularChart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (radius : Fraction.Rational) (positive : 0 < radius) :
    (coarses : List (Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length))) →
    (within : ∀ coarse ∈ coarses, coarse ∈ attached.caps) →
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisFace.buildMany geometry parameters
      polynomials regularChart radius positive coarses within).map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisFace.coarse = coarses
  | [], _ => rfl
  | coarse :: coarses, within => congrArg (List.cons coarse)
      (buildMany_coarses
        geometry parameters polynomials regularChart radius positive coarses
        (fun other member => within other (List.mem_cons_of_mem coarse member)))

end RegularBasisFace

set_option genInjectivity false in
/-- Every original cap triangle appears once, sharing the same basis and
refinement parameters. Its full homogeneous budget is cached. -/
structure RegularBasisCap (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  (parameters : Path.Dyadic.RadialTriangles.Parameters depth)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      where
  /-- The actual sampled faces in original cap order. -/ entries : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisFace geometry parameters polynomials)
  /-- Every original attached cap triangle occurs in exactly that order. -/ coarses_eq : entries.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisFace.coarse = attached.caps
  /-- The cached sum of retained local surface budgets. -/ budget : Fraction.Rational
  /-- The cached whole-cap budget equals the finite sum of the actual local budgets. -/ budget_eq : budget =
    FiniteSum.Rational.Squares.coordinateSum (entries.map (fun entry => entry.sample.budget.total))

constructive_injectivity RegularBasisCap

namespace RegularBasisCap

variable {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index
  box}

/-- Refine every original cap triangle once and cache its retained basis sample and total homogeneous budget. -/
@[expose] def build (geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached)
  (parameters : Path.Dyadic.RadialTriangles.Parameters depth)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (regularChart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (radius : Fraction.Rational) (positive : 0 < radius) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisCap geometry parameters polynomials :=
  let entries := Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisFace.buildMany geometry
    parameters polynomials regularChart radius positive attached.caps (fun _ member => member)
  ⟨entries, Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisFace.buildMany_coarses geometry
    parameters polynomials regularChart radius positive attached.caps
    (fun _ member => member), FiniteSum.Rational.Squares.coordinateSum (entries.map (fun entry =>
      entry.sample.budget.total)), rfl⟩

set_option genInjectivity false in
/-- The cached actual whole-cap boundary area for the supplied coefficient vector. -/
structure Evaluation (prepared : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisCap geometry
  parameters polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) where
  /-- The cached complete original cap boundary area. -/ area : Gaussian.Basic.Canonical
  /-- The cached area is exactly the sum of retained local sampled boundary areas. -/ area_eq : area =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.entries.map (fun entry => (entry.sample.budget.sample
    coefficients).boundaryArea))

constructive_injectivity Evaluation

/-- Cache the finite sum of actual sampled cap boundary areas for the retained coefficient vector. -/
@[expose] def evaluate (prepared : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisCap
  geometry parameters polynomials) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    prepared.Evaluation coefficients :=
  ⟨gaussianSum (prepared.entries.map (fun entry => (entry.sample.budget.sample coefficients).boundaryArea)), rfl⟩

namespace Evaluation

variable {prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisCap
  geometry parameters polynomials} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- The cached whole-cap energy is bounded below by minus its retained budget times the coefficient norm. -/
theorem lower (evaluated : prepared.Evaluation coefficients) :
    -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * prepared.budget) ≤ evaluated.area.im / 4
      := by
  rw [evaluated.area_eq, prepared.budget_eq]
  have aggregate (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisFace
    geometry parameters polynomials)) :
      -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * FiniteSum.Rational.Squares.coordinateSum
        (entries.map (fun entry => entry.sample.budget.total))) ≤
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => (entry.sample.budget.sample
          coefficients).boundaryArea))).im / 4 := by
    induction entries with
    | nil => change -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * 0) ≤ 0 / 4
             rw [mul_zero, neg_zero]
             decide
    | cons head tail ih =>
        have bound := Fraction.Order.Arithmetic.add_le_add_direct (head.sample.lower coefficients) ih
        simp only [List.map_cons, FiniteSum.Rational.Squares.coordinateSum, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
          Gaussian.Basic.add_im]
        exact (show -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * (head.sample.budget.total
          + FiniteSum.Rational.Squares.coordinateSum (tail.map (fun entry => entry.sample.budget.total)))) =
          -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * head.sample.budget.total) +
            -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients *
              FiniteSum.Rational.Squares.coordinateSum (tail.map (fun entry => entry.sample.budget.total))) by
              ring1).trans_le
          (bound.trans_eq (by simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1))
  exact aggregate prepared.entries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment in
/-- All radial contributions cancel along the actual closed cap words.
The only surviving paths are the inverse source arcs with cap orientation. -/
theorem area_eq_arcs (evaluated : prepared.Evaluation coefficients) :
    evaluated.area = Geometry.Grid.CellBoundary.sumValues (fun word => Geometry.Grid.CellBoundary.sumValues (fun edge =>
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea (polynomials.value coefficients) depth
        (lifted.vertices.coordinate edge.finish) (lifted.vertices.coordinate edge.start)) word) attached.words := by
  let radial (vertex : Fin (lifted.vertices.count + attached.words.length)) :=
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.radialArea (polynomials.value coefficients) depth
      (geometry.sourceCoordinates vertex)
  let arc (first last : Fin (lifted.vertices.count + attached.words.length)) :=
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea (polynomials.value coefficients) depth
      (geometry.sourceCoordinates first) (geometry.sourceCoordinates last)
  let contribution (triangle : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length))
    :=
    radial triangle.second + arc triangle.second triangle.third - radial triangle.third
  have aggregate (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisFace
    geometry parameters polynomials)) :
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => (entry.sample.budget.sample
        coefficients).boundaryArea)) =
        Geometry.Grid.CellBoundary.sumValues contribution (entries.map
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate.RegularBasisFace.coarse) := by
    induction entries with
    | nil => rfl
    | cons head tail ih =>
        change (head.sample.budget.sample coefficients).boundaryArea + _ = contribution head.coarse + _
        rw [head.sample.boundary_eq_arc, ih]
  rw [evaluated.area_eq, aggregate, prepared.coarses_eq, attached.caps_eq]
  change Geometry.Grid.CellBoundary.sumValues contribution (Topology.Surface.Boundary.BoundaryCaps.fans vertex
    attached.words Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.apex) = _
  rw [Meshes.fans_radial_sum vertex radial arc attached.words
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.apex attached.words_closed]
  apply Geometry.Grid.CellBoundary.sumValues_congr
  intro word _
  apply Geometry.Grid.CellBoundary.sumValues_congr
  intro edge _
  dsimp only [arc]
  rw [geometry.source_vertex_eq, geometry.source_vertex_eq]

end Evaluation
end RegularBasisCap
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate
