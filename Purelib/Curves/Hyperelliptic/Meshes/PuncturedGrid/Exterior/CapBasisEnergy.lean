module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy
public import Purelib.Riemann.Readings.AffineBasisEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Mesh.CoordinateTriangulation

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-! Homogeneous energy on the actual regular reciprocal cap refinement. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

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

/-- All basis polynomials use the same reciprocal sample stage and box. -/
def RegularBasisPolynomials (cap : Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar) (index :
  Nat) (box : Rational.Box) :=
  Data.Vector.DependentVector (fun row : Fin genus => Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    (Periods.PeriodMatrix.standardDifferential row) index box)

namespace RegularBasisPolynomials

/-- The homogeneous combination of the original retained basis primitive polynomials at the supplied coordinate. -/
def value (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index
  box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (point : Gaussian.Basic.Canonical) :
      Gaussian :=
  FiniteSum.Fin.sumFin fun row => coefficients row * (polynomials.get row).primitive.value.eval point

end RegularBasisPolynomials

/-- An affine basis on the exact retained radial cap triangulation and coordinates. -/
def RegularCapBasis (refinement : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse
  parameters) :=
  Readings.AffineBasisEnergy.AffineBasis parameters.mesh.mesh.triangulation refinement.coordinates genus

set_option genInjectivity false in
/-- Retain the actual basis values, derivatives and coefficient-independent
error budget on one original reciprocal cap triangle. -/
structure RegularBasisSample (refinement : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry
  coarse parameters)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      where
  /-- The reciprocal chart has origin order zero. -/ regular_chart :
    Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0
  /-- The actual cached affine basis on the retained cap refinement. -/ basis :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularCapBasis refinement
  /-- Every cached basis value is the original primitive polynomial evaluation. -/ values_eq : ∀ row vertex,
    basis.values row vertex = (polynomials.get row).primitive.value.eval (refinement.coordinates vertex)
  /-- Every cached basis coefficient is the original coefficient evaluation at the retained face's first vertex. -/
    coefficients_eq : ∀ row face, basis.coefficients row face = (polynomials.get row).coefficient.eval
    (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first)
  /-- The actual coefficient-independent affine surface budget on that cached basis. -/ budget :
    Readings.AffineBasisEnergy.AffineBasis.SurfaceBudget basis

constructive_injectivity RegularBasisSample

namespace RegularBasisSample

variable {refinement : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse parameters}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
  index box}

/-- Cache every original basis polynomial and coefficient on the same fine vertices and faces, then retain their
coefficient-independent surface budget. -/
def build (refinement : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse parameters)
  (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
    (regularChart : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0)
    (radius : Fraction.Rational) (positive : 0 < radius) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisSample refinement polynomials := by
  let values := Data.Vector.Basic.vectorOfFn (fun row : Fin genus => Data.Vector.Basic.vectorOfFn (fun vertex =>
    (polynomials.get row).primitive.value.eval (refinement.coordinates vertex)))
  let coefficients := Data.Vector.Basic.vectorOfFn (fun row : Fin genus => Data.Vector.Basic.vectorOfFn (fun face =>
    (polynomials.get row).coefficient.eval (refinement.coordinates (parameters.mesh.mesh.triangulation.faces
      face).first)))
  let basis : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularCapBasis refinement := ⟨values,
    coefficients⟩
  refine ⟨regularChart, basis, ?_, ?_, Readings.AffineBasisEnergy.AffineBasis.SurfaceBudget.build basis radius positive⟩
  · intro row vertex
    change (values row) vertex = _
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  · intro row face
    change (coefficients row) face = _
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]

/-- The actual affine-basis sample reads the original homogeneous polynomial combination at each retained vertex. -/
theorem value_readback (sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisSample
  refinement polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (vertex : Fin
      parameters.mesh.mesh.vertices.length) :
    (sample.budget.sample coefficients).primitiveValue vertex =
      polynomials.value coefficients (refinement.coordinates vertex) := by
  rw [sample.budget.sample_value]
  unfold Readings.AffineBasisEnergy.AffineBasis.value
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials.value
  exact FiniteSum.Fin.sumFin_congr fun row => congrArg (fun value => coefficients row * value) (sample.values_eq row
    vertex)

/-- Nonnegative coordinate areas control the full coefficient combination,
with a homogeneous error even at the zero vector. -/
theorem lower (sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisSample refinement
  polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * sample.budget.total) ≤
      (sample.budget.sample coefficients).boundaryArea.im / 4 := by
  have nonnegative : 0 ≤ (sample.budget.sample coefficients).affineEnergy := by
    change 0 ≤ FiniteSum.Fin.sumFin (fun face => Energy.AffineTriangle.coordinateTriangleArea
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).second)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).third) * _)
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 : Fraction.Rational)) _
      (fun face => Fraction.Order.Arithmetic.mul_nonneg_direct (refinement.nonnegative face)
        (Gaussian.Norm.Basic.normSq_nonneg ((sample.budget.sample coefficients).faceCoefficient face)))
    exact FiniteSum.Fin.sumFin_zero.symm.trans_le bound
  have bound := Fraction.Order.Arithmetic.sub_le_sub_direct nonnegative
    (le_refl (a := Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * sample.budget.total))
  rw [zero_sub] at bound
  exact bound.trans (sample.budget.energy_lower coefficients)

end RegularBasisSample
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
