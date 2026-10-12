module
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Polynomial.Geometry.Grid.CellBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAccuracy
import Purelib.Integration.Path.Arc.EnergyCombination
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalArc
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

public section

/-! The requested cap energy controls the complete forward exterior arc
contraction on the same basis samples, with its orientation made explicit. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
open Purelib.Data.Rat
open Purelib.LinearAlgebra.Gaussian.Energy
open Purelib.Polynomial.Geometry.Grid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Integration.Energy.AffineTriangle (coordinateTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
  (ReciprocalGeometry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate (RegularBasisCap)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_congr sumValues_neg)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Normalization
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_zero sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential : Differential
    genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {attached :
    CapAttachment prepared}
  {geometry :
    Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached} {coarse : OrientedTriangle (lifted.vertices.count + attached.words.length)}
  {depth : Nat} {parameters : Purelib.Integration.Path.Dyadic.RadialTriangles.Parameters depth}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap (EnergyBounds)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin_mul_right)
open Purelib.Integration.Energy.AffineTriangle (affinePrimitiveIncrement affinePrimitiveIncrementError)

open Purelib.Riemann.Topology.PrimitiveSurfaceBudget (SurfaceTolerance)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_ge firstQuarterBelow_accurate)

open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)

open _root_.Purelib.Data.Gaussian.Basic (conj)

/-- Forward boundary on the actual attachment words and retained pair of basis polynomials. The cap itself has the
opposite orientation. -/
@[expose] def
  CapBasisEnergy.RegularBasisPolynomials.forwardBoundary
  (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (attached : AllSurfacePreparation.CapAttachment prepared) (depth : Nat) (first second : Fin genus) : Gaussian :=
  CellBoundary.sumValues (fun word => CellBoundary.sumValues (fun edge => Bilinear.arcArea
    (fun point => ⟨conj ((polynomials.get first).primitive.value.eval point),
      (polynomials.get second).primitive.value.eval point⟩)
    depth (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate edge.finish)) word) attached.words

/-- The cached cap energy is exactly the negative coefficient contraction of forward conjugate basis-pair arcs; every
mixed term is retained. -/
theorem
  CapBasisAggregate.RegularBasisCap.Evaluation.area_eq_neg_forward
    {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}
    {caps : CapBasisAggregate.RegularBasisCap geometry parameters polynomials}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} (evaluated : caps.Evaluation coefficients) :
    evaluated.area = -FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second =>
      Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
      polynomials.forwardBoundary attached depth first second)) := by
  rw [evaluated.area_eq_arcs]
  have reversed (word : List (OrientedEdge lifted.vertices.count)) :
      CellBoundary.sumValues (fun edge => ReciprocalRadialGeometry.arcArea (polynomials.value coefficients) depth
        (lifted.vertices.coordinate edge.finish) (lifted.vertices.coordinate edge.start)) word =
      -CellBoundary.sumValues (fun edge => ReciprocalRadialGeometry.arcArea (polynomials.value coefficients) depth
        (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate edge.finish)) word := by
    exact (CellBoundary.sumValues_congr _ _ word (fun edge _ => ReciprocalRadialGeometry.arcArea_reverse
      (polynomials.value coefficients) depth (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate
        edge.finish))).trans
      (CellBoundary.sumValues_neg _ word)
  have boundary := (CellBoundary.sumValues_congr _ _ attached.words (fun word _ => reversed word)).trans
    (CellBoundary.sumValues_neg _ attached.words)
  exact boundary.trans (congrArg Neg.neg (ReciprocalRadialGeometry.words_arcs_energy_combination coefficients
    (fun row point => (polynomials.get row).primitive.value.eval point) lifted.vertices.coordinate depth
      attached.words))

namespace CapBasisRequest.RegularBasisRequest
variable {polynomials :
  RegularBasisPolynomials cap index box}
  {bounds : RegularBasisBounds polynomials
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.boundingBox}
  {minimum : Nat} {target : Purelib.Data.Rat.Fraction.Rational}
  (request : RegularBasisRequest bounds
    attached.caps.length target minimum)
  {parameters : Purelib.Integration.Path.Dyadic.RadialTriangles.Parameters request.depth}

/-- The requested homogeneous cap lower bound gives the needed upper bound on the oppositely oriented exterior arc
contraction, including zero vectors. -/
theorem
  forward_energy_upper
  (caps : CapBasisAggregate.RegularBasisCap geometry parameters polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (evaluated : (request.certify caps).Evaluation coefficients) :
    (FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj
      (coefficients first) * coefficients second *
      polynomials.forwardBoundary attached request.depth first second))).im / 4 ≤
      target * coefficientNormSq coefficients := by
  have lower := request.energy_lower caps coefficients evaluated
  rw [evaluated.area_eq_neg_forward] at lower
  have bound := Fraction.Order.Arithmetic.neg_le_neg_direct lower
  simpa only [Data.Gaussian.Basic.neg_im, Fraction.Field.div_eq_mul_inv_direct, neg_mul, neg_neg] using bound

end CapBasisRequest.RegularBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
