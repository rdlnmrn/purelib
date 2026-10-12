module
import Purelib.Algebra.NatCast
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.RootContinuation.RootRadialBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Homogeneous refinement error on the actual retained root-chart edges. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {comparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell} {target :
    Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
  {index depth stage : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {sample : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}
  {first last : Normalization.InverseRootPolynomial.Coordinate}
  {before : Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Reading regular model sample first target floor stage}
  {after : Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Reading regular model sample last target floor stage}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

universe u

open Purelib.Data.Rat.Fraction.Compatibility

/-- The homogeneous inverse-chart arc error scale from the retained basis coefficient bound and coordinate slope. -/
@[expose] def basisArcScale (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds)
  (slope : Normalization.InverseRootPolynomial.Coordinate) : Coordinate :=
  64 * basis.coefficient^2 * (slope + 4)^2

namespace Path

/-- Geometry belongs to the actual retained path, independently of how its
cell or subinterval request was prepared. -/
@[expose] def BasisArcGeometry (path : Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Path regular model sample target
  floor stage depth before after) (slope : Normalization.InverseRootPolynomial.Coordinate) : Prop :=
  ∀ segment ∈ path.segments,
    regular.padded.Contains (segment.last.root.coordinate * segment.last.root.coordinate) ∧
    regular.padded.Contains (segment.first.root.coordinate * segment.first.root.coordinate) ∧
    Data.Gaussian.Norm.Basic.normSq (segment.last.root.coordinate - segment.first.root.coordinate) ≤
      2 * (slope + 4) * Rational.Geometric.Basic.quarterRadius 1 depth

/-- The squared finite dyadic edge count cancels the unit quarter-power radius exactly. -/
private theorem count_cancel (depth : Nat) :
    (((2 ^ depth : Nat) : Normalization.InverseRootPolynomial.Coordinate) ^ 2) * Rational.Geometric.Basic.quarterRadius
      1 depth = 1 := by
  have square : (((2 ^ depth : Nat) : Normalization.InverseRootPolynomial.Coordinate) ^ 2) = (4 :
    Normalization.InverseRootPolynomial.Coordinate) ^ depth := by
    rw [Purelib.Algebra.NatCast.pow, Nat.cast_ofNat]
    calc
      _ = ((2 : Normalization.InverseRootPolynomial.Coordinate) ^ 2) ^ depth := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = _ := by rw [show (2 : Normalization.InverseRootPolynomial.Coordinate) ^ 2 = 4 by decide]
  rw [square, Rational.Geometric.Basic.quarterRadius]
  exact (Fraction.Field.mul_comm _ _).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (Fraction.Order.Arithmetic.pow_pos_direct (by decide) depth).ne')

/-- Each retained chart segment has the homogeneous refined-arc error bound under its actual root geometry and
odd-degree certificate. -/
private theorem basis_arc_error (path : Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Path regular model sample
  target floor stage depth before after)
    (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (energyDepth : Nat)
    {slope : Normalization.InverseRootPolynomial.Coordinate} (geometry :
      Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs.Path.BasisArcGeometry path slope)
    (segment : Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model sample target floor stage)
    (member : segment ∈ path.segments) :
    Data.Gaussian.Norm.Basic.normSq (RootContinuation.RootRadialGeometry.arcArea (polynomials.value coefficients)
      energyDepth
      segment.last.root.coordinate segment.first.root.coordinate -
      Path.BoundaryRibbon.area (polynomials.value coefficients segment.last.root.coordinate)
        (polynomials.value coefficients segment.first.root.coordinate)) ≤
      Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs.basisArcScale basis slope *
        Rational.Geometric.Basic.quarterRadius 1 depth^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 := by
  have estimate := Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs.BasisBounds.arc_refinement basis
    polynomials coefficients branch
    (geometry segment member).1 (geometry segment member).2.1 energyDepth
  rw [show segment.first.root.coordinate - segment.last.root.coordinate =
    -(segment.last.root.coordinate - segment.first.root.coordinate) by ring1, Gaussian.Norm.Basic.normSq_neg]
      at estimate
  have bounded := Fraction.Order.Arithmetic.pow_le_pow_direct (Gaussian.Norm.Basic.normSq_nonneg _) (geometry segment
    member).2.2 2
  exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤
        16) (Fraction.Order.Arithmetic.sq_nonneg_direct _))) (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans_eq
        (by unfold Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs.basisArcScale; ring1))

/-- The original chart count cancels one dyadic decay factor. The estimate
holds for the full basis at every later polynomial and radial depth. -/
theorem basis_refined_arc_error (path : Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Path regular model sample
  target floor stage depth before after)
    (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds) (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (energyDepth : Nat)
    {slope : Normalization.InverseRootPolynomial.Coordinate} (geometry :
      Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs.Path.BasisArcGeometry path slope) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (path.segments.map (fun segment =>
      RootContinuation.RootRadialGeometry.arcArea (polynomials.value coefficients) energyDepth
        segment.last.root.coordinate segment.first.root.coordinate)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (path.segments.map (fun segment => Path.BoundaryRibbon.area
        (polynomials.value coefficients segment.last.root.coordinate) (polynomials.value coefficients
          segment.first.root.coordinate)))) ≤
      Rational.Geometric.Basic.quarterRadius (Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs.basisArcScale basis
        slope) depth * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  let errors := path.segments.map (fun segment =>
    RootContinuation.RootRadialGeometry.arcArea (polynomials.value coefficients) energyDepth
      segment.last.root.coordinate segment.first.root.coordinate -
      Path.BoundaryRibbon.area (polynomials.value coefficients segment.last.root.coordinate) (polynomials.value
        coefficients segment.first.root.coordinate))
  have scaleNonnegative : 0 ≤ Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs.basisArcScale basis slope :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have errorNonnegative : 0 ≤ Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs.basisArcScale basis slope *
    Rational.Geometric.Basic.quarterRadius 1 depth^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq
    coefficients)^2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct scaleNonnegative
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have each : ∀ value ∈ errors, Data.Gaussian.Norm.Basic.normSq value ≤
      Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs.basisArcScale basis slope *
        Rational.Geometric.Basic.quarterRadius 1 depth^2 * (Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 := by
    intro value member
    obtain ⟨segment, segmentMember, rfl⟩ := Data.List.Map.mem_map.mp member
    exact Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs.Path.basis_arc_error path basis coefficients branch
      energyDepth geometry segment segmentMember
  have length : errors.length ≤ 2^depth := by
    rw [Purelib.Data.List.Map.length_map, path.count_eq]
  have estimate := Path.IncrementArea.sum_bound_of_length errorNonnegative each length
  dsimp only [errors] at estimate
  rw [Purelib.Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_sub] at estimate
  refine estimate.trans_eq ?_
  calc
    _ = ((((2^depth : Nat) : Normalization.InverseRootPolynomial.Coordinate)^2) * Rational.Geometric.Basic.quarterRadius
      1 depth) *
        (Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs.basisArcScale basis slope *
          Rational.Geometric.Basic.quarterRadius 1 depth) * (Readings.PreparedObservationCoercivity.coefficientNormSq
          coefficients)^2 := by ring1
    _ = _ := by
      rw [Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs.Path.count_cancel];
      simp only [-eq_self, -iff_self, Rational.Geometric.Basic.quarterRadius, Fraction.Field.div_eq_mul_inv_direct];
      ring1

end Path
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs
