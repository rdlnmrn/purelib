module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisRadialRibbon
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
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

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Automatic homogeneous radial requests on the actual retained root joins. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.RootContinuation

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {source :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {lastCount : Nat} {lastParent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {lastPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch lastParent} {lastSource :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data lastPatch lastCount}
  {firstEdge lastEdge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge}
  {firstCell : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell source firstEdge} {lastCell :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell lastSource lastEdge}
  {firstModel : Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel firstCell} {lastModel :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel lastCell}
  {firstParameter lastParameter : Normalization.InverseRootPolynomial.Coordinate} {first :
    Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap firstModel firstParameter} {last :
    Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap lastModel lastParameter}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

open Purelib.Data.Rat.Fraction.Compatibility

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

set_option genInjectivity false in
/-- One coordinate request pays every homogeneous primitive connector.
It reuses the original root owners and the shared uniform basis cache. -/
structure BasisRequest (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds) (joined
  : Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join first last)
    (target : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The coefficient-independent radial and primitive comparison scale. -/ scale :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The retained scale equals the original basis coefficient expression. -/ scale_eq : scale = 512 *
    basis.coefficient^2 + 2 * basis.coefficient
  /-- The retained root-coordinate comparison allowance. -/ budget : Normalization.InverseRootPolynomial.Coordinate
  /-- The retained coordinate allowance is positive. -/ budget_positive : 0 < budget
  /-- The complete fixed comparison scale times its allowance fits the target. -/ paid : scale * budget ≤ target
  /-- The comparison of the original joined root-coordinate owners. -/ comparison : Gaussian.Equivalence.Comparison
    (Gaussian.Name.Sampling.approximation first.coordinates.coordinate.prepared.denominator.name)
    (Gaussian.Name.Sampling.approximation last.coordinates.coordinate.prepared.denominator.name) floor floor budget
  /-- The cached common sufficient left and right comparison stage. -/ index : Nat
  /-- The common stage is the maximum of the retained left and right indices. -/ index_eq : index = max
    comparison.leftIndex comparison.rightIndex

constructive_injectivity BasisRequest

namespace BasisRequest

/-- Allocate the fixed basis scale and retain the original joined-coordinate comparison with a common sufficient stage.
-/
@[expose] def build (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds) (joined :
  Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join first last)
    (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests.BasisRequest basis joined target floor := open
      Purelib.Data.Rat in by
  let scale := 512 * basis.coefficient^2 + 2 * basis.coefficient
  have nonnegative : 0 ≤ scale := add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) basis.coefficient_nonnegative)
  let budget := Rational.Budget.Weighted.allowance target scale
  have budgetPositive : 0 < budget := Rational.Budget.Weighted.allowance_positive positive nonnegative
  let comparison := joined.coordinate.compare floor floor budget budgetPositive
  exact ⟨scale, rfl, budget, budgetPositive, Rational.Budget.Weighted.mul_allowance_le positive.le nonnegative,
    comparison, max comparison.leftIndex comparison.rightIndex, rfl⟩

variable {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds} {joined :
  Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join first last} {target :
  Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The retained sufficient index is at least the original reading floor. -/
theorem floor_le (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests.BasisRequest basis joined target
  floor) : floor ≤ request.index := by
  rw [request.index_eq]
  exact request.comparison.left_ge.trans (Purelib.Data.Nat.Order.le_max_left _ _)

/-- The actual endpoint coordinates at any sufficient left and right stages meet the retained coordinate allowance. -/
theorem coordinate_accurate (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests.BasisRequest basis
  joined target floor)
    {index leftIndex rightIndex : Nat} {box : Rational.Box}
    {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
    {left : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint first.coordinates capSample}
    {right : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint last.coordinates capSample}
    (leftReading : Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading left leftIndex)
    (rightReading : Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading right rightIndex)
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex) :
    Data.Gaussian.Norm.Basic.normSq (rightReading.coordinate - leftReading.coordinate) < request.budget := by
  rw [leftReading.coordinate_eq, rightReading.coordinate_eq,
    show (Gaussian.Name.Sampling.approximation last.coordinates.coordinate.prepared.denominator.name).sample rightIndex
      -
      (Gaussian.Name.Sampling.approximation first.coordinates.coordinate.prepared.denominator.name).sample leftIndex =
      -((Gaussian.Name.Sampling.approximation first.coordinates.coordinate.prepared.denominator.name).sample leftIndex -
        (Gaussian.Name.Sampling.approximation last.coordinates.coordinate.prepared.denominator.name).sample rightIndex)
          by ring1,
    Gaussian.Norm.Basic.normSq_neg]
  exact request.comparison.close
    ((Purelib.Data.Nat.Order.le_max_left _ _).trans (request.index_eq.ge.trans leftLater))
    ((Purelib.Data.Nat.Order.le_max_right _ _).trans (request.index_eq.ge.trans rightLater))

/-- Original endpoint readings may have different later indices. The
requested error is uniform in both their shared polynomial stage and depth. -/
theorem radial_accurate (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests.BasisRequest basis joined
  target floor)
    {index leftIndex rightIndex : Nat} {box : Rational.Box}
    {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    {left : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint first.coordinates capSample}
    {right : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint last.coordinates capSample}
    (leftReading : Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading left leftIndex)
    (rightReading : Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading right rightIndex)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (leftInside : regular.padded.Contains (leftReading.coordinate * leftReading.coordinate))
    (rightInside : regular.padded.Contains (rightReading.coordinate * rightReading.coordinate))
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (RootContinuation.RootRadialGeometry.radialArea (polynomials.value coefficients)
      depth rightReading.coordinate -
      RootContinuation.RootRadialGeometry.radialArea (polynomials.value coefficients) depth leftReading.coordinate -
      Path.BoundaryRibbon.area (polynomials.value coefficients leftReading.coordinate)
        (polynomials.value coefficients rightReading.coordinate)) ≤ target *
          (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := open Purelib.Data.Rat in by
  have estimate := Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisRadialRibbon.radial_connector_bound basis
    polynomials coefficients branch leftInside rightInside depth
  have close := request.coordinate_accurate leftReading rightReading leftLater rightLater
  have coefficientLe : 512 * basis.coefficient^2 ≤ request.scale := by
    rw [request.scale_eq]
    exact le_add_of_nonneg_right (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      basis.coefficient_nonnegative)
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficientLe
    request.budget_positive.le).trans request.paid
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct close.le
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
        Normalization.InverseRootPolynomial.Coordinate) ≤ 512) (Fraction.Order.Arithmetic.sq_nonneg_direct _))).trans
        paid)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- The same coordinate request also pays the actual primitive increment. -/
theorem increment_accurate (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests.BasisRequest basis
  joined target floor)
    {index leftIndex rightIndex : Nat} {box : Rational.Box}
    {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    {left : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint first.coordinates capSample}
    {right : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint last.coordinates capSample}
    (leftReading : Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading left leftIndex)
    (rightReading : Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading right rightIndex)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (leftInside : regular.padded.Contains (leftReading.coordinate * leftReading.coordinate))
    (rightInside : regular.padded.Contains (rightReading.coordinate * rightReading.coordinate))
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex) :
    Data.Gaussian.Norm.Basic.normSq (polynomials.value coefficients rightReading.coordinate -
      polynomials.value coefficients leftReading.coordinate) ≤ target *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := open Purelib.Algebra in open
        Purelib.Data.Rat in by
  have estimate := Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs.BasisBounds.chord_increment basis
    polynomials coefficients branch leftInside rightInside
    (left := 0) (right := 1) (by decide +kernel) (by decide +kernel)
  have atZero : RootContinuation.RootRadialGeometry.chord leftReading.coordinate rightReading.coordinate 0 =
    leftReading.coordinate := by
    apply Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, RootContinuation.RootRadialGeometry.chord,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1
  have atOne : RootContinuation.RootRadialGeometry.chord leftReading.coordinate rightReading.coordinate 1 =
    rightReading.coordinate := by
    apply Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, RootContinuation.RootRadialGeometry.chord,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1
  rw [atZero, atOne] at estimate
  have close := request.coordinate_accurate leftReading rightReading leftLater rightLater
  have coefficientLe : 2 * basis.coefficient ≤ request.scale := by
    rw [request.scale_eq]
    exact le_add_of_nonneg_left (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficientLe
    request.budget_positive.le).trans request.paid
  have scalar := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct close.le
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
      Normalization.InverseRootPolynomial.Coordinate) ≤ 2) basis.coefficient_nonnegative)).trans paid
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  exact (estimate.trans_eq (by ring1)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scalar nonnegative)

end BasisRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests
