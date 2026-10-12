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
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.IncrementRestoration
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests
import Purelib.Integration.Path.HomogeneousIncrementRestoration
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
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

/-! A shared request pays both the retained endpoint gap and its shifted
radial-potential join, without normalizing the coefficient vector. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins

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
/-- A shared request for the actual joined root coordinates, endpoint gaps and radial-potential restoration.

It retains separate endpoint and radial allowances and one sufficient stage before coefficient-dependent evaluation. -/
structure BasisRestorationRequest (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds
  bounds) (joined : Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join first last)
    (target : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The whole restoration target is positive. -/ positive : 0 < target
  /-- The retained local endpoint-gap allowance. -/ endpointTarget : Normalization.InverseRootPolynomial.Coordinate
  /-- The endpoint allowance is one sixteenth of the original target. -/ endpoint_eq : endpointTarget = target / 16
  /-- The actual retained homogeneous radial comparison request. -/ radial :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests.BasisRequest basis joined target floor
  /-- The cached endpoint comparison coefficient scale. -/ scale : Normalization.InverseRootPolynomial.Coordinate
  /-- The scale is twice the original basis coefficient bound. -/ scale_eq : scale = 2 * basis.coefficient
  /-- The retained original root-coordinate comparison allowance. -/ budget :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The coordinate comparison allowance is positive. -/ budget_positive : 0 < budget
  /-- The scaled coordinate allowance fits the retained endpoint target. -/ paid : scale * budget ≤ endpointTarget
  /-- The actual comparison of the two original prepared denominator root names. -/ comparison :
    Gaussian.Equivalence.Comparison
    (Gaussian.Name.Sampling.approximation first.coordinates.coordinate.prepared.denominator.name)
    (Gaussian.Name.Sampling.approximation last.coordinates.coordinate.prepared.denominator.name) floor floor budget
  /-- The cached sufficient stage for radial and coordinate comparisons. -/ index : Nat
  /-- The common stage is exactly the maximum of all retained comparison indices. -/ index_eq : index = max radial.index
    (max comparison.leftIndex comparison.rightIndex)

constructive_injectivity BasisRestorationRequest

namespace BasisRestorationRequest

/-- Prepare the original radial request and paid endpoint coordinate comparison with one shared sufficient stage. -/
@[expose] def build (basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds) (joined :
  Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join first last)
    (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins.BasisRestorationRequest basis joined target floor :=
      by
  let endpointTarget := target / 16
  have endpointPositive : 0 < endpointTarget := Fraction.Order.Field.div_pos_direct positive (by decide)
  let radial := Hyperelliptic.Charts.Reciprocal.Disk.Basis.JunctionRequests.BasisRequest.build basis joined target
    positive floor
  let scale := 2 * basis.coefficient
  have nonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) basis.coefficient_nonnegative
  let budget := Rational.Budget.Weighted.allowance endpointTarget scale
  have budgetPositive := Rational.Budget.Weighted.allowance_positive endpointPositive nonnegative
  let comparison := joined.coordinate.compare floor floor budget budgetPositive
  exact ⟨positive, endpointTarget, rfl, radial, scale, rfl, budget, budgetPositive,
    Rational.Budget.Weighted.mul_allowance_le endpointPositive.le nonnegative, comparison,
    max radial.index (max comparison.leftIndex comparison.rightIndex), rfl⟩

variable {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds} {joined :
  Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join first last} {target :
  Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
  {index leftIndex rightIndex : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {left : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint first.coordinates capSample}
  {right : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint last.coordinates capSample}

/-- The finite squared Gaussian coefficient norm is nonnegative. -/
private theorem norm_nonnegative (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : 0 ≤
  Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
  open Purelib.Algebra in FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))

/-- The retained endpoint allowance is at most the whole restoration target. -/
theorem endpoint_le (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins.BasisRestorationRequest basis
  joined target floor) : request.endpointTarget ≤ target := by
  rw [request.endpoint_eq]
  apply (Fraction.Order.Field.div_le_iff_pos (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 16)).mpr
  exact (show target = target * 1 by ring1).trans_le
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide) request.positive.le)

/-- The extra coordinate request controls the actual polynomial endpoint
increment, separately from the radial area defect. -/
theorem chart_gap (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins.BasisRestorationRequest basis
  joined target floor)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (leftReading : Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading left leftIndex)
    (rightReading : Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading right rightIndex)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (leftInside : regular.padded.Contains (leftReading.coordinate * leftReading.coordinate))
    (rightInside : regular.padded.Contains (rightReading.coordinate * rightReading.coordinate))
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex) :
    Data.Gaussian.Norm.Basic.normSq (polynomials.value coefficients rightReading.coordinate - polynomials.value
      coefficients leftReading.coordinate) ≤
      request.endpointTarget * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have estimate := Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisArcs.BasisBounds.chord_increment basis
    polynomials coefficients branch leftInside rightInside
    (left := 0) (right := 1) (by decide) (by decide)
  have atZero : RootContinuation.RootRadialGeometry.chord leftReading.coordinate rightReading.coordinate 0 =
    leftReading.coordinate := by
    apply Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, RootContinuation.RootRadialGeometry.chord,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1
  have atOne : RootContinuation.RootRadialGeometry.chord leftReading.coordinate rightReading.coordinate 1 =
    rightReading.coordinate := by
    apply Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, RootContinuation.RootRadialGeometry.chord,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1
  rw [atZero, atOne, show ((1 : Normalization.InverseRootPolynomial.Coordinate) - 0)^2 = 1 by decide,
    Fraction.Field.mul_one_direct] at estimate
  have close : Data.Gaussian.Norm.Basic.normSq (rightReading.coordinate - leftReading.coordinate) < request.budget
    := by
    rw [leftReading.coordinate_eq, rightReading.coordinate_eq,
      show (Gaussian.Name.Sampling.approximation last.coordinates.coordinate.prepared.denominator.name).sample
        rightIndex -
        (Gaussian.Name.Sampling.approximation first.coordinates.coordinate.prepared.denominator.name).sample leftIndex =
        -((Gaussian.Name.Sampling.approximation first.coordinates.coordinate.prepared.denominator.name).sample leftIndex
          -
          (Gaussian.Name.Sampling.approximation last.coordinates.coordinate.prepared.denominator.name).sample
            rightIndex) by ring1, Gaussian.Norm.Basic.normSq_neg]
    exact request.comparison.close
      ((Purelib.Data.Nat.Order.le_max_left _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans
        (request.index_eq.symm.trans_le leftLater)))
      ((Purelib.Data.Nat.Order.le_max_right _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans
        (request.index_eq.symm.trans_le rightLater)))
  have scaleNonnegative : 0 ≤ request.scale := request.scale_eq.symm ▸ Fraction.Order.Arithmetic.mul_nonneg_direct (by
    decide) basis.coefficient_nonnegative
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct close.le scaleNonnegative).trans request.paid
  rw [request.scale_eq] at paid
  exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins.BasisRestorationRequest.norm_nonnegative
    coefficients)).trans_eq (by ring1))

/-- Chart-to-direct offsets and the polynomial gap pay the gap of the
retained direct endpoints; no equality of independently sampled roots is used. -/
theorem direct_gap (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins.BasisRestorationRequest basis
  joined target floor)
    {firstChart lastChart firstDirect lastDirect : Normalization.InverseRootPolynomial.Gaussian} (coefficients :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (firstClose : Data.Gaussian.Norm.Basic.normSq (firstDirect - firstChart) ≤ request.endpointTarget *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
    (lastClose : Data.Gaussian.Norm.Basic.normSq (lastDirect - lastChart) ≤ request.endpointTarget *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
    (chartClose : Data.Gaussian.Norm.Basic.normSq (lastChart - firstChart) ≤ request.endpointTarget *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Data.Gaussian.Norm.Basic.normSq (lastDirect - firstDirect) ≤ target *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have firstReversed : Data.Gaussian.Norm.Basic.normSq (firstChart - firstDirect) ≤ request.endpointTarget *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [show firstChart - firstDirect = -(firstDirect - firstChart) by ring1, Gaussian.Norm.Basic.normSq_neg]
    exact firstClose
  have middle := (Gaussian.Norm.Bounds.normSq_sub_le_via lastChart firstChart firstDirect).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct chartClose
      firstReversed) (by decide))
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_via lastDirect lastChart firstDirect).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct lastClose
      middle) (by decide))
  have endpointNonnegative : 0 ≤ request.endpointTarget := by
    rw [request.endpoint_eq]
    exact (Fraction.Order.Field.div_pos_direct request.positive (by decide)).le
  have factor := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
      decide : (10 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16)
    (Fraction.Order.Arithmetic.mul_nonneg_direct endpointNonnegative
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins.BasisRestorationRequest.norm_nonnegative
      coefficients))
  have paid : 16 * request.endpointTarget = target := by
    rw [request.endpoint_eq, Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  exact estimate.trans ((show 2 * (request.endpointTarget * Readings.PreparedObservationCoercivity.coefficientNormSq
    coefficients +
    2 * (request.endpointTarget * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients +
      request.endpointTarget * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)) =
    10 * (request.endpointTarget * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) by
      ring1).trans_le
      (factor.trans_eq (by rw [← Fraction.Field.mul_assoc, paid])))

/-- The same actual root join pays the shifted endpoint potentials once
the two basis direct readings satisfy their preselected endpoint targets. -/
theorem potential_accurate (request :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins.BasisRestorationRequest basis joined target floor)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (leftReading : Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading left leftIndex)
    (rightReading : Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading right rightIndex)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (leftInside : regular.padded.Contains (leftReading.coordinate * leftReading.coordinate))
    (rightInside : regular.padded.Contains (rightReading.coordinate * rightReading.coordinate))
    (leftLater : request.index ≤ leftIndex) (rightLater : request.index ≤ rightIndex) (depth : Nat)
    (firstDirect lastDirect : Normalization.InverseRootPolynomial.Gaussian)
    (firstClose : Data.Gaussian.Norm.Basic.normSq (firstDirect - polynomials.value coefficients
      leftReading.coordinate) ≤ request.endpointTarget * Readings.PreparedObservationCoercivity.coefficientNormSq
      coefficients)
    (lastClose : Data.Gaussian.Norm.Basic.normSq (lastDirect - polynomials.value coefficients
      rightReading.coordinate) ≤ request.endpointTarget * Readings.PreparedObservationCoercivity.coefficientNormSq
      coefficients)
    (small : target ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementRestoration.potential
      (RootContinuation.RootRadialGeometry.radialArea (polynomials.value coefficients) depth rightReading.coordinate)
      (polynomials.value coefficients rightReading.coordinate) lastDirect -
      Path.IncrementRestoration.potential (RootContinuation.RootRadialGeometry.radialArea (polynomials.value
        coefficients) depth leftReading.coordinate)
        (polynomials.value coefficients leftReading.coordinate) firstDirect - Path.BoundaryRibbon.area firstDirect
          lastDirect) ≤
      (80 * target + 2 * target) * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have base := request.radial.radial_accurate polynomials coefficients leftReading rightReading branch leftInside
    rightInside
    ((Purelib.Data.Nat.Order.le_max_left _ _).trans (request.index_eq.symm.trans_le leftLater))
    ((Purelib.Data.Nat.Order.le_max_left _ _).trans (request.index_eq.symm.trans_le rightLater)) depth
  have gap := request.direct_gap coefficients firstClose lastClose
    (request.chart_gap polynomials coefficients leftReading rightReading branch leftInside rightInside leftLater
      rightLater)
  have firstOffset : Data.Gaussian.Norm.Basic.normSq (polynomials.value coefficients leftReading.coordinate -
    firstDirect) ≤ target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [show polynomials.value coefficients leftReading.coordinate - firstDirect =
      -(firstDirect - polynomials.value coefficients leftReading.coordinate) by ring1, Gaussian.Norm.Basic.normSq_neg]
    exact firstClose.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct request.endpoint_le
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins.BasisRestorationRequest.norm_nonnegative
      coefficients))
  have lastOffset : Data.Gaussian.Norm.Basic.normSq (polynomials.value coefficients rightReading.coordinate -
    lastDirect) ≤ target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    rw [show polynomials.value coefficients rightReading.coordinate - lastDirect =
      -(lastDirect - polynomials.value coefficients rightReading.coordinate) by ring1, Gaussian.Norm.Basic.normSq_neg]
    exact lastClose.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct request.endpoint_le
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins.BasisRestorationRequest.norm_nonnegative
      coefficients))
  have smallWeight : target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct small
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins.BasisRestorationRequest.norm_nonnegative
      coefficients)).trans_eq (by ring1)
  exact Path.HomogeneousIncrementRestoration.potential_join_bound_homogeneous base firstOffset lastOffset
    (lastOffset.trans smallWeight) (gap.trans smallWeight)

end BasisRestorationRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.RestorationJoins
