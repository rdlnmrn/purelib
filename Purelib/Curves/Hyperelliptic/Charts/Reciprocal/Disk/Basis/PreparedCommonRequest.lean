module
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Order
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
public import Purelib.Riemann.Readings.PreparedPrimitiveDepthRequests
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Integration.Path.Dyadic

open Purelib.Integration.Polynomial.Gaussian.Path.Basic

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.AffineBasisEnergy

public section

/-! The common-parent area request and actual prepared integral requests
consume one original basis primitive bank at a single selected index. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)
open Purelib.Riemann.Readings.AffineBasisEnergy (WeightedNormBudget)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations
  (PrimitiveBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests (CoupledLocalPlan)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin_zero sumFin_mul_right)

open Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples (DyadicSample)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements_sub_constant pathArea_dyadicIncrements)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {target :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

variable {minimum : Nat} {common :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}

open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledLocalRequest)

/-- Per-row plans are selected before source polynomials are materialized. -/
@[expose] def BasisPreparedPlans (covers : SourceLocations.BasisSourceCovers parent) (sourceTarget coefficientTarget :
  InverseRootPolynomial.Coordinate) (floor : Nat) :=
  Data.Vector.DependentVector (fun row => PreparedReciprocalControlledRequests.CoupledLocalPlan (covers.get row).data
    sourceTarget sourceTarget coefficientTarget floor)

/-- The actual controlled source requests for every standard differential on the retained parent edge. -/
@[expose] def BasisPreparedRows (covers : SourceLocations.BasisSourceCovers parent) (sourceTarget coefficientTarget :
  InverseRootPolynomial.Coordinate) (floor : Nat) :=
  Data.Vector.DependentVector (fun row => PreparedControlledPrimitiveRequests.ControlledLocalRequest
    (PreparedEdgeRecasting.recastCenteredEdge (PeriodMatrix.standardDifferential row) parent)
    (covers.get row).count sourceTarget coefficientTarget floor)

/-- Exact child geometry, retained separately from counts and total integrals. -/
@[expose] def BasisPreparedRows.Paths {sourceTarget coefficientTarget : InverseRootPolynomial.Coordinate}
    (rows : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedRows covers
      sourceTarget coefficientTarget floor) : Prop :=
  ∀ row (value : InverseRootPolynomial.Gaussian → InverseRootPolynomial.Gaussian),
    (rows.get row).localRequest.request.block.children.map
      (fun child => value (child.edge.point 1) - value (child.edge.point 0)) =
    DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.edge.point parameter))
      (rows.get row).localRequest.request.block.depth 0 1

set_option genInjectivity false in
/-- A common area request and basis source plans sharing one original primitive bank.

A positive per-row source allowance and one cached maximum stage pay the area comparison and all prepared rows. -/
structure BasisPreparedCommonRequest (regular : RegularBounds.Data cap)
    (common : CommonCover.BasisCommonCover cover covers minimum) (areaAllowance sourceTarget coefficientTarget :
      InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The aggregate source error target is strictly positive. -/ source_positive : 0 < sourceTarget
  /-- The shared per-row source allowance. -/ sourceTolerance : InverseRootPolynomial.Coordinate
  /-- The per-row allowance is the aggregate target divided by its finite-count budget. -/ sourceTolerance_eq :
    sourceTolerance = Aggregate.perTerm sourceTarget genus
  /-- The retained per-row source allowance is strictly positive. -/ tolerance_positive : 0 < sourceTolerance
  /-- The common-parent primitive area request on the same retained cover. -/ comparison :
    CommonPrimitiveRequest regular common areaAllowance floor
  /-- The retained controlled basis source plans. -/ prepared :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedPlans covers sourceTolerance
    coefficientTarget floor
  /-- The cached common stage paying the area comparison and every prepared row. -/ index : Nat
  /-- The common stage equals the maximum of the area request and the complete plan bank. -/ index_eq : index = max
    comparison.index (prepared.maximum fun _ plan => plan.index)

constructive_injectivity BasisPreparedCommonRequest

namespace BasisPreparedCommonRequest

/-- Prepare the common area comparison and all basis source plans with one shared source allowance and cached stage. -/
@[expose] def build (regular : RegularBounds.Data cap) (common : CommonCover.BasisCommonCover cover covers minimum)
    (areaAllowance sourceTarget coefficientTarget : InverseRootPolynomial.Coordinate)
    (areaPositive : 0 < areaAllowance) (sourcePositive : 0 < sourceTarget) (coefficientPositive : 0 < coefficientTarget)
    (floor : Nat) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest
      regular common areaAllowance sourceTarget coefficientTarget floor :=
  let sourceTolerance := Aggregate.perTerm sourceTarget genus
  let tolerancePositive := Aggregate.perTerm_positive sourcePositive genus
  let comparison := CommonPrimitiveRequest.build regular common areaAllowance areaPositive floor
  let prepared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedPlans covers
    sourceTolerance coefficientTarget floor := DependentVector.ofFn fun row =>
    CoupledLocalPlan.build (covers.get row).data sourceTolerance sourceTolerance coefficientTarget
      tolerancePositive tolerancePositive coefficientPositive floor
  ⟨sourcePositive, sourceTolerance, rfl, tolerancePositive, comparison, prepared,
    max comparison.index (prepared.maximum fun _ plan => plan.index), rfl⟩

variable {areaAllowance sourceTarget coefficientTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- The area comparison is paid by the cached common stage. -/
theorem comparison_le (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
  areaAllowance sourceTarget coefficientTarget floor) :
    request.comparison.index ≤ request.index := (Purelib.Data.Nat.Order.le_max_left ..).trans_eq request.index_eq.symm

/-- Every retained basis source plan is paid by the cached common stage. -/
theorem prepared_le (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
  areaAllowance sourceTarget coefficientTarget floor)
    (row : Fin genus) : (request.prepared.get row).index ≤ request.index :=
  (request.prepared.get_le_maximum (fun _ plan => plan.index) row).trans
    ((Purelib.Data.Nat.Order.le_max_right ..).trans_eq request.index_eq.symm)

/-- Materialize the prepared source rows from the exact retained primitive bank at a paid stage. -/
@[expose] def preparedRows (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
  areaAllowance sourceTarget coefficientTarget floor)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (later : request.index ≤ index) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedRows covers
      request.sourceTolerance coefficientTarget floor :=
  DependentVector.ofFn fun row =>
    (request.prepared.get row).sourceRequest proper (originals.get row) ((request.prepared_le row).trans later)

/-- Every materialized row retains its original primitive polynomial. -/
theorem preparedRows_primitive (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
  areaAllowance sourceTarget coefficientTarget floor)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (later : request.index ≤ index) (row : Fin genus) :
    ((request.preparedRows proper originals later).get row).localRequest.request.model.primitive.value =
      (originals.get row).primitive.value := by
  unfold PreparedCommonRequest.BasisPreparedCommonRequest.preparedRows
  rw [DependentVector.ofFn_get]
  exact (request.prepared.get row).sourceRequest_primitive proper (originals.get row) ((request.prepared_le row).trans
    later)

/-- Every materialized row records the original primitive index plus two. -/
theorem preparedRows_index (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
  areaAllowance sourceTarget coefficientTarget floor)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (later : request.index ≤ index) (row : Fin genus) :
    ((request.preparedRows proper originals later).get row).localRequest.request.index = 2 + index := by
  unfold PreparedCommonRequest.BasisPreparedCommonRequest.preparedRows
  rw [DependentVector.ofFn_get]
  rfl

set_option genInjectivity false in
/-- Both consumers retain the same original polynomials. The prepared side also retains its actual child blocks,
coefficient bounds and index readbacks. -/
structure Acquisition (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
  areaAllowance sourceTarget coefficientTarget floor)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (cells : BasisSourceLocations.SampleBank covers index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (depth : Nat) where
  /-- The selected common refinement beyond the retained common-cover depth. -/ extraDepth : Nat
  /-- The selected additional refinement respects the requested minimum. -/ minimum_le : depth ≤ extraDepth
  /-- The actual prepared source rows at the shared spatial depth. -/ prepared :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedRows covers
    request.sourceTolerance coefficientTarget floor
  /-- Each prepared row uses the exact original primitive polynomial. -/ primitive_eq : ∀ row, (prepared.get
    row).localRequest.request.model.primitive.value = (originals.get row).primitive.value
  /-- Each prepared row retains the original primitive index plus two. -/ index_eq : ∀ row, (prepared.get
    row).localRequest.request.index = 2 + index
  /-- The retained child blocks give the exact dyadic primitive paths. -/ paths :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedRows.Paths prepared
  /-- All prepared row child blocks use the common cover depth plus the retained additional depth. -/ depths_eq : ∀ row,
    (prepared.get row).localRequest.request.block.depth = common.depth + extraDepth
  /-- The actual common-parent area acquisition at the same additional depth. -/ area :
    CommonPrimitiveRequest.Acquisition request.comparison polynomials originals cells coefficients extraDepth

constructive_injectivity Acquisition

/-- Materialize the basis source rows, refine them to one common depth and acquire the area comparison from the same
original banks. -/
@[expose] def acquire (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
  areaAllowance sourceTarget coefficientTarget floor)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (cells : BasisSourceLocations.SampleBank covers index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (depth : Nat) (later : request.index ≤ index) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition
      request polynomials originals cells coefficients depth := by
  let originalRows := request.preparedRows proper originals later
  let spatialDepth := max (common.depth + depth) (originalRows.maximum fun _ row =>
    row.localRequest.request.block.depth)
  have enough (row : Fin genus) : (originalRows.get row).localRequest.request.block.depth ≤ spatialDepth :=
    (originalRows.get_le_maximum (fun _ row => row.localRequest.request.block.depth) row).trans
      (Purelib.Data.Nat.Order.le_max_right ..)
  let prepared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedRows covers
    request.sourceTolerance coefficientTarget floor := DependentVector.ofFn fun row =>
    (originalRows.get row).atDepth proper spatialDepth (enough row)
  let extraDepth := spatialDepth - common.depth
  have totalDepth : common.depth + extraDepth = spatialDepth :=
    Purelib.Data.Nat.Subtraction.add_sub_of_le ((Nat.le_add_right _ _).trans (Purelib.Data.Nat.Order.le_max_left ..))
  have minimumLe : depth ≤ extraDepth :=
    by
    have bound := (Purelib.Data.Nat.Order.le_max_left (common.depth + depth) _).trans_eq totalDepth.symm
    omega0
  refine ⟨extraDepth, minimumLe, prepared, ?_, ?_, ?_, ?_,
    request.comparison.acquire polynomials originals cells coefficients extraDepth (request.comparison_le.trans later)⟩
  · intro row
    dsimp only [prepared]
    rw [DependentVector.ofFn_get]
    exact request.preparedRows_primitive proper originals later row
  · intro row
    dsimp only [prepared]
    rw [DependentVector.ofFn_get]
    exact request.preparedRows_index proper originals later row
  · intro row value
    dsimp only [prepared]
    rw [DependentVector.ofFn_get]
    exact (originalRows.get row).localRequest.request.atDepth_path proper spatialDepth (enough row) value
  · intro row
    dsimp only [prepared]
    rw [DependentVector.ofFn_get]
    exact totalDepth.symm

namespace Acquisition

variable {request :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular
  common areaAllowance sourceTarget coefficientTarget floor}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box} {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank
    covers index} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {depth : Nat}

/-- The coefficient-weighted value of the actual prepared primitive polynomials at a parent parameter. -/
@[expose] def preparedValue (acquired :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth) (parameter : InverseRootPolynomial.Coordinate) : Gaussian :=
  FiniteSum.Fin.sumFin fun row => coefficients row * (acquired.prepared.get
    row).localRequest.request.model.primitive.value.eval (parent.edge.point parameter)

/-- Exact pointwise readback, rather than equality of final integral totals. -/
theorem preparedValue_eq (acquired :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth) (parameter : InverseRootPolynomial.Coordinate) :
    acquired.preparedValue parameter =
      CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
      originals coefficients parameter := by
  unfold PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition.preparedValue PrimitiveBank.value
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [acquired.primitive_eq row]

/-- Each actual prepared row retains its original polynomial path at the recorded child depth. The acquisition also
certifies that all row depths agree. -/
theorem prepared_primitive_path (acquired :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth) (row : Fin genus) :
    (acquired.prepared.get row).localRequest.request.block.children.map
      (fun child => (acquired.prepared.get row).localRequest.request.model.primitive.value.eval (child.edge.point 1) -
        (acquired.prepared.get row).localRequest.request.model.primitive.value.eval (child.edge.point 0)) =
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => (originals.get row).primitive.value.eval
        (parent.edge.point parameter))
        (acquired.prepared.get row).localRequest.request.block.depth 0 1 := by
  have equal := acquired.paths row (originals.get row).primitive.value.eval
  rw [acquired.primitive_eq row]
  exact equal

/-- Every actual prepared child path reads its original primitive at the shared retained spatial depth. -/
theorem synchronized_primitive_path (acquired :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth) (row : Fin genus) :
    (acquired.prepared.get row).localRequest.request.block.children.map
      (fun child => (acquired.prepared.get row).localRequest.request.model.primitive.value.eval (child.edge.point 1) -
        (acquired.prepared.get row).localRequest.request.model.primitive.value.eval (child.edge.point 0)) =
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => (originals.get row).primitive.value.eval
        (parent.edge.point parameter))
        (common.depth + acquired.extraDepth) 0 1 := by
  rw [acquired.prepared_primitive_path, acquired.depths_eq]

/-- The coefficient-weighted sum of the actual prepared child-block integral samples. -/
@[expose] def integralValue (acquired :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth) : Gaussian :=
  FiniteSum.Fin.sumFin fun row => coefficients row *
    (PathModel.mk
      ((acquired.prepared.get row).localRequest.request.block.children.map
        PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample

/-- The retained actual prepared child integrals approximate the shared original primitive increment for every Gaussian
coefficient vector. -/
theorem integral_error (acquired :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth) :
    Data.Gaussian.Norm.Basic.normSq (PrimitiveBank.value originals coefficients 1 - PrimitiveBank.value
      originals coefficients 0 - acquired.integralValue) ≤
      sourceTarget * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  let errors := fun row =>
    (acquired.prepared.get row).localRequest.request.model.primitive.value.eval (parent.edge.point 1) -
    (acquired.prepared.get row).localRequest.request.model.primitive.value.eval (parent.edge.point 0) -
    (PathModel.mk
      ((acquired.prepared.get row).localRequest.request.block.children.map
        PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample
  let budget := WeightedNormBudget.build errors
  have each (row : Fin genus) : Data.Gaussian.Norm.Basic.normSq (errors row) ≤ request.sourceTolerance := by
    have scalar := ((acquired.prepared.get row).localRequest.accurate request.tolerance_positive).le
    change Data.Gaussian.Basic.Canonical.normSq (errors row) ≤ request.sourceTolerance at scalar
    rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  have paid : budget.scale ≤ sourceTarget := by
    rw [budget.scale_eq]
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Order.Positivity.sumFin_mono _ _ each)
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
    rw [Purelib.Algebra.FiniteSum.Fin.Rational.sum_constant, request.sourceTolerance_eq] at bound
    exact bound.trans (Aggregate.count_mul_perTerm_lt request.source_positive genus).le
  have equal : PrimitiveBank.value originals coefficients 1 - PrimitiveBank.value originals coefficients 0 -
    acquired.integralValue =
      FiniteSum.Fin.sumFin (fun row => coefficients row * errors row) := by
    rw [← acquired.preparedValue_eq 1, ← acquired.preparedValue_eq 0]
    unfold PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition.preparedValue
      PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition.integralValue
    rw [← FiniteSum.Fin.sumFin_sub, ← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    dsimp only [errors]
    ring1
  have nonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : InverseRootPolynomial.Coordinate)) _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  rw [equal]
  exact (budget.bound coefficients).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid nonnegative).trans_eq (by ring1))

end Acquisition
end BasisPreparedCommonRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
