module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootOwners
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPathSamples
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational.Box

open Purelib.Integration.Polynomial.Gaussian.Path.Basic

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Riemann.RootContinuation

@[expose] public section

/-!
# Reciprocal-owner readings of retained prepared boundary cells

The actual reciprocal owner's coefficient is compared to the original
persisted coefficient state. Its finite reading error is paid in addition
to the original cell's model allowance and the non-affine inversion error.
These are samples of the actual owner programs, not exact rational roots or
an identification of the inverted arc with its endpoint chord.
-/

open Purelib.Data

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

/-- Read the original persisted center name with the coherence of its retained differential coefficient channel. -/
public def centeredChannel (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) :
  Coherent.CoherentNamed :=
  { name := parent.center.named
    coherent := (parent.edge.coefficient 0 parent.edge.baseInside).coherent }

/-- The same cached point-query root used by the original prepared model. -/
def root (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)) :=
  ReciprocalRootNames.ofPreparedEdge parent.edge 0 parent.edge.baseInside
    (PreparedExteriorReciprocal.parent_point_nonzero boundary parent.edge.baseInside)

/-- A winding-owner attachment to the reciprocal scaling of the original cached point-query root. -/
abbrev Attachment (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)) :=
  SquareRootChannelOwnership.Attachment (root parent
    boundary).prepared.denominator
    ((HyperellipticReciprocal.polynomial curve).eval (parent.edge.point 0)⁻¹)

/-- Read the reciprocal differential coefficient on the same retained attached winding owner. -/
def ownerCoefficient {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)}
    (attached : Attachment parent boundary) :=
  ReciprocalRootOwners.coefficient differential (parent.edge.point 0) attached.owner

/-- Normalize only the comparison's right side to products of the actual later persisted-centre readings. The left side
still samples the attached winding owner's coefficient program. -/
def centerComparison (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential)
    (boundary : PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)) (attached :
      Attachment parent boundary) :
    Gaussian.Equivalence.Equivalent
      (Sampling.approximation (ownerCoefficient
        attached).name)
      (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation
        (Coherence.exact (-(parent.edge.point 0 ^ 2))).name parent.center.named) := by
  let factor := Coherence.exact (-(parent.edge.point 0 ^ 2))
  let original := parent.edge.coefficient 0 parent.edge.baseInside
  let centered := centeredChannel parent
  let product := Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation factor.name centered.name
  have chart := (ReciprocalRootOwners.coefficient_handoff differential (parent.edge.point 0)
    (root parent boundary) attached).trans
    (ReciprocalRootNames.prepared_coefficient_transport parent.edge 0 parent.edge.baseInside
      (PreparedExteriorReciprocal.parent_point_nonzero boundary parent.edge.baseInside))
  have replaced := chart.trans
    (Congruence.coherentMul_respects factor factor original centered
      (NamedEquivalent.refl _) parent.center.equivalent)
  exact Equivalent.trans
    (replaced.trans (Bridge.coherentMul_toNamed factor centered))
    (Equivalent.toNamed_sampling product)

set_option genInjectivity false in
/-- The program is abstract here so generating the record projections does not unfold its retained root and continuation
caches. -/
structure Observation (program : Gaussian.Name.Basic.Named) (ideal : Data.Gaussian.Basic.Canonical) (bound :
  Fraction.Rational) where
  /-- The retained finite reading index in the original coefficient program. -/ index : Nat
  /-- The cached original coefficient-program reading at the retained index. -/ value : Data.Gaussian.Basic.Canonical
  /-- The cached value is exactly the original program's retained-index sample. -/ value_eq : value =
    (Sampling.approximation program).sample index
  /-- The retained reading discrepancy squared norm is bounded by the original supplied allowance. -/ close :
    Data.Gaussian.Norm.Basic.normSq (value - ideal) ≤ bound

constructive_injectivity Observation

/-- Pay the coefficient reading target and the original model allowance after reciprocal-coordinate scaling. -/
def coefficientAllowance (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (target :
  Fraction.Rational) : Fraction.Rational :=
  2 * (target + Data.Gaussian.Norm.Basic.normSq (parent.edge.point 0) ^ 2 * parent.edge.modelErrorAllowance)

/-- One requested actual reciprocal coefficient reading. The persisted original centre need not be an exact differential
value; its existing model allowance is explicitly retained. -/
def observe (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve))
    (attached : Attachment parent boundary) (target :
      Fraction.Rational) (positive : 0 < target) :
    Observation
      (ownerCoefficient attached).name
      (PreparedExteriorReciprocal.parentSample parent boundary).coefficient
      (coefficientAllowance parent target) := by
  let comparison := (centerComparison parent boundary
    attached).compare 0 0 target positive
  let value := (Sampling.approximation
    (ownerCoefficient attached).name).sample
    comparison.leftIndex
  refine ⟨comparison.leftIndex, value, rfl, ?_⟩
  let later := parent.center.laterValue comparison.rightIndex
  let multiplier := -(parent.edge.point 0 ^ 2)
  have close : Data.Gaussian.Norm.Basic.normSq (value - multiplier * later) < target :=
    comparison.close (Nat.le_refl comparison.leftIndex) (Nat.le_refl comparison.rightIndex)
  have centerBound : Data.Gaussian.Norm.Basic.normSq (multiplier * later - multiplier * parent.center.value) ≤
      Data.Gaussian.Norm.Basic.normSq (parent.edge.point 0) ^ 2 * parent.edge.modelErrorAllowance := by
    rw [← mul_sub, Data.Gaussian.Norm.Basic.normSq_mul]
    have norm : Data.Gaussian.Norm.Basic.normSq multiplier = Data.Gaussian.Norm.Basic.normSq
      (parent.edge.point 0) ^ 2 := by
      rw [Data.Gaussian.Norm.Basic.normSq_neg, Power.normSq_pow]
    rw [norm]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (parent.center.laterValue_sub_value_lt comparison.rightIndex).le
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have ideal : (PreparedExteriorReciprocal.parentSample parent boundary).coefficient = multiplier * parent.center.value
    := by
    rw [PreparedExteriorReciprocal.parentSample_coefficient]
    dsimp only [multiplier]
    ring1
  rw [ideal]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_via value (multiplier * later) (multiplier *
    parent.center.value)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add close.le centerBound) (by decide))

/-- Ownership, the actual requested reading and its provenance are retained together. Repeated sample/error queries do
not reacquire the winding owner. -/
abbrev Reading (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve))
    (target : Fraction.Rational) :=
  (attached : Attachment parent boundary) ×
    Observation
    (ownerCoefficient attached).name
    (PreparedExteriorReciprocal.parentSample parent boundary).coefficient
      (coefficientAllowance parent target)

/-- Attach the original scaled root once and retain its requested coefficient observation. -/
def acquire (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential) (boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve))
    (target : Fraction.Rational) (positive : 0 < target) :
      Reading parent boundary target :=
  let attached := ReciprocalRootOwners.attach (root
    parent boundary)
  ⟨attached, observe parent boundary attached target
    positive⟩

/-- Multiply the retained reciprocal coefficient observation by the original inverse-endpoint displacement. -/
def sample {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)}
    {target : Fraction.Rational} (reading : Reading
      parent boundary target) : Gaussian :=
  ((parent.edge.point 1)⁻¹ - (parent.edge.point 0)⁻¹) * reading.2.value

/-- The exact inverse-endpoint displacement is the negative original displacement divided by the nonzero endpoint
product. -/
private theorem inverse_displacement {first last : Data.Gaussian.Basic.Canonical} (firstNonzero : first ≠ 0)
  (lastNonzero : last ≠ 0) :
    last⁻¹ - first⁻¹ = -(last - first) / (first * last) := by
  apply Data.Gaussian.Field.mul_right_cancel_of_ne (Data.Gaussian.Field.mul_ne_zero_direct firstNonzero lastNonzero)
  rw [Algebra.Field.ExplicitField.div_mul_cancel _ (Data.Gaussian.Field.mul_ne_zero_direct firstNonzero lastNonzero)]
  calc
    _ = first * (last * last⁻¹) - last * (first * first⁻¹) := by ring1
    _ = _ := by
      rw [Algebra.Field.ExplicitField.mul_inv_cancel _ lastNonzero, Algebra.Field.ExplicitField.mul_inv_cancel _
        firstNonzero]
      ring1

/-- Inversion does not expand squared distance between points on the fixed exterior boundary. This applies to every
rational subedge, not only its ends. -/
theorem inverse_movement_between {first last : Data.Gaussian.Basic.Canonical}
    (firstBoundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) first)
    (lastBoundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) last) :
    Data.Gaussian.Norm.Basic.normSq (last⁻¹ - first⁻¹) ≤ Data.Gaussian.Norm.Basic.normSq (last -
      first) := by
  have firstNonzero := PreparedExteriorReciprocal.boundary_nonzero firstBoundary
  have lastNonzero := PreparedExteriorReciprocal.boundary_nonzero lastBoundary
  have firstLower := PreparedExteriorReciprocal.boundary_norm_lower firstBoundary
  have lastLower := PreparedExteriorReciprocal.boundary_norm_lower lastBoundary
  have productLower : (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq first *
    Data.Gaussian.Norm.Basic.normSq last := by
    simpa only [Fraction.Field.one_mul] using
      Fraction.Order.Arithmetic.mul_le_mul_direct firstLower lastLower (by decide)
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)
  rw [inverse_displacement firstNonzero lastNonzero,
    Data.Gaussian.Field.normSq_div _ _ (Data.Gaussian.Field.mul_ne_zero_direct firstNonzero lastNonzero),
    Data.Gaussian.Norm.Basic.normSq_neg, Data.Gaussian.Norm.Basic.normSq_mul]
  apply (Fraction.Order.Field.div_le_iff_pos ((by decide : (0 : Fraction.Rational) < 1).trans_le productLower)).mpr
  simpa only [Fraction.Field.mul_one_direct] using
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct productLower (Data.Gaussian.Norm.Basic.normSq_nonneg
      (last - first))

/-- The original prepared boundary cell's reciprocal displacement squared norm is bounded by its retained source
movement. -/
private theorem inverse_movement (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential)
    (boundary : PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)) :
    Data.Gaussian.Norm.Basic.normSq ((parent.edge.point 1)⁻¹ - (parent.edge.point 0)⁻¹) ≤
      Data.Gaussian.Norm.Basic.normSq parent.model.displacement :=
  inverse_movement_between (boundary.point
    parent.edge.baseInside)
    (boundary.point (fraction := 1) (by constructor <;> decide))

/-- Readback error is weighted by the actual reciprocal displacement. Boundary coordinate clearance permits replacing
that weight by the original movement; no endpoint chord is asserted to be the whole inverted path. -/
theorem sample_error {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)}
    {target : Fraction.Rational} (reading : Reading
      parent boundary target) (positive : 0 < target) :
    Data.Gaussian.Norm.Basic.normSq (sample
      reading - (PreparedExteriorReciprocal.parentSample parent boundary).sample) ≤
      Data.Gaussian.Norm.Basic.normSq parent.model.displacement *
        coefficientAllowance parent target := by
  let ideal := PreparedExteriorReciprocal.parentSample parent boundary
  have identity : sample reading - ideal.sample =
      ((parent.edge.point 1)⁻¹ - (parent.edge.point 0)⁻¹) * (reading.2.value - ideal.coefficient) := by
    rw [sample, ideal.sample_eq, ideal.start_eq,
      ideal.finish_eq]
    change ((parent.edge.point 1)⁻¹ - (parent.edge.point 0)⁻¹) * reading.2.value -
      ((parent.edge.point 1)⁻¹ - (parent.edge.point 0)⁻¹) * ideal.coefficient = _
    ring1
  rw [identity, Data.Gaussian.Norm.Basic.normSq_mul]
  have allowanceNonnegative : 0 ≤ coefficientAllowance
    parent target :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg positive.le (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct _) parent.edge.modelErrorAllowance_positive.le))
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct reading.2.close
    (Data.Gaussian.Norm.Basic.normSq_nonneg _)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (inverse_movement parent boundary)
      allowanceNonnegative)

/-- The original cell-sample discrepancy is bounded by its inversion error and paid reciprocal coefficient observation
error. -/
private theorem cell_error {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {boundary :
  PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)}
    {target density allowance movement : Fraction.Rational} (reading :
      Reading parent boundary target) (positive : 0 <
      target)
    (coefficientBound : Data.Gaussian.Norm.Basic.normSq parent.center.value ≤ density) (allowanceBound :
      parent.edge.modelErrorAllowance ≤ allowance)
    (movementBound : Data.Gaussian.Norm.Basic.normSq parent.model.displacement ≤ movement) :
    Data.Gaussian.Norm.Basic.normSq (parent.model.integralSample -
      sample reading) ≤
      2 * density * movement ^ 2 + 4 * movement * (target + (Cuts.Ambient curve).normSqBound ^ 2 * allowance) := by
  let ideal := PreparedExteriorReciprocal.parentSample parent boundary
  have densityNonnegative := (Data.Gaussian.Norm.Basic.normSq_nonneg parent.center.value).trans coefficientBound
  have allowanceNonnegative := parent.edge.modelErrorAllowance_positive.le.trans allowanceBound
  have inversion : Data.Gaussian.Norm.Basic.normSq (parent.model.integralSample - ideal.sample) ≤ density *
    movement ^ 2 := by
    have estimate := ideal.error_bound (lower := 1) (by decide) coefficientBound
      (PreparedExteriorReciprocal.boundary_norm_lower (boundary.point (fraction := 1) (by constructor <;> decide)))
    have divideOne : density / 1 = density :=
      (show density / 1 = (density / 1) * 1 by ring1).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
    rw [divideOne] at estimate
    exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _) movementBound 2)
        densityNonnegative)
  have coefficientError : coefficientAllowance parent
    target ≤
      2 * (target + (Cuts.Ambient curve).normSqBound ^ 2 * allowance) := by
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _ (by decide)
    apply add_le_add (le_refl target)
    exact Fraction.Order.Arithmetic.mul_le_mul_direct
      (Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _)
        (Rational.Box.normSq_le_normSqBound boundary.startInside) 2)
      allowanceBound parent.edge.modelErrorAllowance_positive.le (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have budgetNonnegative : 0 ≤ 2 * (target + (Cuts.Ambient curve).normSqBound ^ 2 * allowance) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg positive.le (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct _) allowanceNonnegative))
  have observation : Data.Gaussian.Norm.Basic.normSq (ideal.sample -
    sample reading) ≤
      movement * (2 * (target + (Cuts.Ambient curve).normSqBound ^ 2 * allowance)) := by
    rw [show ideal.sample - sample reading =
      -(sample reading - ideal.sample) by ring1,
      Data.Gaussian.Norm.Basic.normSq_neg]
    exact (sample_error reading positive).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct coefficientError
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct movementBound budgetNonnegative))
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_via parent.model.integralSample ideal.sample
    (sample reading)).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add inversion observation) (by
      decide)).trans_eq (by ring1))

set_option genInjectivity false in
/-- One owner-backed reading for every occurrence of the retained parent list. This spine keeps equal-looking cells as
distinct occurrences. -/
inductive Readings (target : Fraction.Rational) : List (PreparedSubdivisionModelCore.CenteredEdge curve differential) →
  Type 1
  /-- The empty original parent list has no reciprocal readings. -/ | nil :
    Readings target []
  /-- Retain the original head parent's boundary proof and owner-backed reading, followed by the exact original tail. -/
    | cons {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {remaining : List
    (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      (boundary : PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)) (head :
        Reading parent boundary target)
      (tail : Readings target remaining) :
        Readings target (parent :: remaining)

constructive_injectivity Readings

namespace Readings

/-- Acquire one owner-backed reading for each original parent occurrence while preserving its retained boundary evidence
and list order. -/
def build (target : Fraction.Rational) (positive : 0 < target) : (parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve differential)) →
    (∀ parent ∈ parents, PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve)) →
      Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.Readings target parents
  | [], _ => .nil
  | parent :: remaining, boundary =>
      let first := boundary parent (List.mem_cons_self ..)
      .cons first (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.acquire parent first target
        positive)
        (build target positive
          remaining (fun other member => boundary other (List.mem_cons_of_mem _ member)))

/-- Read cached reciprocal samples in the original parent-occurrence order. -/
def values {target : Fraction.Rational} : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve
  differential)} → Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.Readings target parents → List
  Data.Gaussian.Basic.Canonical
  | _, .nil => []
  | _, .cons _ head tail => Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.sample head :: tail.values

/-- Read each original parent integral sample minus its corresponding retained reciprocal sample. -/
def errors {target : Fraction.Rational} : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve
  differential)} → Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.Readings target parents → List
  Data.Gaussian.Basic.Canonical
  | _, .nil => []
  | parent :: _, .cons _ head tail => (parent.model.integralSample -
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.sample head) :: tail.errors

/-- There is exactly one retained reciprocal discrepancy for each original parent occurrence. -/
theorem errors_length {target : Fraction.Rational} {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve
  differential)} (readings : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.Readings target parents) :
    readings.errors.length = parents.length := by
  induction readings with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg Nat.succ ih

/-- The retained discrepancy sum equals the original integral sample minus the retained reciprocal sample sum. -/
theorem errors_sum {target : Fraction.Rational} {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve
  differential)} (readings : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.Readings target parents) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum readings.errors = (PathModel.mk (parents.map
      PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample - Data.Gaussian.Norm.Sum.Basic.gaussianSum
      readings.values := by
  induction readings with
  | nil => change (0 : Data.Gaussian.Basic.Canonical) = 0 - 0; ring1
  | @cons parent remaining boundary head tail ih =>
      change (parent.model.integralSample - Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.sample
        head) + Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.errors = _
      rw [ih]
      change (parent.model.integralSample - Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.sample
        head) +
        ((PathModel.mk (remaining.map PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample -
          Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.values) =
        (parent.model.integralSample + (PathModel.mk (remaining.map
          PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample) -
        (Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.sample head +
          Data.Gaussian.Norm.Sum.Basic.gaussianSum tail.values)
      ring1

/-- Uniform original coefficient, allowance and movement bounds control every retained reciprocal sample discrepancy. -/
private theorem errors_bounded {target density allowance movement : Fraction.Rational}
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (readings :
      Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.Readings target parents) (positive : 0 < target)
    (coefficients : ∀ parent ∈ parents, Data.Gaussian.Norm.Basic.normSq parent.center.value ≤ density)
    (allowances : ∀ parent ∈ parents, parent.edge.modelErrorAllowance ≤ allowance)
    (movements : ∀ parent ∈ parents, Data.Gaussian.Norm.Basic.normSq parent.model.displacement ≤ movement) :
    ∀ error ∈ readings.errors, Data.Gaussian.Norm.Basic.normSq error ≤
      2 * density * movement ^ 2 + 4 * movement * (target + (Cuts.Ambient curve).normSqBound ^ 2 * allowance) := by
  induction readings with
  | nil => intro error member; cases member
  | @cons parent remaining boundary head tail ih =>
      intro error member
      rcases List.Membership.mem_cons.mp member with rfl | member
      · exact Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.cell_error head positive (coefficients
          parent (List.mem_cons_self ..))
          (allowances parent (List.mem_cons_self ..)) (movements parent (List.mem_cons_self ..))
      · exact ih (fun other inTail => coefficients other (List.mem_cons_of_mem _ inTail))
          (fun other inTail => allowances other (List.mem_cons_of_mem _ inTail))
          (fun other inTail => movements other (List.mem_cons_of_mem _ inTail)) error member

/-- Both factors of the actual dyadic cell count are paid. The model allowance is not multiplied by a growing cell count
after this cancellation. The two remaining errors are the decaying inversion term and the explicitly displayed
coefficient/model readback term. -/
theorem dyadic_error_bound {target density allowance movement : Fraction.Rational}
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} (readings :
      Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.Readings target parents) (positive : 0 < target)
    (depth : Nat) (count : parents.length = 2 ^ depth)
    (coefficients : ∀ parent ∈ parents, Data.Gaussian.Norm.Basic.normSq parent.center.value ≤ density)
    (allowances : ∀ parent ∈ parents, parent.edge.modelErrorAllowance ≤ allowance)
    (movements : ∀ parent ∈ parents, Data.Gaussian.Norm.Basic.normSq parent.model.displacement ≤
      Geometric.Basic.quarterRadius movement depth) :
    Data.Gaussian.Norm.Basic.normSq ((PathModel.mk (parents.map
      PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample - Data.Gaussian.Norm.Sum.Basic.gaussianSum
      readings.values) ≤
      2 * density * movement * Geometric.Basic.quarterRadius movement depth +
        4 * movement * (target + (Cuts.Ambient curve).normSqBound ^ 2 * allowance) := by
  rw [← readings.errors_sum]
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le readings.errors _
    (readings.errors_bounded positive coefficients allowances movements)
  rw [readings.errors_length, count] at estimate
  apply estimate.trans_eq
  calc
    _ = (2 * density * Geometric.Basic.quarterRadius movement depth +
        4 * (target + (Cuts.Ambient curve).normSqBound ^ 2 * allowance)) *
        (((2 ^ depth : Nat) : Fraction.Rational) * (((2 ^ depth : Nat) : Fraction.Rational) *
          Geometric.Basic.quarterRadius movement depth)) := by ring1
    _ = _ := by rw [DyadicCount.dyadic_count_cancel]; ring1

end Readings

set_option genInjectivity false in
/-- Both ceilings are computed once from the actual retained centres and prepared error allowances; no caller
coefficient or model bound is needed. -/
structure Bounds (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)) where
  /-- The retained common squared-norm ceiling for the original persisted center values. -/ density : Fraction.Rational
  /-- The retained original center-density ceiling is nonnegative. -/ densityNonnegative : 0 ≤ density
  /-- The retained common ceiling for the original prepared model allowances. -/ allowance : Fraction.Rational
  /-- The retained original model-allowance ceiling is nonnegative. -/ allowanceNonnegative : 0 ≤ allowance
  /-- Every original persisted center value satisfies the retained density ceiling. -/ coefficients : ∀ parent ∈
    parents, Data.Gaussian.Norm.Basic.normSq parent.center.value ≤ density
  /-- Every original prepared model allowance satisfies the retained common ceiling. -/ allowances : ∀ parent ∈ parents,
    parent.edge.modelErrorAllowance ≤ allowance

constructive_injectivity Bounds

/-- Compute and cache common ceilings from the exact original persisted centers and model allowances. -/
def Bounds.build : (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)) →
  Bounds parents
  | [] =>
      { density := 0
        densityNonnegative := le_rfl
        allowance := 0
        allowanceNonnegative := le_rfl
        coefficients := fun _ member => by cases member
        allowances := fun _ member => by cases member }
  | parent :: remaining =>
      let tail := build remaining
      { density := max (Data.Gaussian.Norm.Basic.normSq parent.center.value) tail.density
        densityNonnegative := (Data.Gaussian.Norm.Basic.normSq_nonneg _).trans (Fraction.Order.Basic.le_max_left _ _)
        allowance := max parent.edge.modelErrorAllowance tail.allowance
        allowanceNonnegative := parent.edge.modelErrorAllowance_positive.le.trans (Fraction.Order.Basic.le_max_left _ _)
        coefficients := by
          intro other member
          rcases List.Membership.mem_cons.mp member with rfl | member
          · exact Fraction.Order.Basic.le_max_left _ _
          · exact (tail.coefficients other member).trans (Fraction.Order.Basic.le_max_right _ _)
        allowances := by
          intro other member
          rcases List.Membership.mem_cons.mp member with rfl | member
          · exact Fraction.Order.Basic.le_max_left _ _
          · exact (tail.allowances other member).trans (Fraction.Order.Basic.le_max_right _ _) }

set_option genInjectivity false in
/-- A reusable bank of actual attached-owner readings and the original source bounds used by every subsequent sum
comparison. -/
structure Bank (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)) (target :
  Fraction.Rational) where
  /-- The original reciprocal coefficient reading target is strictly positive. -/ positive : 0 < target
  /-- The cached coefficient and model-allowance ceilings of the exact original parent list. -/ bounds :
    Bounds parents
  /-- The retained owner-backed reciprocal readings for every original parent occurrence. -/ readings :
    Readings target parents

constructive_injectivity Bank

/-- Cache the original parent bounds and requested reciprocal readings in one reusable bank. -/
def Bank.build (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential))
    (boundary : ∀ parent ∈ parents, PreparedBoundarySegments.ParentOnBoundary parent (Cuts.Ambient curve))
    (target : Fraction.Rational) (positive : 0 < target) :
      Bank parents target :=
  ⟨positive, Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.Bounds.build parents,
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.Readings.build target positive parents boundary⟩

namespace Segment

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)

variable {start finish : Purelib.Data.Gaussian.Basic.Canonical} {segment :
  Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial
  (Ambient curve) start finish}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    CoveredSegment segment owner} {sheet : Fin 2}

/-- Attach the original scaled root once and retain its requested coefficient observation. -/
def acquire (cache : PreparedClearPathModels.ParentCache piece.path differential sheet) (side :
  PreparedBoundarySegments.SameSide (Cuts.Ambient curve) start finish)
    (target : Fraction.Rational) (positive : 0 < target) :
      Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.Bank cache.parents target :=
  Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.Bank.build cache.parents (fun _ member =>
    PreparedSegmentBoundaryGeometry.segment_parent_boundary cache
    (by simpa only [ClearSegment.pointAt_zero] using segment.pointAt_contains piece.within 0 (by decide))
    (by simpa only [ClearSegment.pointAt_one] using segment.pointAt_contains piece.within 1 (by decide)) side member)
    target positive

/-- Comparison with the actual original period-segment sample, not with an unrelated exact matrix or a replacement path.
The displayed model allowance still needs to be paid by the shared refinement request; this statement does not discard
it or assert reciprocal primitive/integral gluing. -/
theorem error_bound (cache : PreparedClearPathModels.ParentCache piece.path differential sheet) {target :
  Fraction.Rational}
    (bank : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples.Bank cache.parents target) :
    Data.Gaussian.Norm.Basic.normSq ((PathModel.mk (cache.parents.map
      PreparedSubdivisionModelCore.CenteredEdge.model)).integralSample - Data.Gaussian.Norm.Sum.Basic.gaussianSum
      bank.readings.values) ≤
      2 * bank.bounds.density * Data.Gaussian.Norm.Basic.normSq (finish - start) *
          Geometric.Basic.quarterRadius (Data.Gaussian.Norm.Basic.normSq (finish - start)) piece.mesh.depth +
        4 * Data.Gaussian.Norm.Basic.normSq (finish - start) * (target + (Cuts.Ambient curve).normSqBound ^ 2 *
          bank.bounds.allowance) :=
  bank.readings.dyadic_error_bound bank.positive piece.mesh.depth (PreparedSegmentBoundaryGeometry.segment_parentCount
    cache)
    bank.bounds.coefficients bank.bounds.allowances (fun parent member => by
      have movement := PreparedSegmentBoundaryGeometry.segment_parent_movement cache member
      change Data.Gaussian.Norm.Basic.normSq (parent.edge.point 1 - parent.edge.point 0) ≤ _
      rw [parent.edge.point_one, parent.edge.point_zero]
      exact movement.le)

end Segment

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalSamples
