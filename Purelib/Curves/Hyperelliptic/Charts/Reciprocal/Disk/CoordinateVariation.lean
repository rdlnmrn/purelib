module
import Purelib.Algebra.NatCast
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexArea
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
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

/-!
# Coordinate variation on the actual retained chart polygon

The reference values are cached in the same vertex records as the root
readings. Their polynomial has one uniform arc bound. Exact parameter widths
come from the original dyadic tree, independently of the primitive values.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial

open Purelib.Data.Rat

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Riemann.Normalization

public section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Reading)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Segment Path)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor index : Nat} {box :
    Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample} {stage : Nat}

namespace Reading

/-- The cached coordinate-reference value equals its retained polynomial evaluated on the reciprocal parent arc. -/
theorem coordinate_value {parameter : InverseRootPolynomial.Coordinate} (reading : VertexRequests.Reading regular model
  sample parameter target floor stage)
    (coordinate : CoordinatePolynomial sample) : reading.coordinateValue = coordinate.value.eval
      (parent.edge.point parameter)⁻¹ := by
  rw [reading.coordinate_eq, CoordinatePolynomial.eval coordinate]

/-- An accurate square-root reading retains one twentieth of the source squared-norm lower bound when the error fits the
stated clearance. -/
private theorem square_norm_lower {root point : InverseRootPolynomial.Gaussian} {lower tolerance :
  InverseRootPolynomial.Coordinate}
    (pointLower : lower ≤ Data.Gaussian.Norm.Basic.normSq point) (pointUpper :
      Data.Gaussian.Norm.Basic.normSq point ≤ 1)
    (small : tolerance ≤ 1) (paid : tolerance ≤ lower / 4)
    (accurate : Data.Gaussian.Norm.Basic.normSq (root * root - point) < tolerance) : lower / 20 ≤
      Data.Gaussian.Norm.Basic.normSq root := by
  have squareUpper : (Data.Gaussian.Norm.Basic.normSq root) ^ 2 ≤ 4 := by
    have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two (root * root - point) point).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (accurate.le.trans small) pointUpper) (by decide))
    rw [show root * root - point + point = root * root by ring1, Data.Gaussian.Norm.Basic.normSq_mul] at estimate
    exact (show (Data.Gaussian.Norm.Basic.normSq root) ^ 2 = Data.Gaussian.Norm.Basic.normSq root *
      Data.Gaussian.Norm.Basic.normSq root by ring1).trans_le
      (estimate.trans_eq (by decide))
  have rootUpper : Data.Gaussian.Norm.Basic.normSq root ≤ 5 := by
    have estimate : Data.Gaussian.Norm.Basic.normSq root ≤ 1 + (Data.Gaussian.Norm.Basic.normSq root)
      ^ 2 := by
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      exact (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct (Data.Gaussian.Norm.Basic.normSq root - 1))
        (Data.Gaussian.Norm.Basic.normSq_nonneg root)).trans_eq (by ring1)
    exact estimate.trans ((add_le_add le_rfl squareUpper).trans_eq (by decide))
  have squareLinear : Data.Gaussian.Norm.Basic.normSq (root * root) ≤ 5 *
    Data.Gaussian.Norm.Basic.normSq root := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct rootUpper (Data.Gaussian.Norm.Basic.normSq_nonneg
      root)
  have lowerEstimate : lower ≤ 2 * tolerance + 10 * Data.Gaussian.Norm.Basic.normSq root := by
    have estimate := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two (root * root) (root * root - point)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add squareLinear accurate.le) (by decide))
    rw [show root * root - (root * root - point) = point by ring1] at estimate
    exact pointLower.trans (estimate.trans_eq (by ring1))
  have readingPaid : 4 * tolerance ≤ lower :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid (by decide)).trans_eq (by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  have doubled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lowerEstimate (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
  have scaled : lower + lower ≤ 20 * Data.Gaussian.Norm.Basic.normSq root + lower := by
    exact (show lower + lower = 2 * lower by ring1).trans_le
      (doubled.trans ((show 2 * (2 * tolerance + 10 * Data.Gaussian.Norm.Basic.normSq root) = 4 * tolerance +
        20 * Data.Gaussian.Norm.Basic.normSq root by ring1).trans_le
        ((add_le_add readingPaid le_rfl).trans_eq (by ring1))))
  apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : InverseRootPolynomial.Coordinate) < 20)).mpr
  exact (Fraction.Order.Arithmetic.le_of_add_le_add_right_direct scaled).trans_eq (by ring1)

/-- Clearance of the actual source boundary gives a lower bound for the same finite coordinate reading retained by the
vertex. -/
theorem coordinate_norm_lower {parameter : InverseRootPolynomial.Coordinate}
    (reading : VertexRequests.Reading regular model sample parameter target floor stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (small : target ≤ 1) (paid : target ≤ collar.coordinateBound / 4) :
    collar.coordinateBound / 20 ≤ Data.Gaussian.Norm.Basic.normSq reading.root.coordinate := by
  have boundary := data.boundary.point
    ⟨edge.left.inside.1.trans reading.prepared.inside.1, reading.prepared.inside.2.trans edge.right.inside.2⟩
  have lower := (collar.point_clearance boundary
    (show 0 ≤ (0 : InverseRootPolynomial.Coordinate) ∧ (0 : InverseRootPolynomial.Coordinate) ≤ 1 from ⟨le_rfl, by
      decide⟩)).1
  rw [collar.point_eq, ReciprocalExteriorCollar.deform_zero] at lower
  have accurate := reading.square
  rw [branch, pow_one] at accurate
  exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation.Reading.square_norm_lower lower
    (Reciprocal.Bounds.disk_unit_bound (ReciprocalExteriorCollar.inverse_inDisk curve boundary)) small paid accurate

end Reading

namespace Segment

/-- A displacement smaller in squared norm than its first point forces a positive real dot product. -/
private theorem dot_positive_of_step {first last : InverseRootPolynomial.Gaussian}
    (step : Data.Gaussian.Norm.Basic.normSq (last - first) < Data.Gaussian.Norm.Basic.normSq first) :
      0 < first.re * last.re + first.im * last.im := by
  have positive : 0 < 2 * (first.re * last.re + first.im * last.im) := by
    have difference := Fraction.Order.Arithmetic.sub_pos_direct step
    have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct difference
      (Data.Gaussian.Norm.Basic.normSq last)
    rw [Fraction.Field.zero_add] at shifted
    exact ((Data.Gaussian.Norm.Basic.normSq_nonneg last).trans_lt shifted).trans_eq (by
      simp only [Data.Gaussian.Norm.Basic.normSq, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im];
        ring1)
  have divided := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
  exact divided.trans_eq (by
    rw [Fraction.Field.mul_comm]
    change (_ * 2) * (2 : InverseRootPolynomial.Coordinate)⁻¹ = _
    rw [Fraction.Field.mul_assoc, show (2 : InverseRootPolynomial.Coordinate) * 2⁻¹ = 1 by decide,
      Fraction.Field.mul_one_direct])

/-- A step smaller than the source clearance cannot switch to the opposite root. This concerns the root coordinate
itself, independently of F. -/
theorem coordinate_dot_positive (segment : VertexPaths.Segment regular model sample target floor stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (small : target ≤ 1) (paid : target ≤ collar.coordinateBound / 4)
    (step : Data.Gaussian.Norm.Basic.normSq (segment.last.root.coordinate - segment.first.root.coordinate) <
      collar.coordinateBound / 20) :
    0 < segment.first.root.coordinate.re * segment.last.root.coordinate.re +
      segment.first.root.coordinate.im * segment.last.root.coordinate.im :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation.Segment.dot_positive_of_step (step.trans_le
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation.Reading.coordinate_norm_lower segment.first branch
    small paid))

/-- The actual root-coordinate step is bounded by the retained reference-polynomial variation and both endpoint errors.
-/
theorem coordinate_increment_bound (segment : VertexPaths.Segment regular model sample target floor stage)
    (bounds : CoordinatePolynomial.CoordinateBounds comparison) (coordinate : CoordinatePolynomial
      sample)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq (segment.last.root.coordinate - segment.first.root.coordinate) <
      2 * (bounds.slope * (segment.lastParameter - segment.firstParameter) ^ 2 + 4 * target) := by
  let reference := segment.last.coordinateValue - segment.first.coordinateValue
  let actual := segment.last.root.coordinate - segment.first.root.coordinate
  have error : Data.Gaussian.Norm.Basic.normSq (reference - actual) < 4 * target := by
    rw [show reference - actual = (segment.last.coordinateValue - segment.last.root.coordinate) -
      (segment.first.coordinateValue - segment.first.root.coordinate) by dsimp only [reference, actual]; ring1]
    exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
      ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct segment.last.coordinate_accurate
          segment.first.coordinate_accurate)).trans_eq (by ring1))
  have bounded : Data.Gaussian.Norm.Basic.normSq reference ≤ bounds.slope * (segment.lastParameter -
    segment.firstParameter) ^ 2 := by
    dsimp only [reference]
    rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation.Reading.coordinate_value segment.last
      coordinate, Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation.Reading.coordinate_value segment.first
      coordinate]
    exact CoordinateBounds.increment_bound bounds coordinate branch segment.first.prepared.inside
      segment.last.prepared.inside
  change Data.Gaussian.Norm.Basic.normSq actual < _
  rw [show actual = reference - (reference - actual) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      ((add_le_add bounded le_rfl).trans_lt (Fraction.Order.Arithmetic.add_lt_add_left_direct error _)))

end Segment

namespace Path

/-- The squared dyadic segment count cancels its quarter-radius width factor.

Each successor doubles the segment count and multiplies the width factor by one
quarter. The owned natural cast law transports this exact scalar identity. -/
private theorem count_quarter (depth : Nat) : (((2 ^ depth : Nat) : InverseRootPolynomial.Coordinate) ^ 2) *
  Geometric.Basic.quarterRadius 1 depth = 1 := by
  induction depth with
  | zero =>
    rw [Geometric.Basic.quarterRadius_eq_mul_pow]; change (1 : InverseRootPolynomial.Coordinate) ^ 2 * (1 * 1) = 1;
      ring1
  | succ depth ih =>
      rw [Nat.pow_succ, Algebra.NatCast.mul, Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ]
      rw [Geometric.Basic.quarterRadius_eq_mul_pow] at ih
      calc
        _ = ((((2 ^ depth : Nat) : InverseRootPolynomial.Coordinate) ^ 2) * (1 * (1 / 4 :
          InverseRootPolynomial.Coordinate) ^ depth)) * (4 * (1 / 4)) := by
          ring1
        _ = _ := by rw [ih, show (4 : InverseRootPolynomial.Coordinate) * (1 / 4) = 1 by decide]; ring1

variable {depth : Nat} {first last : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {before : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Reading regular model sample first target
    floor stage}
  {after : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Reading regular model sample last target
    floor stage}

/-- Each actual retained segment's squared width is the whole interval's squared width times the dyadic quarter factor.
-/
theorem width_square (path : VertexPaths.Path regular model sample target floor stage depth before after)
    (segment : VertexPaths.Segment regular model sample target floor stage) (member : segment ∈ path.segments) :
    (segment.lastParameter - segment.firstParameter) ^ 2 = Geometric.Basic.quarterRadius 1 depth * (last - first) ^ 2 :=
      by
  have nonzero : (((2 ^ depth : Nat) : InverseRootPolynomial.Coordinate) ^ 2) ≠ 0 := by
    intro zero
    have paid := Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation.Path.count_quarter depth
    rw [zero, Fraction.Field.zero_mul_direct] at paid
    exact (by decide : (0 : InverseRootPolynomial.Coordinate) ≠ 1) paid
  apply Fraction.Field.mul_right_cancel_of_ne nonzero
  calc
    _ = ((((2 ^ depth : Nat) : InverseRootPolynomial.Coordinate) * (segment.lastParameter - segment.firstParameter))) ^
      2 := by
      ring1
    _ = (last - first) ^ 2 := by rw [path.width_eq segment member]
    _ = _ := by
      rw [show Geometric.Basic.quarterRadius 1 depth * (last - first) ^ 2 * (((2 ^ depth : Nat) :
        InverseRootPolynomial.Coordinate) ^ 2) =
        ((((2 ^ depth : Nat) : InverseRootPolynomial.Coordinate) ^ 2) * Geometric.Basic.quarterRadius 1 depth) * (last -
          first) ^ 2 by ring1, Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation.Path.count_quarter]
      exact (Fraction.Field.one_mul _).symm

/-- Every actual retained polygon segment satisfies the same depth-dependent coordinate-step bound, using its exact
dyadic width. -/
theorem coordinate_increment_bound (path : VertexPaths.Path regular model sample target floor stage depth before after)
    (bounds : CoordinatePolynomial.CoordinateBounds comparison) (coordinate : CoordinatePolynomial
      sample)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (segment : VertexPaths.Segment regular model sample target floor stage) (member : segment ∈ path.segments) :
    Data.Gaussian.Norm.Basic.normSq (segment.last.root.coordinate - segment.first.root.coordinate) <
      2 * (Geometric.Basic.quarterRadius bounds.slope depth * (last - first) ^ 2 + 4 * target) := by
  have estimate := Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation.Segment.coordinate_increment_bound
    segment bounds coordinate branch
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation.Path.width_square path segment member] at estimate
  exact estimate.trans_eq (by simp only [Geometric.Basic.quarterRadius_eq_mul_pow]; ring1)

end Path
end

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation
