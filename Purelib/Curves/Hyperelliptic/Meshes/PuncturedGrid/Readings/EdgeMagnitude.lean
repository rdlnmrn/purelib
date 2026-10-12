module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic

import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

public section

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families (Domains MagnitudeBank PrimitiveBank
  TriangleCache Source Sources Nonloop)

/-!
# Abstract magnitude bounds for a retained value vector

The ordered region comparison chain consumes exactly three consequences of a
`FaceMagnitudeBank`: the triangle increment bound, the paired source increment
bound, and the chart projection magnitude bound. This module extracts those
three bounds for an arbitrary retained value vector, with `FaceMagnitudeBank`
as the single-differential instance and the conjugate-linear combination
`conj left + coefficient * right` as the mixed instance. The region proofs can
then be replayed against a value that has no `FacePrimitiveBank` of its own.

The value API retains the selected punctured-mesh owner. Bound validity
indices and primitive sample stages remain separate parameters.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes (OrientedEdge triangleEdgeOccurrences)

open _root_.Purelib.Data.Gaussian.Basic (conj)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve}

namespace EdgeMagnitude

/-- The retained executable triangle values of this exact owner. -/
@[reducible, expose] def Values (owner : OwnedPuncturedMesh curve) :=
  Fin owner.mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3

/-- Every original retained triangle value differs from its anchor by at most the supplied squared-norm bound. -/
@[expose] def TriangleBound (owner : OwnedPuncturedMesh curve) (values : Values owner)
    (bound : Fraction.Rational) : Prop :=
  ∀ (source : Fin owner.mesh.triangles.length) (which : Fin 3),
    normSq (values source which - values source 0) ≤ bound

/-- Every original source-edge increment has squared norm at most four times the retained bound. -/
@[expose] def SourceBound (owner : OwnedPuncturedMesh curve) (values : Values owner)
    (bound : Fraction.Rational) : Prop :=
  ∀ (source : Source owner),
    normSq (source.increment values) ≤ 4 * bound

/-- The original oriented edge or its reversal occurs in the retained triangulation. -/
@[expose] def Supported (owner : OwnedPuncturedMesh curve) (edge : OrientedEdge owner.vertices.count) : Prop :=
  edge ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces ∨
    edge.reverse ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces

/-- Every supported original canonical edge valuation satisfies the retained eight-times-bound-plus-two ceiling. -/
@[expose] def ChartBound (owner : OwnedPuncturedMesh curve) (values : Values owner)
    (bound : Fraction.Rational) : Prop :=
  ∀ (edge : OrientedEdge owner.vertices.count) (_supported : Supported owner edge),
    normSq (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh values edge) ≤ 8 * bound + 2

end EdgeMagnitude

set_option genInjectivity false in
/-- The three numerical bounds used by the region comparison, stated for the
actual retained triangle values rather than for a named differential. -/
structure EdgeMagnitude (values : EdgeMagnitude.Values owner) where
  /-- The retained validity index, distinct from later primitive sample stages. -/ index : Nat
  /-- The retained common numerical magnitude ceiling. -/ bound : Fraction.Rational
  /-- The retained magnitude ceiling is nonnegative. -/ nonnegative : 0 ≤ bound
  /-- The actual original triangle values satisfy the retained anchor-increment bound. -/ triangle_bounded :
    _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude.TriangleBound owner values bound
  /-- Every original source-edge increment satisfies the retained magnitude bound. -/
  source_bounded : EdgeMagnitude.SourceBound owner
    values bound
  /-- The canonical chart valuation satisfies the retained bound on each supported original edge. -/ chart_bounded :
    _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude.ChartBound owner values bound

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity EdgeMagnitude

namespace EdgeMagnitude

/-- The conjugate-linear combination of two retained value vectors. -/
@[expose] def mixValues (leftValues rightValues : Values owner)
    (coefficient : Gaussian.Basic.Canonical) (triangle : Fin owner.mesh.triangles.length) :
      Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3 :=
  Data.Vector.Basic.vectorOfFn fun which =>
    conj (leftValues triangle which) + coefficient * rightValues triangle which

/-- Read the exact conjugate-linear combination at one original triangle coordinate. -/
theorem mixValues_apply (leftValues rightValues : Values owner)
    (coefficient : Gaussian.Basic.Canonical) (triangle : Fin owner.mesh.triangles.length) (which : Fin 3) :
    EdgeMagnitude.mixValues (owner := owner) leftValues rightValues coefficient triangle which =
      conj (leftValues triangle which) + coefficient * rightValues triangle which := by
  rw [EdgeMagnitude.mixValues.eq_1, Data.Vector.Basic.vectorOfFn_apply]

end EdgeMagnitude

namespace EdgeMagnitude

/-- The enlarged bound carried by the conjugate-linear combination. -/
@[expose] def mixBound (leftBound rightBound : Fraction.Rational) (coefficient : Gaussian.Basic.Canonical) :
  Fraction.Rational :=
  4 * (leftBound + normSq coefficient * rightBound) + 4 * normSq coefficient + 4

/-- The enlarged conjugate-linear magnitude ceiling is nonnegative when both original bounds are. -/
theorem mixBound_nonnegative {leftBound rightBound : Fraction.Rational} (left : 0 ≤ leftBound)
    (right : 0 ≤ rightBound) (coefficient : Gaussian.Basic.Canonical) :
    0 ≤ mixBound leftBound rightBound coefficient := by
  rw [mixBound]
  exact add_nonneg
    (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4)
        (add_nonneg left (Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Norm.Basic.normSq_nonneg coefficient)
          right)))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4)
        (Gaussian.Norm.Basic.normSq_nonneg coefficient)))
    (by decide : (0 : Fraction.Rational) ≤ 4)

variable {domains : Domains owner} {differential : Hyperelliptic.Differentials.Basic.Differential genus}

/-- The single-differential instance: the retained bank and its readings
provide all three bounds at the bank's own index. -/
@[expose] def ofBank (fixed : MagnitudeBank owner domains differential)
    {stage : Nat} (later : fixed.index ≤ stage)
    {data : PrimitiveBank owner differential stage domains}
    (readings : TriangleCache owner differential stage domains data) : EdgeMagnitude (owner := owner) readings.values
      where
  index := fixed.index
  bound := fixed.bound
  nonnegative := fixed.nonnegative
  triangle_bounded := fun source which => fixed.triangle_bounded later readings source which
  source_bounded := fun source => by
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests.source_increment_bounded fixed later readings
      source
  chart_bounded := fun edge supported => by
    rw [← Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute_value owner.mesh edge supported
      readings.values]
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    refine (Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests.source_increment_bounded fixed later readings
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute owner.mesh edge supported).sourceEdge).trans
        ?_
    rw [show (8 : Fraction.Rational) * fixed.bound + 2 =
      4 * fixed.bound + (4 * fixed.bound + 2) by ring1]
    exact le_add_of_nonneg_right
      (add_nonneg (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : Fraction.Rational) ≤ 4) fixed.nonnegative)
        (by decide : (0 : Fraction.Rational) ≤ 2))

/-- The sample stage does not change the bank's retained validity index. -/
theorem ofBank_index (fixed : MagnitudeBank owner domains differential)
    {stage : Nat} (later : fixed.index ≤ stage)
    {data : PrimitiveBank owner differential stage domains}
    (readings : TriangleCache owner differential stage domains data) :
    (ofBank (owner := owner) fixed later readings).index = fixed.index := rfl

/-- The single-differential magnitude retains exactly the original bank's bound. -/
theorem ofBank_bound (fixed : MagnitudeBank owner domains differential)
    {stage : Nat} (later : fixed.index ≤ stage)
    {data : PrimitiveBank owner differential stage domains}
    (readings : TriangleCache owner differential stage domains data) :
    (ofBank (owner := owner) fixed later readings).bound = fixed.bound := rfl

/-- Gaussian conjugation commutes with negation. -/
private theorem conj_neg (value : Gaussian.Basic.Canonical) : conj (-value) = -conj value := rfl

/-- Conjugation commutes with subtraction. -/
theorem conj_sub (left right : Gaussian.Basic.Canonical) : conj (left - right) = conj left - conj right := by
  rw [Gaussian.Basic.sub_eq_add_neg, Gaussian.Basic.sub_eq_add_neg, Gaussian.Basic.conj_add, conj_neg]

/-- The norm of a conjugate-linear combination. -/
theorem normSq_conj_add_mul (left right coefficient : Gaussian.Basic.Canonical) :
    normSq (conj left + coefficient * right) ≤
      2 * (normSq left + normSq coefficient * normSq right) := by
  have bound := Gaussian.Norm.Bounds.normSq_add_le_two (conj left) (coefficient * right)
  rw [Gaussian.Norm.Basic.normSq_conj, Gaussian.Norm.Basic.normSq_mul] at bound
  exact bound

/-- The conjugate-linear edge valuation of a mixed value vector. -/
theorem edgeValuation_mixValues {leftValues rightValues : Values owner}
    (coefficient : Gaussian.Basic.Canonical) {edge : OrientedEdge owner.vertices.count}
    (supported : edge ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces ∨
      edge.reverse ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces) :
    Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh (mixValues (owner := owner)
      leftValues rightValues coefficient) edge =
      conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh leftValues edge) +
        coefficient * Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh rightValues edge
          := by
  have leftValue := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute_value owner.mesh edge supported
    leftValues
  have rightValue := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute_value owner.mesh edge supported
    rightValues
  rw [← Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute_value owner.mesh edge supported (mixValues
    (owner := owner) leftValues rightValues coefficient),
    ← leftValue, ← rightValue]
  unfold Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment
  rw [mixValues_apply (owner := owner), mixValues_apply (owner := owner), conj_sub]
  ring1

/-- The conjugate-linear increment of a mixed value vector. -/
theorem source_increment_mixValues (leftValues rightValues : Values owner)
    (coefficient : Gaussian.Basic.Canonical) (source : Source owner) :
    source.increment (mixValues (owner := owner) leftValues rightValues coefficient) =
      conj (source.increment leftValues) + coefficient * source.increment rightValues := by
  unfold Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment
  rw [mixValues_apply (owner := owner), mixValues_apply (owner := owner), conj_sub]
  ring1

/-- The mixed instance: the conjugate-linear combination of two retained
values, with a bound enlarged to absorb the two chart constants. -/
@[expose] def mix {leftValues rightValues : Values owner}
    (left : EdgeMagnitude (owner := owner) leftValues) (right : EdgeMagnitude (owner := owner) rightValues)
    (coefficient : Gaussian.Basic.Canonical) :
    EdgeMagnitude (owner := owner) (mixValues (owner := owner) leftValues rightValues coefficient) where
  index := max left.index right.index
  bound := mixBound left.bound right.bound coefficient
  nonnegative := by
    have coefficientNonnegative := Gaussian.Norm.Basic.normSq_nonneg coefficient
    have first : 0 ≤ 4 * (left.bound + normSq coefficient * right.bound) :=
      Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg left.nonnegative
          (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct coefficientNonnegative right.nonnegative))
    exact add_nonneg (add_nonneg first
      (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4)
        coefficientNonnegative))
      (by decide : (0 : Fraction.Rational) ≤ 4)
  triangle_bounded := fun source which => by
    have expand : mixValues (owner := owner) (leftValues := leftValues) (rightValues := rightValues)
        coefficient source which - mixValues (owner := owner) (leftValues := leftValues)
        (rightValues := rightValues) coefficient source 0 =
        conj (leftValues source which - leftValues source 0) +
          coefficient * (rightValues source which - rightValues source 0) := by
      rw [mixValues_apply (owner := owner), mixValues_apply (owner := owner), conj_sub]
      ring1
    rw [expand]
    have estimate := normSq_conj_add_mul (leftValues source which - leftValues source 0)
      (rightValues source which - rightValues source 0) coefficient
    refine estimate.trans ?_
    have inner : normSq (leftValues source which - leftValues source 0) +
        normSq coefficient * normSq (rightValues source which - rightValues source 0) ≤
        left.bound + normSq coefficient * right.bound :=
      Purelib.Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct (left.triangle_bounded source which)
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (right.triangle_bounded source
          which)
          (Gaussian.Norm.Basic.normSq_nonneg coefficient))
    have scaled := Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inner (by
        decide : (0 : Fraction.Rational) ≤ 2)
    refine scaled.trans ?_
    rw [show mixBound left.bound right.bound coefficient =
        2 * (left.bound + normSq coefficient * right.bound) +
          (2 * (left.bound + normSq coefficient * right.bound) +
            4 * normSq coefficient + 4) by
      rw [mixBound]; ring1]
    exact le_add_of_nonneg_right (add_nonneg
      (add_nonneg
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 2)
          (add_nonneg left.nonnegative
            (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Norm.Basic.normSq_nonneg
              coefficient) right.nonnegative)))
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4)
          (Gaussian.Norm.Basic.normSq_nonneg coefficient)))
      (by decide : (0 : Fraction.Rational) ≤ 4))
  source_bounded := fun source => by
    have expand : source.increment (mixValues (owner := owner) (leftValues := leftValues)
        (rightValues := rightValues) coefficient) =
        conj (source.increment leftValues) + coefficient * source.increment rightValues := by
      unfold Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment
      rw [mixValues_apply (owner := owner), mixValues_apply (owner := owner), conj_sub]
      ring1
    rw [expand]
    have estimate := normSq_conj_add_mul (source.increment leftValues)
      (source.increment rightValues) coefficient
    refine estimate.trans ?_
    have inner : normSq (source.increment leftValues) +
        normSq coefficient * normSq (source.increment rightValues) ≤
        4 * (left.bound + normSq coefficient * right.bound) := by
      have combined := Purelib.Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct (left.source_bounded source)
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (right.source_bounded source)
          (Gaussian.Norm.Basic.normSq_nonneg coefficient))
      calc
        _ ≤ 4 * left.bound + normSq coefficient * (4 * right.bound) := combined
        _ = 4 * (left.bound + normSq coefficient * right.bound) := by ring1
    have scaled := Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inner (by
        decide : (0 : Fraction.Rational) ≤ 2)
    refine scaled.trans ?_
    rw [show 4 * mixBound left.bound right.bound coefficient =
        2 * (4 * (left.bound + normSq coefficient * right.bound)) +
          (8 * (left.bound + normSq coefficient * right.bound) +
            16 * normSq coefficient + 16) by
      rw [mixBound]; ring1]
    exact le_add_of_nonneg_right (add_nonneg
      (add_nonneg
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 8)
          (add_nonneg left.nonnegative
            (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Norm.Basic.normSq_nonneg
              coefficient) right.nonnegative)))
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 16)
          (Gaussian.Norm.Basic.normSq_nonneg coefficient)))
      (by decide : (0 : Fraction.Rational) ≤ 16))
  chart_bounded := fun edge supported => by
    have leftValue := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute_value owner.mesh edge
      supported leftValues
    have rightValue := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute_value owner.mesh edge
      supported rightValues
    have expand : Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh (mixValues (owner :=
      owner) (leftValues := leftValues)
        (rightValues := rightValues) coefficient) edge =
        conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh leftValues edge) +
          coefficient * Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh rightValues edge
            := by
      rw [← Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute_value owner.mesh edge supported
        (mixValues (owner := owner)
        (leftValues := leftValues) (rightValues := rightValues) coefficient),
        ← leftValue, ← rightValue]
      unfold Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment
      rw [mixValues_apply (owner := owner), mixValues_apply (owner := owner), conj_sub]
      ring1
    rw [expand]
    have estimate := normSq_conj_add_mul (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
      owner.mesh leftValues edge)
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh rightValues edge) coefficient
    refine estimate.trans ?_
    have inner : normSq (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh leftValues
      edge) +
        normSq coefficient * normSq (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh
          rightValues edge) ≤
        (8 * left.bound + 2) + normSq coefficient * (8 * right.bound + 2) :=
      Purelib.Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct (left.chart_bounded edge supported)
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (right.chart_bounded edge
          supported)
          (Gaussian.Norm.Basic.normSq_nonneg coefficient))
    have scaled := Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inner (by
        decide : (0 : Fraction.Rational) ≤ 2)
    refine scaled.trans ?_
    rw [show 8 * mixBound left.bound right.bound coefficient + 2 =
        2 * ((8 * left.bound + 2) + normSq coefficient * (8 * right.bound + 2)) +
          (16 * (left.bound + normSq coefficient * right.bound) +
            28 * normSq coefficient + 30) by
      rw [mixBound]; ring1]
    exact le_add_of_nonneg_right (add_nonneg
      (add_nonneg
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 16)
          (add_nonneg left.nonnegative
            (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Norm.Basic.normSq_nonneg
              coefficient) right.nonnegative)))
        (Purelib.Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 28)
          (Gaussian.Norm.Basic.normSq_nonneg coefficient)))
      (by decide +kernel : (0 : Fraction.Rational) ≤ 30))

/-- Mixing retains the maximum validity index, independently of a sample stage. -/
theorem mix_index {leftValues rightValues : Values owner}
    (left : EdgeMagnitude (owner := owner) leftValues)
    (right : EdgeMagnitude (owner := owner) rightValues) (coefficient : Gaussian.Basic.Canonical) :
    (mix (owner := owner) left right coefficient).index = max left.index right.index := rfl

/-- The mixed magnitude retains exactly the specified enlargement of both original bounds and the coefficient norm. -/
theorem mix_bound {leftValues rightValues : Values owner}
    (left : EdgeMagnitude (owner := owner) leftValues)
    (right : EdgeMagnitude (owner := owner) rightValues) (coefficient : Gaussian.Basic.Canonical) :
    (mix (owner := owner) left right coefficient).bound =
      mixBound left.bound right.bound coefficient := rfl

end EdgeMagnitude
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings
