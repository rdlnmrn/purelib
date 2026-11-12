module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningValues
public import Purelib.Topology.Surface.Sewing.SewingRetraction.Comparison
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Tactic.Ring

/-! # Triangle allowances for actual paired-basis reconstruction

The original source route and every coefficient-weighted basis route keep
their complete signed face corrections. Their finite bound is computed
from those exact lists before any triangle readings are requested.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_right)
open Purelib.Algebra.FiniteSum.Rational.Order (weight_sum_nonnegative)
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank ClosedCoordinates)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq normSq_mul normSq_nonneg)
open Purelib.Data.Gaussian.Norm.Sum.Indexed (normSq_sumFin_le_count_mul_sumFin)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Vector (get)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {lifted : LiftedPuncturedGrid base} {bank : BasedBranchBank lifted} {sheet : Fin 2}
    {ordered : Ordered bank sheet} {paired : Paired ordered} {prepared : Prepared paired}
    {cut : CutBank prepared} {word : List (OrientedEdge lifted.vertices.count)}
    {row : ClosedCoordinates word cut.integral} (coordinates : BasisCoordinates cut row)

/-- The actual source and basis face corrections determine their complete count-and-coefficient allowance.

Both original A/B coefficient vectors contribute their squared Gaussian
integer norms. The source route and each original basis route retain their
own correction count and signed occurrences; no physical remainder is included.
-/
@[expose] def faceResidualAllowance (bounds : Fin lifted.mesh.triangles.length → Rational) : Rational :=
  2 * (SewingRetraction.faceAllowance row.route.correction bounds +
    (genus : Rational) * sumFin (fun index : Fin genus =>
      2 * (normSq ((get coordinates.a index : Int) : Canonical) *
          SewingRetraction.faceAllowance (cut.rows.get index).a.route.correction bounds +
        normSq ((get coordinates.b index : Int) : Canonical) *
          SewingRetraction.faceAllowance (cut.rows.get index).b.route.correction bounds)))

/-- Nonnegative bounds on the same triangle bank give a nonnegative full face-residual allowance. -/
theorem faceResidualAllowance_nonnegative (bounds : Fin lifted.mesh.triangles.length → Rational)
    (nonnegative : ∀ index, 0 ≤ bounds index) : 0 ≤ coordinates.faceResidualAllowance bounds := by
  apply Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2)
  apply (Field.zero_add (0 : Rational)).symm.trans_le
  apply Order.Arithmetic.add_le_add_direct
  · exact SewingRetraction.faceAllowance_nonnegative _ bounds nonnegative
  · apply Order.Arithmetic.mul_nonneg_direct
      (Cast.Order.natCast_le_direct (m := 0) (n := genus) (Nat.zero_le genus))
    apply weight_sum_nonnegative
    intro index
    apply Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2)
    apply (Field.zero_add (0 : Rational)).symm.trans_le
    exact Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.mul_nonneg_direct (normSq_nonneg _)
        (SewingRetraction.faceAllowance_nonnegative _ bounds nonnegative))
      (Order.Arithmetic.mul_nonneg_direct (normSq_nonneg _)
        (SewingRetraction.faceAllowance_nonnegative _ bounds nonnegative))

/-- Triangle bounds pay the original source-minus-weighted-basis face residual without asserting its vanishing.

Each estimate refers to the same retained mesh and actual cochain. Finite
summation charges both cached coefficient vectors and all three kinds of
route corrections, including repeated or oppositely signed faces.
-/
theorem faceResidual_le (value : OrientedEdge lifted.vertices.count → Canonical)
    (bounds : Fin lifted.mesh.triangles.length → Rational)
    (bounded : ∀ index, normSq (SewingRetraction.wordValue value
      (lifted.mesh.triangulation.faces index).boundary) ≤ bounds index) :
    normSq (coordinates.faceResidual value) ≤ coordinates.faceResidualAllowance bounds := by
  have source := SewingRetraction.faceValue_le lifted.mesh.triangulation.faces value row.route.correction bounds bounded
  have basis := normSq_sumFin_le_count_mul_sumFin
    (fun index : Fin genus =>
      ((get coordinates.a index : Int) : Canonical) * SewingRetraction.faceValue lifted.mesh.triangulation.faces value
          (cut.rows.get index).a.route.correction +
        ((get coordinates.b index : Int) : Canonical) * SewingRetraction.faceValue lifted.mesh.triangulation.faces value
          (cut.rows.get index).b.route.correction)
    (fun index : Fin genus => 2 * (normSq ((get coordinates.a index : Int) : Canonical) *
        SewingRetraction.faceAllowance (cut.rows.get index).a.route.correction bounds +
      normSq ((get coordinates.b index : Int) : Canonical) *
        SewingRetraction.faceAllowance (cut.rows.get index).b.route.correction bounds))
    (fun index => by
      have pair := Norm.Bounds.normSq_add_le_two
        (((get coordinates.a index : Int) : Canonical) *
          SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get index).a.route.correction)
        (((get coordinates.b index : Int) : Canonical) *
          SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get index).b.route.correction)
      rewrite [normSq_mul, normSq_mul] at pair
      exact pair.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct
          (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (SewingRetraction.faceValue_le _ value _ bounds bounded) (normSq_nonneg _))
          (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (SewingRetraction.faceValue_le _ value _ bounds bounded) (normSq_nonneg _))) (by decide +kernel)))
  have difference := Norm.Bounds.normSq_sub_le_two
    (SewingRetraction.faceValue lifted.mesh.triangulation.faces value row.route.correction)
    (sumFin (fun index : Fin genus =>
      ((get coordinates.a index : Int) : Canonical) * SewingRetraction.faceValue lifted.mesh.triangulation.faces value
          (cut.rows.get index).a.route.correction +
        ((get coordinates.b index : Int) : Canonical) * SewingRetraction.faceValue lifted.mesh.triangulation.faces value
          (cut.rows.get index).b.route.correction))
  exact difference.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct source basis) (by decide +kernel))

/-- A uniform triangle allowance scales the same complete face-residual allowance linearly.

The gain depends only on the actual source and basis routes, their signed
face multiplicities and the retained A/B coefficient vectors. It is fixed
before any numerical cochain or requested triangle reading.
-/
theorem faceResidualAllowance_uniform (bound : Rational) :
    coordinates.faceResidualAllowance (fun _ => bound) =
      coordinates.faceResidualAllowance (fun _ => 1) * bound := by
  have source := SewingRetraction.faceAllowance_uniform row.route.correction bound
  have basis := (sumFin_congr (fun index : Fin genus => by
    show 2 * (normSq ((get coordinates.a index : Int) : Canonical) *
          SewingRetraction.faceAllowance (cut.rows.get index).a.route.correction (fun _ => bound) +
        normSq ((get coordinates.b index : Int) : Canonical) *
          SewingRetraction.faceAllowance (cut.rows.get index).b.route.correction (fun _ => bound)) =
      (2 * (normSq ((get coordinates.a index : Int) : Canonical) *
          SewingRetraction.faceAllowance (cut.rows.get index).a.route.correction (fun _ => 1) +
        normSq ((get coordinates.b index : Int) : Canonical) *
          SewingRetraction.faceAllowance (cut.rows.get index).b.route.correction (fun _ => 1))) * bound
    rewrite [SewingRetraction.faceAllowance_uniform (cut.rows.get index).a.route.correction bound,
      SewingRetraction.faceAllowance_uniform (cut.rows.get index).b.route.correction bound]
    ring1)).trans (sumFin_mul_right _ bound)
  change 2 * (SewingRetraction.faceAllowance row.route.correction (fun _ => bound) +
      (genus : Rational) * sumFin (fun index : Fin genus =>
        2 * (normSq ((get coordinates.a index : Int) : Canonical) *
            SewingRetraction.faceAllowance (cut.rows.get index).a.route.correction (fun _ => bound) +
          normSq ((get coordinates.b index : Int) : Canonical) *
            SewingRetraction.faceAllowance (cut.rows.get index).b.route.correction (fun _ => bound)))) =
    (2 * (SewingRetraction.faceAllowance row.route.correction (fun _ => 1) +
      (genus : Rational) * sumFin (fun index : Fin genus =>
        2 * (normSq ((get coordinates.a index : Int) : Canonical) *
            SewingRetraction.faceAllowance (cut.rows.get index).a.route.correction (fun _ => 1) +
          normSq ((get coordinates.b index : Int) : Canonical) *
            SewingRetraction.faceAllowance (cut.rows.get index).b.route.correction (fun _ => 1))))) * bound
  rewrite [source, basis]
  ring1

/-- Allocate a triangle target using the actual geometry and coefficient gain before numerical observations.

The original weighted-budget operation reserves half the requested residual
target. Its incremented denominator handles a zero gain without a separate
case or a nonvanishing assumption on the coefficients.
-/
@[expose] def faceResidualTarget (target : Rational) : Rational :=
  Weighted.allowance (target / 2) (coordinates.faceResidualAllowance (fun _ => 1))

/-- Every positive residual request gives a positive target for each original triangle reading. -/
theorem faceResidualTarget_positive {target : Rational} (positive : 0 < target) :
    0 < coordinates.faceResidualTarget target :=
  Weighted.allowance_positive (Order.Field.div_pos_direct positive (by decide +kernel))
    (coordinates.faceResidualAllowance_nonnegative (fun _ => 1) (fun _ => by decide +kernel))

/-- Meeting the allocated triangle target pays the complete actual face residual strictly within the request.

Only the triangle readings are bounded hypotheses. The complete signed
route residual and its coefficient weights are charged internally; no
physical-boundary or annular correction is discarded by this estimate.
-/
theorem faceResidual_requested_lt (value : OrientedEdge lifted.vertices.count → Canonical)
    {target : Rational} (positive : 0 < target)
    (bounded : ∀ index, normSq (SewingRetraction.wordValue value
      (lifted.mesh.triangulation.faces index).boundary) ≤ coordinates.faceResidualTarget target) :
    normSq (coordinates.faceResidual value) < target := by
  have original := (coordinates.faceResidual_le value (fun _ => coordinates.faceResidualTarget target) bounded).trans_eq
    (coordinates.faceResidualAllowance_uniform (coordinates.faceResidualTarget target))
  have paid := Weighted.mul_allowance_le
    (Order.Field.div_pos_direct positive (by decide +kernel : (0 : Rational) < 2)).le
    (coordinates.faceResidualAllowance_nonnegative (fun _ => 1) (fun _ => by decide +kernel))
  exact (original.trans paid).trans_lt (Order.Field.half_lt_self positive)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates
