module

public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Monomial.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Winding.Polygon.Comparison
public import Purelib.Polynomial.Winding.Polygon.Normalized
import Purelib.Polynomial.Winding.Polygon.Phase
public import Purelib.Polynomial.Winding.Polygon.Power
import Purelib.Polynomial.Winding.Polygon.Product

public import Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Nat.Coprime.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity
@[expose] public section

/-!
# Cached finite square-root traces and winding parity

Each edge retains its root norms, residual, translated polynomial, and proved
movement bound.  The canonical constructor uses exact Horner bounds; prepared
paths may reuse their existing variation bounds.  A finite exact check
constructs the local winding formulas.  A closed
chain then computes an integer root winding and proves that the polynomial
base winding is twice that integer.  Generated caches may use the same
semantic equations without reproducing the canonical coefficient calculation.

This module does not assume that coordinate labels imply operational root
closure.  Its closed input contains the actual return chord and that chord's
checked errors; acquiring this input from prepared owners is a separate task.
-/

namespace Purelib.Riemann.RootContinuation.SquareRootTrace

open Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy
  (parameterInterval chordClearance chord_nonzero chord_square_lower
    squaredChordClearance chord_product_formula segmentHomotopy)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Path

open Purelib.Geometry.Rational in
/-- The exact degenerate Gaussian box carrying the original closed unit parameter interval on the real axis. -/
def parameterBox : Box := ⟨0, 1, 0, 0, by decide, le_rfl⟩

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- Cached root displacement, residual and base-polynomial movement data for the original pair of trace endpoints.

The variation polynomial retains its exact affine-base evaluation equation, and its cached movement bound holds
throughout the original unit interval. -/
structure EdgeData (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (start finish baseStart baseFinish : Basic.Canonical) where
  /-- The cached squared norm of the original starting root. -/ rootNorm : Fraction.Rational
  /-- The cache equals the exact original starting root's squared norm. -/ rootNorm_eq : rootNorm = normSq start
  /-- The cached squared displacement between the original root endpoints. -/ distance : Fraction.Rational
  /-- The cache equals the exact original root endpoint squared difference. -/ distance_eq : distance = normSq (finish -
    start)
  /-- The cached squared residual of the original starting root against the base polynomial. -/ residual :
    Fraction.Rational
  /-- The cache equals the squared original root-square minus the original base-start evaluation. -/ residual_eq :
    residual = normSq (start ^ 2 - polynomial.eval baseStart)
  /-- The retained polynomial describing base-polynomial variation along the original affine segment. -/ variation :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  /-- The retained variation evaluates exactly to the original moving base value minus its start value. -/ variation_eq
    : ∀ time : Fraction.Rational, variation.eval (Cast.Path.ofCoordinate time) =
    polynomial.eval (Affine.line baseStart (baseFinish - baseStart) time) - polynomial.eval baseStart
  /-- The retained bound on squared base-polynomial movement along the original parameter interval. -/ movementBound :
    Fraction.Rational
  /-- Every retained unit-interval evaluation of the variation satisfies the cached movement bound. -/
    movementBound_valid : ∀ time : Fraction.Rational, parameterInterval.Contains time →
    normSq (variation.eval (Cast.Path.ofCoordinate time)) ≤ movementBound

constructive_injectivity EdgeData

namespace EdgeData

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Cache the original root norm, displacement and residual together with the normalized base variation polynomial and
exact box majorant. -/
def build (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (start finish baseStart baseFinish : Basic.Canonical) :
    EdgeData polynomial start finish baseStart baseFinish :=
  let baseValue := polynomial.eval baseStart
  let variation := (Substitution.Affine.composeLine polynomial baseStart (baseFinish - baseStart) -
    Dense.Basic.DensePolynomial.constant baseValue).normalize
  { rootNorm := normSq start
    rootNorm_eq := rfl
    distance := normSq (finish - start)
    distance_eq := rfl
    residual := normSq (start ^ 2 - baseValue)
    residual_eq := rfl
    variation := variation
    variation_eq := by
      intro time
      rw [Dense.Basic.DensePolynomial.eval_normalize, Dense.Basic.DensePolynomial.eval_sub,
        Dense.Basic.DensePolynomial.eval_constant, Substitution.Affine.eval_composeLine]
    movementBound := Bounds.Box.denseEvalNormBound variation parameterBox
    movementBound_valid := by
      intro time inside
      have scalarBound := Bounds.Box.normSq_eval_le_denseEvalNormBound variation
        (show parameterBox.Contains (Cast.Path.ofCoordinate time) from
          ⟨inside.1, inside.2, le_rfl, le_rfl⟩)
      simpa only [Norm.Basic.normSq_eq_canonical] using scalarBound }

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {start finish
  baseStart baseFinish :
  Purelib.Data.Gaussian.Basic.Canonical}

/-- The original root norm is positive and the retained displacement, residual and base movement satisfy the three
one-one-thousand-twenty-fourth thresholds. -/
def Small (data : EdgeData polynomial start finish baseStart baseFinish) : Prop :=
  0 < data.rootNorm ∧ data.distance ≤ data.rootNorm / 1024 ∧
    data.residual ≤ data.rootNorm ^ 2 / 1024 ∧ data.movementBound ≤ data.rootNorm ^ 2 / 1024

/-- Decide the retained edge's four rational smallness conditions. -/
instance (data : EdgeData polynomial start finish baseStart baseFinish) : Decidable data.Small := by
  unfold Small
  infer_instance

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
/-- The original base-polynomial movement along the affine segment is bounded by the retained variation majorant. -/
theorem movement_le (data : EdgeData polynomial start finish baseStart baseFinish)
    {time : Fraction.Rational} (inside : parameterInterval.Contains time) :
    normSq (polynomial.eval (Affine.line baseStart (baseFinish - baseStart) time) -
      polynomial.eval baseStart) ≤ data.movementBound := by
  have bound := data.movementBound_valid time inside
  rw [data.variation_eq] at bound
  exact bound

end EdgeData

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- An original root/base trace edge with retained exact data and a successful rational smallness certificate.

The original ordered fields retain the same dependent source and target indices. Equality of the retained constructor is
characterized by its original field equalities, with all caches and relation witnesses preserved. -/
structure Edge (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (start finish baseStart baseFinish : Basic.Canonical) where
  /-- The original exact root/base edge data retained by this certificate. -/ data : EdgeData polynomial start finish
    baseStart baseFinish
  /-- The retained original data satisfies the four rational smallness conditions. -/ checked : data.Small

constructive_injectivity Edge

namespace Edge

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {start finish
  baseStart baseFinish :
  Purelib.Data.Gaussian.Basic.Canonical}

/-- Check the retained edge data and return its original certified trace edge exactly when the smallness predicate
holds. -/
def ofData? (data : EdgeData polynomial start finish baseStart baseFinish) :
    Option (Edge polynomial start finish baseStart baseFinish) :=
  if checked : data.Small then some ⟨data, checked⟩ else none

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original starting root of a retained certified trace edge is nonzero. -/
theorem nonzero (edge : Edge polynomial start finish baseStart baseFinish) : start ≠ 0 := by
  intro zero
  have positive := edge.checked.1
  rw [edge.data.rootNorm_eq, zero, Basic.Canonical.normSq_zero] at positive
  exact (lt_irrefl (0 : Fraction.Rational)) positive

/-- The original endpoint displacement satisfies the retained root-norm-relative squared distance bound. -/
theorem distance (edge : Edge polynomial start finish baseStart baseFinish) :
    normSq (finish - start) ≤ normSq start / 1024 := by
  have small := edge.checked.2.1
  rw [edge.data.rootNorm_eq, edge.data.distance_eq] at small
  exact small

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- A retained certified root edge gives the exact segment homotopy formula between the square of the root coordinate
and the original base polynomial. -/
theorem homotopy (edge : Edge polynomial start finish baseStart baseFinish) :
    Winding.Polygon.Comparison.SegmentHomotopyFormula
      (Power.Coordinate.coordinatePositivePower 1) polynomial
      start finish baseStart baseFinish := by
  apply segmentHomotopy polynomial edge.nonzero edge.distance
  · have small := edge.checked.2.2.1
    rw [edge.data.rootNorm_eq, edge.data.residual_eq] at small
    exact small
  · intro time inside
    have small := edge.checked.2.2.2
    rw [edge.data.rootNorm_eq] at small
    exact (edge.data.movement_le inside).trans small

end Edge

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- An ordered pair of original root and base point lists connected by retained certified trace edges.

Each step keeps the exact previous and next points for both traces, and the tail preserves the original paired ordering.
-/
inductive Chain (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
    Basic.Canonical → List Basic.Canonical → Basic.Canonical → List Basic.Canonical → Type
  /-- The empty paired trace retains its original starting root and base point. -/ | nil (start baseStart :
    Basic.Canonical) : Chain polynomial start [] baseStart []
  /-- Prepend the retained certified edge to the exact original paired tail traces. -/ | cons {start finish baseStart
    baseFinish : Basic.Canonical}
      {roots bases : List Basic.Canonical}
      (edge : Edge polynomial start finish baseStart baseFinish)
      (tail : Chain polynomial finish roots baseFinish bases) :
      Chain polynomial start (finish :: roots) baseStart (baseFinish :: bases)

constructive_injectivity Chain

namespace Chain

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}

open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
/-- Construct the original root-coordinate phase formula along the retained certified trace chain. -/
def phase : ∀ {start baseStart : Basic.Canonical} {roots bases : List Basic.Canonical},
    Chain polynomial start roots baseStart bases →
      Winding.Polygon.Phase.ChainPhaseFormula Monomial.Coordinate.coordinatePolynomial start roots
  | _, _, [], [], .nil start _ => .nil _ start
  | _, _, _ :: _, _ :: _, .cons edge tail =>
      .consOfClearance (chordClearance edge.nonzero edge.distance) tail.phase

/-- The retained root-coordinate trace satisfies its exact coordinate-square product formula along the original chain.
-/
theorem product : ∀ {start baseStart : Basic.Canonical} {roots bases : List Basic.Canonical},
    Chain polynomial start roots baseStart bases →
      Winding.Polygon.Product.ChainProductFormula
        Monomial.Coordinate.coordinatePolynomial Monomial.Coordinate.coordinatePolynomial start roots
  | _, _, [], [], .nil start _ => .nil start
  | _, _, _ :: _, _ :: _, .cons edge tail =>
      .cons (chord_product_formula edge.nonzero edge.distance) tail.product

/-- Compose the retained edge homotopy formulas along the exact original paired root and base trace lists. -/
theorem homotopy : ∀ {start baseStart : Basic.Canonical} {roots bases : List Basic.Canonical},
    Chain polynomial start roots baseStart bases →
      Winding.Polygon.Comparison.ChainHomotopyFormula
        (Power.Coordinate.coordinatePositivePower 1) polynomial start roots baseStart bases
  | _, _, [], [], .nil start baseStart => .nil start baseStart
  | _, _, _ :: _, _ :: _, .cons edge tail => .cons edge.homotopy tail.homotopy

end Chain

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
/-- The original paired trace chain with the exact starting root and base point appended to close both lists. -/
abbrev Closed (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (start :
  Basic.Canonical) (roots : List Basic.Canonical)
    (baseStart : Basic.Canonical) (bases : List Basic.Canonical) :=
  Chain polynomial start (roots ++ [start]) baseStart (bases ++ [baseStart])

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- A normalized winding for the original root trace with the exact factor-eight equation for the base polynomial's raw
winding.

Both original closed point lists remain indices, and the retained equation expresses the square-root trace's winding
relation without replacing either trace. -/
structure WindingComparison (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (start : Basic.Canonical)
    (roots : List Basic.Canonical) (baseStart : Basic.Canonical) (bases : List Basic.Canonical) where
  /-- The retained normalized winding certificate of the exact original root trace. -/ root :
    Polynomial.Winding.Polygon.Normalized Monomial.Coordinate.coordinatePolynomial start roots
  /-- The original base polynomial raw winding equals eight times the retained root winding. -/ raw_eq :
    Winding.Polygon.Basic.closedRaw polynomial baseStart bases = 8 * root.winding

constructive_injectivity WindingComparison

namespace WindingComparison

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {start baseStart :
  Purelib.Data.Gaussian.Basic.Canonical} {roots bases : List Purelib.Data.Gaussian.Basic.Canonical}

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Construct the normalized root winding and exact base-winding comparison from the retained closed trace.

The original phase, coordinate-square product and homotopy formulas establish divisibility and the factor-eight raw
winding equation, preserving both trace lists. -/
def build (trace : Closed polynomial start roots baseStart bases) :
    WindingComparison polynomial start roots baseStart bases :=
  let raw := Winding.Polygon.Basic.closedRaw Monomial.Coordinate.coordinatePolynomial start roots
  let root : Polynomial.Winding.Polygon.Normalized Monomial.Coordinate.coordinatePolynomial start roots :=
    { winding := raw / 4
      raw_eq := by
        have divisible := (Polynomial.Winding.Polygon.Normalized.ofPhaseFormula _ _ _ trace.phase).raw_eq
        change raw = 4 * (raw / 4)
        change raw = 4 * _ at divisible
        omega }
  { root := root
    raw_eq := by
      have homotopy := Winding.Polygon.Comparison.closedRaw_eq_of_homotopy _ _ _ _ _ _ trace.homotopy
      have power := Winding.Polygon.Power.closedRaw_coordinatePositivePower start roots 1
        (.succ .zero trace.product)
      rw [homotopy, power, root.raw_eq]
      ring1 }

open Purelib.Polynomial
/-- Normalize the original base-polynomial winding as twice the retained root winding. -/
def normalizedBase (comparison : WindingComparison polynomial start roots baseStart bases) :
    Polynomial.Winding.Polygon.Normalized polynomial baseStart bases where
  winding := 2 * comparison.root.winding
  raw_eq := by rw [comparison.raw_eq]; ring1

/-- The original base-polynomial raw winding cannot be four times an odd integer when the retained closed square-root
trace exists. -/
theorem not_odd (comparison : WindingComparison polynomial start roots baseStart bases)
    (turns : Int) : Winding.Polygon.Basic.closedRaw polynomial baseStart bases ≠ 4 * (2 * turns + 1) := by
  rw [comparison.raw_eq]
  omega

end WindingComparison

end Purelib.Riemann.RootContinuation.SquareRootTrace
