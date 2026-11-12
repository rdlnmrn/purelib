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
import Purelib.Data.Gaussian.Norm.SquareResidual
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
structure EdgeData (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
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
    Basic.CanonicalCoefficients.CoefficientPolynomial
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

open Purelib.Geometry.Rational

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The normalized original polynomial variation along an exact affine base segment. -/
def baseVariation (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (baseStart baseFinish : Basic.Canonical) : Basic.CanonicalCoefficients.CoefficientPolynomial :=
  (Substitution.Affine.composeLine polynomial baseStart (baseFinish - baseStart) -
    constant (polynomial.eval baseStart)).normalize

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The original normalized variation evaluates to the exact moving polynomial value minus its retained start. -/
theorem baseVariation_eval (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (baseStart baseFinish : Data.Gaussian.Basic.Canonical) (time : Fraction.Rational) :
    (baseVariation polynomial baseStart baseFinish).eval (Cast.Path.ofCoordinate time) =
      polynomial.eval (Affine.line baseStart (baseFinish - baseStart) time) - polynomial.eval baseStart := by
  unfold baseVariation
  rw [eval_normalize, eval_sub, eval_constant, Substitution.Affine.eval_composeLine]

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Retain one actual variation cache and its certified movement budget in the original trace-edge data.

The original root endpoints and base endpoints stay as indices. A supplied
whole-interval bound can come from the canonical coefficient fold or an
independently retained geometric polynomial bound; the same exact variation
and all scalar caches are stored once.
-/
def ofVariation (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (start finish baseStart baseFinish : Basic.Canonical)
    (variation : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (variation_eq : ∀ time : Data.Rat.Fraction.Rational,
      variation.eval (Cast.Path.ofCoordinate time) =
        polynomial.eval (Affine.line baseStart (baseFinish - baseStart) time) - polynomial.eval baseStart)
    (movementBound : Data.Rat.Fraction.Rational)
    (movementBound_valid : ∀ time : Data.Rat.Fraction.Rational, parameterInterval.Contains time →
      normSq (variation.eval (Cast.Path.ofCoordinate time)) ≤ movementBound) :
    EdgeData polynomial start finish baseStart baseFinish :=
  { rootNorm := normSq start
    rootNorm_eq := rfl
    distance := normSq (finish - start)
    distance_eq := rfl
    residual := normSq (start ^ 2 - polynomial.eval baseStart)
    residual_eq := rfl
    variation := variation
    variation_eq := variation_eq
    movementBound := movementBound
    movementBound_valid := movementBound_valid }

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Retain the original base-variation cache while consuming new actual root-reading scalar caches.

The polynomial, both base endpoints, complete variation and movement budget
remain the original data. Only the two root endpoints change; the supplied
norm/residual caches are consumed directly, and their new pair distance is
computed once.
-/
def withRootCaches
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {start finish baseStart baseFinish : Basic.Canonical}
    (data : EdgeData polynomial start finish baseStart baseFinish)
    (first last : Basic.Canonical) (firstNorm : Fraction.Rational)
    (firstNorm_eq : firstNorm = normSq first) (firstResidual : Fraction.Rational)
    (firstResidual_eq : firstResidual = normSq (first ^ 2 - polynomial.eval baseStart)) :
    EdgeData polynomial first last baseStart baseFinish where
  rootNorm := firstNorm
  rootNorm_eq := firstNorm_eq
  distance := normSq (last - first)
  distance_eq := rfl
  residual := firstResidual
  residual_eq := firstResidual_eq
  variation := data.variation
  variation_eq := data.variation_eq
  movementBound := data.movementBound
  movementBound_valid := data.movementBound_valid

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Cache the original root norm, displacement and residual with the normalized variation and exact box majorant. -/
def build (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (start finish baseStart baseFinish : Basic.Canonical) :
    EdgeData polynomial start finish baseStart baseFinish :=
  let variation := EdgeData.baseVariation polynomial baseStart baseFinish
  ofVariation polynomial start finish baseStart baseFinish variation
    (EdgeData.baseVariation_eval polynomial baseStart baseFinish)
    (Bounds.Box.denseEvalNormBound variation parameterBox) (by
      intro time inside
      have scalarBound := Bounds.Box.normSq_eval_le_denseEvalNormBound variation
        (show parameterBox.Contains (Cast.Path.ofCoordinate time) from
          ⟨inside.1, inside.2, le_rfl, le_rfl⟩)
      simpa only [Norm.Basic.normSq_eq_canonical] using scalarBound)

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {start finish
  baseStart baseFinish :
  Data.Gaussian.Basic.Canonical}

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
structure Edge (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (start finish baseStart baseFinish : Basic.Canonical) where
  /-- The original exact root/base edge data retained by this certificate. -/ data : EdgeData polynomial start finish
    baseStart baseFinish
  /-- The retained original data satisfies the four rational smallness conditions. -/ checked : data.Small

constructive_injectivity Edge

namespace Edge

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {start finish
  baseStart baseFinish :
  Data.Gaussian.Basic.Canonical}

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
  rw [edge.data.rootNorm_eq, zero, normSq_zero] at positive
  exact (lt_irrefl (0 : Fraction.Rational)) positive

/-- The original endpoint displacement satisfies the retained root-norm-relative squared distance bound. -/
theorem distance (edge : Edge polynomial start finish baseStart baseFinish) :
    normSq (finish - start) ≤ normSq start / 1024 := by
  have small := edge.checked.2.1
  rw [edge.data.rootNorm_eq, edge.data.distance_eq] at small
  exact small

/-- The original first root's square residual satisfies the retained root-norm-relative budget. -/
theorem residual (edge : Edge polynomial start finish baseStart baseFinish) :
    normSq (start ^ 2 - polynomial.eval baseStart) ≤ normSq start ^ 2 / 1024 := by
  have small := edge.checked.2.2.1
  rewrite [edge.data.rootNorm_eq, edge.data.residual_eq] at small
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
  · exact edge.residual
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
inductive Chain (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) :
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
open Purelib.Geometry.Rational
open Purelib.Data.Rat

/-- The actual terminal root of a short trace remains near one retained original reference reading.

All actual base vertices have their own radicand-movement payment. The
original Edge caches supply every intermediate root displacement and square
residual; only the actual last reading's residual is separate. Induction
keeps the same reference value and its squared norm throughout the trace.
-/
theorem terminal_near_reference {reference referenceParameter : Basic.Canonical}
    (positive : 0 < normSq reference)
    (referenceResidual : normSq (reference * reference - referenceParameter) ≤ normSq reference ^ 2 / 1024) :
    ∀ {start baseStart : Basic.Canonical} {roots bases : List Basic.Canonical}
      (_trace : Chain polynomial start roots baseStart bases),
      normSq (start - reference) ≤ normSq reference / 16 →
      (∀ point ∈ bases, normSq (referenceParameter - polynomial.eval point) ≤ normSq reference ^ 2 / 1024) →
      normSq ((Polygon.Chain.terminal start roots) ^ 2 -
        polynomial.eval (Polygon.Chain.terminal baseStart bases)) ≤
          normSq (Polygon.Chain.terminal start roots) ^ 2 / 1024 →
      normSq (Polygon.Chain.terminal start roots - reference) ≤ normSq reference / 16 := by
  intro start baseStart roots bases trace
  induction trace with
  | nil start baseStart =>
      intro near _ _
      exact near
  | @cons start finish baseStart baseFinish roots bases edge tail inductionHypothesis =>
      intro near movement lastResidual
      have nextResidual : normSq (finish * finish - polynomial.eval baseFinish) ≤ normSq finish ^ 2 / 1024 := by
        cases tail with
        | nil => simpa only [Polygon.Chain.terminal, pow_two] using lastResidual
        | cons nextEdge rest => simpa only [pow_two] using nextEdge.residual
      have nearQuarter : normSq (start - reference) ≤ normSq reference / 4 := near.trans (by
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide +kernel) positive.le)
      have nextNear := Norm.SquareResidual.near_of_short_step
        positive nearQuarter edge.distance referenceResidual nextResidual
        (movement baseFinish (List.Mem.head _))
      exact inductionHypothesis nextNear
        (fun point member => movement point (List.Mem.tail baseFinish member)) lastResidual

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
abbrev Closed (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (start :
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
structure WindingComparison (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial)
  (start : Basic.Canonical)
    (roots : List Basic.Canonical) (baseStart : Basic.Canonical) (bases : List Basic.Canonical) where
  /-- The retained normalized winding certificate of the exact original root trace. -/ root :
    Winding.Polygon.Normalized Monomial.Coordinate.coordinatePolynomial start roots
  /-- The original base polynomial raw winding equals eight times the retained root winding. -/ raw_eq :
    Winding.Polygon.Basic.closedRaw polynomial baseStart bases = 8 * root.winding

constructive_injectivity WindingComparison

namespace WindingComparison

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {start baseStart :
  Data.Gaussian.Basic.Canonical} {roots bases : List Data.Gaussian.Basic.Canonical}

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Construct the normalized root winding and exact base-winding comparison from the retained closed trace.

The original phase, coordinate-square product and homotopy formulas establish divisibility and the factor-eight raw
winding equation, preserving both trace lists. -/
def build (trace : Closed polynomial start roots baseStart bases) :
    WindingComparison polynomial start roots baseStart bases :=
  let raw := Winding.Polygon.Basic.closedRaw Monomial.Coordinate.coordinatePolynomial start roots
  let root : Winding.Polygon.Normalized Monomial.Coordinate.coordinatePolynomial start roots :=
    { winding := raw / 4
      raw_eq := by
        have divisible := (Winding.Polygon.Normalized.ofPhaseFormula _ _ _ trace.phase).raw_eq
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
    Winding.Polygon.Normalized polynomial baseStart bases where
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
