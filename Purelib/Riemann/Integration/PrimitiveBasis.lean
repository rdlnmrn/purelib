module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.EvaluationLower
import Purelib.Riemann.Readings.PreparedObservationInterpolation

public import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Integration.PreparedNumeratorVariation
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Coefficient-uniform shared local primitives

Compute one inverse-root refinement and a structural bank of its monomial
primitives before receiving a coefficient vector.  Every vertex in the box
uses the same polynomial combination.  The increment error is homogeneous in
the squared coefficient norm, including the zero vector and arbitrarily small
nonzero vectors.  This supplies local analytic data; it does not identify the
cut-surface boundary with the global period programs.
-/

namespace Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedNumeratorVariation (basisNumerator basisNumerator_eval)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance)
open Purelib.Riemann.Normalization.InverseModelDerivativeBounds (DerivativeBounds)
open Purelib.Riemann.Normalization.InverseModelPrimitiveBounds (PrimitiveDerivativeBounds)
open Purelib.Polynomial.Geometry.EvaluationLower (coefficientPolynomial)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.LinearAlgebra

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

namespace PrimitiveBasis

/-- A structural vector of Gaussian rational coefficients. -/
abbrev Coefficients (count : Nat) := LinearAlgebra.Gaussian.Energy.GaussianVector count

set_option genInjectivity false in
/-- A numerator polynomial with its retained local primitive model.

Each entry stores the model at the same continuation patch and refinement index, allowing a structural vector to retain
the full primitive bank. -/
structure NumeratorPrimitive {polynomial : Polynomial} {siteCount : Nat}
    (patch : ContinuedNeighborhood polynomial siteCount) (index : Nat) where
  /-- The retained numerator polynomial. -/ numerator : Polynomial
  /-- The primitive model for this exact numerator, patch and index. -/ model : PrimitiveModel patch index numerator

constructive_injectivity NumeratorPrimitive

set_option genInjectivity false in
/-- A numerator polynomial with certified primitive derivative bounds.

The bounds share the supplied inverse-root derivative data and do not depend on a later refinement index. -/
structure NumeratorDerivativeBudget {polynomial : Polynomial} {box : Box}
    {clearance : RegionClearance polynomial box} {initial : Model polynomial box}
    (root : DerivativeBounds clearance initial) where
  /-- The numerator whose derivative estimates are retained. -/ numerator : Polynomial
  /-- The certified primitive derivative bounds for this numerator. -/ bounds : PrimitiveDerivativeBounds root numerator

constructive_injectivity NumeratorDerivativeBudget

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A monomial numerator bank and cached bounds prepared before choosing a refinement index.

The structural terms share one inverse-root derivative bound. Their numerator and remainder totals determine the Taylor,
reading and coefficient scales independently of a later coefficient vector. -/
structure PrimitiveBasisPreflight {polynomial : Polynomial} {siteCount : Nat}
    (patch : ContinuedNeighborhood polynomial siteCount) (count : Nat) where
  /-- Shared inverse-root derivative bounds for the patch's base model. -/ rootBounds : DerivativeBounds
    (Readings.SeededPrimitiveBounds.clearance patch.base) patch.base.model
  /-- The retained structural vector of numerator derivative budgets. -/ terms : Data.Vector
    (NumeratorDerivativeBudget rootBounds) count
  /-- Every retained numerator evaluates as its indexed monomial. -/ numerator_eq : ∀ row point, (terms
    row).numerator.eval point = point ^ row.val
  /-- The structural vector of cached numerator norm bounds. -/ numeratorBounds : Data.Vector Coordinate count
  /-- Every numerator cache equals its finite coefficient bound on the patch box. -/ numeratorBounds_eq : ∀ row,
    numeratorBounds row = Dense.Gaussian.Bounds.Box.denseEvalNormBound (terms row).numerator patch.box
  /-- The cached sum of all numerator norm bounds. -/ totalNumerator : Coordinate
  /-- The numerator total equals the finite sum of the retained bounds. -/ totalNumerator_eq : totalNumerator =
    FiniteSum.Fin.sumFin (fun row => numeratorBounds row)
  /-- The cached sum of all primitive remainder bounds. -/ totalRemainder : Coordinate
  /-- The remainder total is the sum of four times each retained derivative bound. -/ totalRemainder_eq : totalRemainder
    = FiniteSum.Fin.sumFin (fun row => 4 * (terms row).bounds.bound)
  /-- The cached coefficient-independent Taylor error scale. -/ taylorScale : Coordinate
  /-- The Taylor scale is twice the basis size times the remainder total. -/ taylorScale_eq : taylorScale = 2 * (count :
    Coordinate) * totalRemainder
  /-- The cached coefficient-independent inverse-root reading scale. -/ readingScale : Coordinate
  /-- The reading scale is twice the basis size times the numerator total and inverse-error scale. -/ readingScale_eq :
    readingScale = 2 * (count : Coordinate) * totalNumerator * patch.inverseErrorScale
  /-- The cached coefficient-reading bound per unit squared coefficient norm. -/ coefficientScale : Coordinate
  /-- The coefficient scale is the basis size times the numerator total divided by the retained positive root lower
    bound. -/ coefficientScale_eq : coefficientScale = (count : Coordinate) * totalNumerator / patch.rootLower

constructive_injectivity PrimitiveBasisPreflight

end PrimitiveBasis

namespace PrimitiveBasis.PrimitiveBasisPreflight

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
/-- Compute the monomial derivative bank and its scalar budgets once.

Retain structural vectors, exact finite totals and their defining equations for the supplied continuation patch and
basis size. -/
def build {polynomial : Polynomial} {siteCount : Nat}
    (patch : ContinuedNeighborhood polynomial siteCount) (count : Nat) : PrimitiveBasisPreflight patch count :=
  let rootBounds := (Readings.SeededPrimitiveBounds.derivativeBounds patch.base)
  let terms : Data.Vector (NumeratorDerivativeBudget rootBounds) count := Vector.Basic.vectorOfFn fun row =>
    let numerator := basisNumerator row
    ⟨numerator, PrimitiveDerivativeBounds.build rootBounds numerator⟩
  let bounds := Vector.Basic.vectorOfFn fun row => Dense.Gaussian.Bounds.Box.denseEvalNormBound (terms row).numerator
    patch.box
  let total := FiniteSum.Fin.sumFin (fun row => bounds row)
  let totalRemainder := FiniteSum.Fin.sumFin (fun row => 4 * (terms row).bounds.bound)
  let rationalCount := Rational.Budget.Aggregate.countCoordinate count
  { rootBounds := rootBounds
    terms := terms
    numerator_eq := fun row point => by rw [Vector.Basic.vectorOfFn_apply]; exact basisNumerator_eval row point
    numeratorBounds := bounds
    numeratorBounds_eq := fun row => Vector.Basic.vectorOfFn_apply _ row
    totalNumerator := total
    totalNumerator_eq := rfl
    totalRemainder := totalRemainder
    totalRemainder_eq := rfl
    taylorScale := 2 * rationalCount * totalRemainder
    taylorScale_eq := by dsimp only [rationalCount]; rw [Rational.Budget.Aggregate.countCoordinate_eq]
    readingScale := 2 * rationalCount * total * patch.inverseErrorScale
    readingScale_eq := by dsimp only [rationalCount]; rw [Rational.Budget.Aggregate.countCoordinate_eq]
    coefficientScale := rationalCount * total / patch.rootLower
    coefficientScale_eq := by dsimp only [rationalCount]; rw [Rational.Budget.Aggregate.countCoordinate_eq] }

end PrimitiveBasis.PrimitiveBasisPreflight

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A retained bank of monomial primitive models at one continuation index.

Its structural entries share the patch and index, with cached numerator bounds and exact aggregate scales that can be
reused for every coefficient vector. -/
structure PrimitiveBasis {polynomial : Polynomial} {siteCount : Nat}
    (patch : ContinuedNeighborhood polynomial siteCount) (index count : Nat) where
  /-- The retained structural vector of numerator primitive models. -/
  terms : Data.Vector (PrimitiveBasis.NumeratorPrimitive
    patch index) count
  /-- Every retained numerator evaluates as its indexed monomial. -/ numerator_eq : ∀ row point, (terms
    row).numerator.eval point = point ^ row.val
  /-- The structural vector of cached numerator norm bounds. -/ numeratorBounds : Data.Vector Coordinate count
  /-- Every numerator cache equals its finite coefficient bound on the patch box. -/ numeratorBounds_eq : ∀ row,
    numeratorBounds row =
    Dense.Gaussian.Bounds.Box.denseEvalNormBound (terms row).numerator patch.box
  /-- The cached sum of all numerator norm bounds. -/ totalNumerator : Coordinate
  /-- The numerator total equals the finite sum of the retained bounds. -/ totalNumerator_eq : totalNumerator =
    FiniteSum.Fin.sumFin (fun row => numeratorBounds row)
  /-- The cached sum of all primitive remainder bounds. -/ totalRemainder : Coordinate
  /-- The remainder total equals the finite sum of the retained per-term bounds. -/ totalRemainder_eq : totalRemainder =
    FiniteSum.Fin.sumFin (fun row => (terms row).model.primitive.remainderBound)
  /-- The cached coefficient-independent Taylor error scale. -/ taylorScale : Coordinate
  /-- The Taylor scale is twice the basis size times the remainder total. -/ taylorScale_eq : taylorScale = 2 * (count :
    Coordinate) * totalRemainder
  /-- The cached coefficient-independent inverse-root reading scale. -/ readingScale : Coordinate
  /-- The reading scale is twice the basis size times the numerator total and inverse-error scale. -/ readingScale_eq :
    readingScale = 2 * (count : Coordinate) * totalNumerator * patch.inverseErrorScale
  /-- The cached coefficient-reading bound per unit squared coefficient norm. -/ coefficientScale : Coordinate
  /-- The coefficient scale is the basis size times the numerator total divided by the retained positive root lower
    bound. -/ coefficientScale_eq : coefficientScale = (count : Coordinate) * totalNumerator / patch.rootLower

constructive_injectivity PrimitiveBasis

namespace PrimitiveBasis

variable {polynomial : Polynomial} {siteCount index count : Nat}
  {patch : ContinuedNeighborhood polynomial siteCount}

open Purelib.Algebra in
open Purelib.Data in
/-- Construct the primitive bank from cached derivative data at a selected index.

Compute the refined inverse-root model once and reuse it in every primitive entry, preserving the preflight's scalar
caches and their exact equations. -/
def ofPreflight (preflight : PrimitiveBasisPreflight patch count) (index : Nat) :
    PrimitiveBasis patch index count :=
  let rootModel := patch.base.refine index
  let terms : Data.Vector (NumeratorPrimitive patch index) count := Vector.Basic.vectorOfFn fun row =>
    { numerator := (preflight.terms row).numerator
      model := PrimitiveModel.ofBounds patch index (preflight.terms row).numerator (preflight.terms row).bounds
        rootModel rfl }
  { terms := terms
    numerator_eq := fun row point => by rw [Vector.Basic.vectorOfFn_apply]; exact preflight.numerator_eq row point
    numeratorBounds := preflight.numeratorBounds
    numeratorBounds_eq := fun row => by rw [Vector.Basic.vectorOfFn_apply]; exact preflight.numeratorBounds_eq row
    totalNumerator := preflight.totalNumerator
    totalNumerator_eq := preflight.totalNumerator_eq
    totalRemainder := preflight.totalRemainder
    totalRemainder_eq := by
      rw [preflight.totalRemainder_eq]
      apply FiniteSum.Fin.sumFin_congr
      intro row
      rw [Vector.Basic.vectorOfFn_apply]
      rfl
    taylorScale := preflight.taylorScale
    taylorScale_eq := preflight.taylorScale_eq
    readingScale := preflight.readingScale
    readingScale_eq := preflight.readingScale_eq
    coefficientScale := preflight.coefficientScale
    coefficientScale_eq := preflight.coefficientScale_eq }

/-- Prepare monomial bounds and construct their shared primitive bank at the specified index. -/
def build (patch : ContinuedNeighborhood polynomial siteCount) (index count : Nat) :
    PrimitiveBasis patch index count := ofPreflight (PrimitiveBasisPreflight.build patch count) index

/-- Constructing a basis preserves the preflight reading scale exactly. -/
theorem ofPreflight_readingScale (preflight : PrimitiveBasisPreflight patch count) (index : Nat) :
    (ofPreflight preflight index).readingScale = preflight.readingScale := rfl

/-- Constructing a basis preserves the preflight coefficient scale exactly. -/
theorem ofPreflight_coefficientScale (preflight : PrimitiveBasisPreflight patch count) (index : Nat) :
    (ofPreflight preflight index).coefficientScale = preflight.coefficientScale := rfl

/-- Constructing a basis preserves the preflight Taylor scale exactly. -/
theorem ofPreflight_taylorScale (preflight : PrimitiveBasisPreflight patch count) (index : Nat) :
    (ofPreflight preflight index).taylorScale = preflight.taylorScale := rfl

section
open Purelib.Algebra
/-- Each entry of a nonnegative finite family is at most its sum. -/
private theorem entry_le_sum {size : Nat} (values : Fin size → Coordinate)
    (nonnegative : ∀ row, 0 ≤ values row) (row : Fin size) : values row ≤ FiniteSum.Fin.sumFin values := by
  rw [← FiniteSum.Fin.sumFin_ite_eq row values]
  apply FiniteSum.Rational.Order.Positivity.sumFin_mono
  intro entry
  by_cases equal : entry = row
  · rw [if_pos equal]
  · rw [if_neg equal]
    exact nonnegative entry

/-- A finite sum of nonnegative rational entries is nonnegative. -/
private theorem sum_nonnegative {size : Nat} (values : Fin size → Coordinate)
    (nonnegative : ∀ row, 0 ≤ values row) : 0 ≤ FiniteSum.Fin.sumFin values := by
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => 0) values nonnegative
  simpa only [FiniteSum.Fin.sumFin_zero] using bound

end

open Purelib.Polynomial in
/-- Each cached numerator norm bound is nonnegative. -/
theorem numeratorBound_nonnegative (basis : PrimitiveBasis patch index count) (row : Fin count) :
    0 ≤ basis.numeratorBounds row := by
  rw [basis.numeratorBounds_eq]
  exact (Dense.Gaussian.Bounds.Box.denseHornerNormBounds_nonneg _ _).1

/-- The cached total numerator bound is nonnegative. -/
theorem totalNumerator_nonnegative (basis : PrimitiveBasis patch index count) : 0 ≤ basis.totalNumerator := by
  rw [basis.totalNumerator_eq]
  exact sum_nonnegative _ basis.numeratorBound_nonnegative

/-- The cached total primitive remainder bound is nonnegative. -/
theorem totalRemainder_nonnegative (basis : PrimitiveBasis patch index count) : 0 ≤ basis.totalRemainder := by
  rw [basis.totalRemainder_eq]
  exact sum_nonnegative _ (fun row => (basis.terms row).model.primitive.remainderBound_nonnegative)

/-- Each primitive remainder bound is at most the retained total. -/
theorem remainder_le_total (basis : PrimitiveBasis patch index count) (row : Fin count) :
    (basis.terms row).model.primitive.remainderBound ≤ basis.totalRemainder := by
  rw [basis.totalRemainder_eq]
  exact entry_le_sum _ (fun row => (basis.terms row).model.primitive.remainderBound_nonnegative) row

open Purelib.Data in
open Purelib.Polynomial in
/-- Inside the continuation box, each numerator's squared norm is bounded by the retained total. -/
theorem numerator_le_total (basis : PrimitiveBasis patch index count) (row : Fin count)
    {point : Gaussian} (inside : patch.box.Contains point) : normSq ((basis.terms row).numerator.eval point) ≤
      basis.totalNumerator := by
  have localBound := Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound (basis.terms row).numerator inside
  rw [← basis.numeratorBounds_eq, Gaussian.Norm.Basic.normSq_eq_canonical] at localBound
  rw [basis.totalNumerator_eq]
  exact localBound.trans (entry_le_sum _ basis.numeratorBound_nonnegative row)

open Purelib.Algebra in
/-- Evaluate a coefficient-weighted sum of the retained primitive polynomials.

A single coordinate determines the value, so equal coordinates reuse the same polynomial expression regardless of mesh
ownership. -/
def value (basis : PrimitiveBasis patch index count) (coefficients : Coefficients count) (point : Gaussian) : Gaussian
  :=
  FiniteSum.Fin.sumFin (fun row => coefficients row * (basis.terms row).model.primitive.value.eval point)

open Purelib.Algebra in
open Purelib.Data in
/-- Scaling all coefficients scales the shared primitive value by the same Gaussian scalar. -/
theorem value_scale (basis : PrimitiveBasis patch index count) (coefficients : Coefficients count)
    (scalar point : Gaussian) :
    basis.value (Vector.Basic.vectorOfFn fun row => scalar * coefficients row) point = scalar * basis.value coefficients
      point := by
  unfold value
  calc
    _ = FiniteSum.Fin.sumFin (fun row => scalar * (coefficients row * (basis.terms row).model.primitive.value.eval
      point)) :=
      FiniteSum.Fin.sumFin_congr (fun row => by rw [Vector.Basic.vectorOfFn_apply]; ring1)
    _ = _ := FiniteSum.Fin.sumFin_mul_left scalar _

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Polynomial in
/-- Evaluate the coefficient polynomial as the corresponding sum of retained monomial numerators. -/
theorem numerator_sum (basis : PrimitiveBasis patch index count) (coefficients : Coefficients count) (point : Gaussian)
  :
    (Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point =
      FiniteSum.Fin.sumFin (fun row => coefficients row * (basis.terms row).numerator.eval point) := by
  change Dense.Basic.DensePolynomial.evalCoeffs point (List.ofFn coefficients).reverse = _
  rw [Readings.PreparedObservationInterpolation.eval_reverse_ofFn]
  exact FiniteSum.Fin.sumFin_congr (fun row => by rw [basis.numerator_eq])

section
open Purelib.Data
/-- The finite squared coefficient norm is nonnegative. -/
theorem coefficientNorm_nonnegative (coefficients : Coefficients count) : 0 ≤ coefficientNormSq coefficients :=
  sum_nonnegative _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row))

/-- The cached coefficient scale is nonnegative. -/
theorem coefficientScale_nonnegative (basis : PrimitiveBasis patch index count) : 0 ≤ basis.coefficientScale := by
  rw [basis.coefficientScale_eq]
  exact Rat.Fraction.Order.Field.div_nonneg_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) basis.totalNumerator_nonnegative)
    patch.rootLower_positive.le

/-- The cached Taylor scale is nonnegative. -/
theorem taylorScale_nonnegative (basis : PrimitiveBasis patch index count) : 0 ≤ basis.taylorScale := by
  rw [basis.taylorScale_eq]
  exact Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))) basis.totalRemainder_nonnegative

/-- The cached reading scale is nonnegative. -/
theorem readingScale_nonnegative (basis : PrimitiveBasis patch index count) : 0 ≤ basis.readingScale := by
  rw [basis.readingScale_eq]
  exact Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))) basis.totalNumerator_nonnegative)
    patch.inverseErrorScale_positive.le

end

open Purelib.Approximation in
/-- The geometric error scale for a primitive increment between two points.

Combine the Taylor scale times squared movement squared with the geometrically refined reading scale times squared
movement; this quantity is independent of the coefficient vector. -/
def incrementScale (basis : PrimitiveBasis patch index count) (start finish : Gaussian) : Coordinate :=
  basis.taylorScale * normSq (finish - start) ^ 2 +
    Rational.Geometric.Basic.quarterRadius basis.readingScale index * normSq (finish - start)

open Purelib.Approximation in
open Purelib.Data in
/-- The geometric increment error scale is nonnegative. -/
theorem incrementScale_nonnegative (basis : PrimitiveBasis patch index count) (start finish : Gaussian) :
    0 ≤ basis.incrementScale start finish :=
  add_nonneg
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct basis.taylorScale_nonnegative
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct _))
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (Rational.Geometric.Basic.quarterRadius_nonneg basis.readingScale_nonnegative index)
        (Gaussian.Basic.Canonical.normSq_nonneg _))

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Polynomial in
/-- Bound an actual coefficient reading by squared coefficient norm times the cached coefficient scale.

The point lies in the continuation box and the root is possible in the retained process; its positive root margin
supplies the denominator bound. -/
theorem operational_coefficient_bound (basis : PrimitiveBasis patch index count) (coefficients : Coefficients count)
    {point : Gaussian} (inside : patch.box.Contains point) (sample : ContinuedNeighborhood.Point patch point)
    (state : sample.certificate.value.name.process.State) {root : Gaussian}
    (possible : sample.certificate.value.name.process.Possible state root) :
    normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point / root) ≤
      coefficientNormSq coefficients * basis.coefficientScale := by
  have rootBound := sample.candidate_lower state possible
  have rootPositive := patch.rootLower_positive.trans_le rootBound
  have rootNonzero : root ≠ 0 := by
    intro zero
    rw [zero, Gaussian.Basic.Canonical.normSq_zero] at rootPositive
    exact (lt_irrefl _ rootPositive)
  have localBounds : ∀ row : Fin count,
      normSq (coefficients row * (basis.terms row).numerator.eval point) ≤
        normSq (coefficients row) * basis.totalNumerator := by
    intro row
    rw [Gaussian.Basic.Canonical.normSq_mul]
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (basis.numerator_le_total row inside)
      (Gaussian.Basic.Canonical.normSq_nonneg _)
  have numeratorBound := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun row => coefficients row * (basis.terms row).numerator.eval point)
    (fun row => normSq (coefficients row) * basis.totalNumerator)
    (fun row => (Gaussian.Norm.Basic.normSq_eq_canonical _).le.trans (localBounds row))
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at numeratorBound
  rw [← basis.numerator_sum, FiniteSum.Fin.sumFin_mul_right] at numeratorBound
  have paid : basis.coefficientScale * patch.rootLower = (count : Coordinate) * basis.totalNumerator := by
    rw [basis.coefficientScale_eq]
    exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _ patch.rootLower_positive.ne'
  rw [Gaussian.Basic.Canonical.normSq_div _ _ rootNonzero, ← Rat.Fraction.Field.div_eq_mul_inv_direct]
  apply (Rat.Fraction.Order.Field.div_le_iff_pos rootPositive).mpr
  calc
    _ ≤ (count : Coordinate) * (coefficientNormSq coefficients * basis.totalNumerator) := numeratorBound
    _ = coefficientNormSq coefficients * (basis.coefficientScale * patch.rootLower) := by rw [paid]; ring1
    _ = (coefficientNormSq coefficients * basis.coefficientScale) * patch.rootLower := by ring1
    _ ≤ _ := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rootBound
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (coefficientNorm_nonnegative coefficients)
        basis.coefficientScale_nonnegative)

open Purelib.Algebra in
open Purelib.Polynomial in
/-- Collect coefficient-weighted primitive errors into the shared primitive increment error.

The finite identity preserves the same starting coefficient polynomial, root and endpoint displacement. -/
private theorem error_sum (basis : PrimitiveBasis patch index count) (coefficients : Coefficients count)
    (start finish root : Gaussian) :
    FiniteSum.Fin.sumFin (fun row => coefficients row * ((basis.terms row).model.primitive.value.eval finish -
      (basis.terms row).model.primitive.value.eval start -
        ((basis.terms row).numerator.eval start / root) * (finish - start))) =
      basis.value coefficients finish - basis.value coefficients start -
        ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval start / root) * (finish - start) := by
  rw [basis.numerator_sum]
  calc
    _ = FiniteSum.Fin.sumFin (fun row => coefficients row * (basis.terms row).model.primitive.value.eval finish -
          coefficients row * (basis.terms row).model.primitive.value.eval start -
            (coefficients row * (basis.terms row).numerator.eval start) * (root⁻¹ * (finish - start))) :=
      FiniteSum.Fin.sumFin_congr (fun row => by rw [Field.ExplicitField.div_eq_mul_inv]; ring1)
    _ = _ := by
      rw [FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_mul_right,
        Field.ExplicitField.div_eq_mul_inv]
      unfold value
      ring1

open Purelib.Algebra in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
/-- Bound a shared primitive increment error homogeneously in the coefficient vector.

Both endpoints lie in the continuation box, and the root is possible at the selected reading state. The squared error is
at most the squared coefficient norm times the cached Taylor and refined reading contributions. -/
theorem operational_increment_bound (basis : PrimitiveBasis patch index count) (coefficients : Coefficients count)
    {start finish : Gaussian} (startInside : patch.box.Contains start) (finishInside : patch.box.Contains finish)
    (sample : ContinuedNeighborhood.Point patch start) {root : Gaussian}
    (possible : sample.certificate.value.name.process.Possible (sample.readingState index) root) :
    normSq (basis.value coefficients finish - basis.value coefficients start -
      ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval start / root) * (finish - start)) ≤
        coefficientNormSq coefficients * (basis.taylorScale * normSq (finish - start) ^ 2 +
          Rational.Geometric.Basic.quarterRadius basis.readingScale index * normSq (finish - start)) := by
  let distance := normSq (finish - start)
  let error := Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale index
  have errorNonnegative : 0 ≤ error := Rational.Geometric.Basic.quarterRadius_nonneg patch.inverseErrorScale_positive.le
    index
  have localBounds : ∀ row : Fin count,
      normSq (coefficients row * ((basis.terms row).model.primitive.value.eval finish -
        (basis.terms row).model.primitive.value.eval start -
          ((basis.terms row).numerator.eval start / root) * (finish - start))) ≤
        normSq (coefficients row) * (2 * (basis.totalRemainder * distance ^ 2 + basis.totalNumerator * error *
          distance)) := by
    intro row
    have bound := (basis.terms row).model.operational_increment_bound startInside finishInside sample possible
    have taylor := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (basis.remainder_le_total row)
      (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct distance)
    have reading := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (basis.numerator_le_total row startInside)
        errorNonnegative)
      (Gaussian.Basic.Canonical.normSq_nonneg (finish - start))
    rw [Gaussian.Basic.Canonical.normSq_mul]
    exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (bound.trans (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add taylor reading) (by
        decide)))
      (Gaussian.Basic.Canonical.normSq_nonneg _)
  have bounded := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun row => coefficients row * ((basis.terms row).model.primitive.value.eval finish -
      (basis.terms row).model.primitive.value.eval start -
        ((basis.terms row).numerator.eval start / root) * (finish - start)))
    (fun row => normSq (coefficients row) *
      (2 * (basis.totalRemainder * distance ^ 2 + basis.totalNumerator * error * distance)))
    (fun row => (Gaussian.Norm.Basic.normSq_eq_canonical _).le.trans (localBounds row))
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at bounded
  rw [basis.error_sum, FiniteSum.Fin.sumFin_mul_right] at bounded
  apply bounded.trans_eq
  rw [basis.taylorScale_eq, basis.readingScale_eq]
  simp only [coefficientNormSq, distance, error, Rational.Geometric.Basic.quarterRadius,
    Field.ExplicitField.div_eq_mul_inv]
  ring1

end PrimitiveBasis

namespace PrimitiveBasis.PrimitiveBasisPreflight

variable {polynomial : Polynomial} {siteCount count : Nat} {patch : ContinuedNeighborhood polynomial siteCount}

/-- The preflight reading scale is nonnegative. -/
theorem readingScale_nonnegative (preflight : PrimitiveBasisPreflight patch count) : 0 ≤ preflight.readingScale :=
  (PrimitiveBasis.ofPreflight preflight 0).readingScale_nonnegative

/-- The preflight coefficient scale is nonnegative. -/
theorem coefficientScale_nonnegative (preflight : PrimitiveBasisPreflight patch count) : 0 ≤ preflight.coefficientScale
  :=
  (PrimitiveBasis.ofPreflight preflight 0).coefficientScale_nonnegative

/-- The preflight Taylor scale is nonnegative. -/
theorem taylorScale_nonnegative (preflight : PrimitiveBasisPreflight patch count) : 0 ≤ preflight.taylorScale :=
  (PrimitiveBasis.ofPreflight preflight 0).taylorScale_nonnegative

end PrimitiveBasis.PrimitiveBasisPreflight

end Purelib.Riemann.Integration
