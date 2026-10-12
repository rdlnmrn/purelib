module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.NatCast
import Purelib.Algebra.Field.ExplicitField
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Geometry.EvaluationLower

public import Purelib.Riemann.Readings.PrimitiveTriangleEnergy
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Integration.PrimitiveBasis
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

@[expose] public section

/-!
# Nested accuracy selection for primitive surface meshes

Choose a coefficient-independent surface tolerance. The cached preflight
Taylor ceiling fixes the spatial depth independently of the inverse-root
index. The final per-face allowance pays the actual `2 * 4^depth` triangles;
neither selection needs to inspect the refined primitive coefficients.
-/

namespace Purelib.Riemann.Topology

namespace PrimitiveSurfaceBudget

open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained surface error budgets. -/
private abbrev Coordinate := Fraction.Rational

end PrimitiveSurfaceBudget

open Purelib.Riemann.Readings.PrimitiveTriangleEnergy
    (TriangleProductBudget)
open _root_.Purelib.Riemann.Integration (PrimitiveBasis)
open _root_.Purelib.Riemann.Integration.PrimitiveBasis (PrimitiveBasisPreflight Coefficients)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial
    (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical

namespace PrimitiveSurfaceBudget

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A positive tolerance at most one that pays the original coefficient-and-diameter target.

The retained inequality bounds twice the diameter times the coefficient factor times the exact tolerance by the
requested positive target. -/
structure SurfaceTolerance (coefficientScale diameter target : Fraction.Rational) where
  /-- The retained positive geometric tolerance for the original surface target. -/ epsilon : Fraction.Rational
  /-- The exact retained tolerance is strictly positive. -/ positive : 0 < epsilon
  /-- The retained tolerance is at most one. -/ le_one : epsilon ≤ 1
  /-- The original coefficient-and-diameter scale times this tolerance is below the target. -/ accurate : 2 * diameter *
    (2 * coefficientScale + 3) * epsilon < target

constructive_injectivity SurfaceTolerance

end PrimitiveSurfaceBudget

namespace PrimitiveSurfaceBudget.SurfaceTolerance

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Find a geometric quarter tolerance paying the original finite surface target.

The explicit search uses the exact coefficient and diameter scale plus one, retaining positivity, the unit bound and the
strict target payment. -/
def build (coefficientScale diameter target : Fraction.Rational)
    (coefficientNonnegative : 0 ≤ coefficientScale) (diameterNonnegative : 0 ≤ diameter) (targetPositive : 0 < target) :
    SurfaceTolerance coefficientScale diameter target := by
  let scale := 2 * diameter * (2 * coefficientScale + 3)
  have scaleNonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) diameterNonnegative)
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) coefficientNonnegative) (by decide))
  have denominatorPositive : 0 < scale + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct scaleNonnegative
    (by decide)
  let threshold := target / (scale + 1)
  have thresholdPositive : 0 < threshold := Fraction.Order.Field.div_pos_direct targetPositive denominatorPositive
  let index := Geometric.Search.firstQuarterBelow 1 0 threshold
  let epsilon := Geometric.Basic.quarterRadius 1 index
  have positive : 0 < epsilon := Geometric.Basic.quarterRadius_pos (by decide) index
  have accurate : epsilon < threshold := Geometric.Search.firstQuarterBelow_accurate 1 (by decide) 0 threshold
    thresholdPositive
  have paid : epsilon * (scale + 1) < target := (Fraction.Order.Field.lt_div_iff_pos denominatorPositive).mp accurate
  exact
    { epsilon := epsilon
      positive := positive
      le_one := Geometric.Basic.quarterRadius_le_scale (by decide) index
      accurate := by
        calc
          scale * epsilon ≤ (scale + 1) * epsilon :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
              calc
                scale = scale + 0 := by ring1
                _ ≤ scale + 1 := Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl scale) (by
                  decide)) positive.le
          _ = epsilon * (scale + 1) := by ring1
          _ < target := paid }

end PrimitiveSurfaceBudget.SurfaceTolerance

namespace PrimitiveSurfaceBudget.TriangleProductBudget

open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
/-- Construct the two equal cross budgets and mixed budget from one original uniform tolerance and distance.

Nonnegative coefficient and distance bounds and a tolerance between zero and one certify the exact two affine and two
increment-error scales. -/
def uniform (coefficient epsilon distance : Fraction.Rational) (coefficientNonnegative : 0 ≤ coefficient)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonLe : epsilon ≤ 1) (distanceNonnegative : 0 ≤ distance) :
    PrimitiveTriangleEnergy.TriangleProductBudget (coefficient * distance) (coefficient * distance)
      (2 * epsilon ^ 2 * distance) (2 * epsilon ^ 2 * distance) where
  first := epsilon * distance * (coefficient + 1)
  second := epsilon * distance * (coefficient + 1)
  mixed := epsilon * distance
  first_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct epsilonNonnegative distanceNonnegative) (add_nonneg
      coefficientNonnegative (by decide))
  second_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct epsilonNonnegative distanceNonnegative) (add_nonneg
      coefficientNonnegative (by decide))
  mixed_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct epsilonNonnegative distanceNonnegative
  first_bound := PrimitiveTriangleEnergy.TriangleProductBudget.uniform_cross coefficientNonnegative
  second_bound := by
    rw [Fraction.Field.mul_comm (coefficient * distance)]
    exact PrimitiveTriangleEnergy.TriangleProductBudget.uniform_cross coefficientNonnegative
  mixed_bound := by
    have squareLe : epsilon ^ 2 ≤ 1 := by
      simpa only [one_pow] using Fraction.Order.Arithmetic.pow_le_pow_direct epsilonNonnegative epsilonLe 2
    have fourthLe : epsilon ^ 2 * epsilon ^ 2 ≤ epsilon ^ 2 := by
      simpa only [Fraction.Field.mul_one_direct] using
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe (Fraction.Order.Arithmetic.sq_nonneg_direct
          epsilon)
    apply (Fraction.Order.Field.div_le_iff_pos (by decide)).mpr
    calc
      _ = (epsilon ^ 2 * epsilon ^ 2) * (4 * distance ^ 2) := by ring1
      _ ≤ epsilon ^ 2 * (4 * distance ^ 2) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct fourthLe
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct distance))
      _ = _ := by ring1

end PrimitiveSurfaceBudget.TriangleProductBudget

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
set_option genInjectivity false in
/-- A retained primitive basis with paid reading accuracy, subdivision depth and uniform face budgets.

The original preflight fixes coefficient, reading and Taylor scales. Separate searches retain the reading index and leaf
diameter, with certificates paying both errors and the original total surface target. -/
structure PrimitiveSurfaceBudget {polynomial : Polynomial} {siteCount count : Nat}
    {patch : ContinuedNeighborhood polynomial siteCount} (preflight : PrimitiveBasisPreflight patch count)
    (diameter target : Fraction.Rational) where
  /-- The original squared-diameter allowance is nonnegative. -/ diameter_nonnegative : 0 ≤ diameter
  /-- The requested original surface target is strictly positive. -/ target_positive : 0 < target
  /-- The retained tolerance indexed by the original preflight coefficient scale, diameter and target. -/ tolerance :
    _root_.Purelib.Riemann.Topology.PrimitiveSurfaceBudget.SurfaceTolerance preflight.coefficientScale diameter target
  /-- The retained primitive reading refinement index. -/ index : Nat
  /-- The exact primitive basis at this original patch and retained reading index. -/ basis : PrimitiveBasis patch index
    count
  /-- The basis retains the exact original preflight coefficient scale. -/ coefficientScale_eq : basis.coefficientScale
    = preflight.coefficientScale
  /-- The basis retains the exact original preflight reading scale. -/ readingScale_eq : basis.readingScale =
    preflight.readingScale
  /-- The basis retains the exact original preflight Taylor scale. -/ taylorScale_eq : basis.taylorScale =
    preflight.taylorScale
  /-- The retained reading allowance is at most the exact tolerance squared. -/ reading_small :
    Geometric.Basic.quarterRadius basis.readingScale index ≤ tolerance.epsilon ^ 2
  /-- The retained geometric subdivision depth. -/ depth : Nat
  /-- The cached original diameter after its geometric quarter refinement. -/ leafDiameter : Fraction.Rational
  /-- The leaf diameter is exactly the original diameter's quarter radius at the retained depth. -/ leafDiameter_eq :
    leafDiameter = Geometric.Basic.quarterRadius diameter depth
  /-- The retained Taylor scale times that exact leaf diameter is at most tolerance squared. -/ taylor_small :
    basis.taylorScale * leafDiameter ≤ tolerance.epsilon ^ 2
  /-- The uniform product budgets indexed by the exact original coefficient, tolerance and leaf diameter. -/ products :
    PrimitiveTriangleEnergy.TriangleProductBudget (preflight.coefficientScale * leafDiameter)
    (preflight.coefficientScale * leafDiameter)
    (2 * tolerance.epsilon ^ 2 * leafDiameter) (2 * tolerance.epsilon ^ 2 * leafDiameter)
  /-- The cached sum of the original uniform face product budgets. -/ faceBudget : Fraction.Rational
  /-- The face budget is exactly its first, second and mixed retained product sum. -/ faceBudget_eq : faceBudget =
    products.first + products.second + products.mixed
  /-- The original face budget is paid by the retained tolerance, leaf diameter and coefficient factor. -/ faceBudget_le
    : faceBudget ≤ tolerance.epsilon * leafDiameter * (2 * preflight.coefficientScale + 3)

constructive_injectivity PrimitiveSurfaceBudget

namespace PrimitiveSurfaceBudget

variable {polynomial : Polynomial} {siteCount count : Nat} {patch : ContinuedNeighborhood polynomial siteCount}
  {preflight : PrimitiveBasisPreflight patch count} {diameter target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Multiplying a geometric quarter radius by a scale equals the quarter radius of the scaled original diameter. -/
private theorem quarterRadius_mul (scale diameter : Fraction.Rational) (depth : Nat) :
    scale * Geometric.Basic.quarterRadius diameter depth = Geometric.Basic.quarterRadius (scale * diameter) depth := by
  simp only [Geometric.Basic.quarterRadius, Field.ExplicitField.div_eq_mul_inv]
  ring1

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Acquire the original primitive basis and uniform surface budget by explicit finite geometric searches.

The positive target fixes one tolerance; independent reading and Taylor searches produce a retained index and depth.
Product and face budgets use those exact cached scales and leaf diameter. -/
def acquire (preflight : PrimitiveBasisPreflight patch count) (diameter target : Fraction.Rational)
    (diameterNonnegative : 0 ≤ diameter) (targetPositive : 0 < target) :
    PrimitiveSurfaceBudget preflight diameter target :=
  let tolerance := SurfaceTolerance.build preflight.coefficientScale diameter target
    preflight.coefficientScale_nonnegative diameterNonnegative targetPositive
  have squaredPositive := Fraction.Order.Arithmetic.pow_pos_direct tolerance.positive 2
  let index := Geometric.Search.firstQuarterBelow preflight.readingScale 0 (tolerance.epsilon ^ 2)
  let depth := Geometric.Search.firstQuarterBelow (preflight.taylorScale * diameter) 0 (tolerance.epsilon ^ 2)
  let basis := PrimitiveBasis.ofPreflight preflight index
  let leafDiameter := Geometric.Basic.quarterRadius diameter depth
  let products := TriangleProductBudget.uniform preflight.coefficientScale tolerance.epsilon leafDiameter
    preflight.coefficientScale_nonnegative tolerance.positive.le tolerance.le_one (Geometric.Basic.quarterRadius_nonneg
      diameterNonnegative depth)
  { diameter_nonnegative := diameterNonnegative
    target_positive := targetPositive
    tolerance := tolerance
    index := index
    basis := basis
    coefficientScale_eq := rfl
    readingScale_eq := rfl
    taylorScale_eq := rfl
    reading_small := (Geometric.Search.firstQuarterBelow_accurate preflight.readingScale
      preflight.readingScale_nonnegative 0 _ squaredPositive).le
    depth := depth
    leafDiameter := leafDiameter
    leafDiameter_eq := rfl
    taylor_small := by
      rw [quarterRadius_mul]
      exact (Geometric.Search.firstQuarterBelow_accurate _
        (Fraction.Order.Arithmetic.mul_nonneg_direct basis.taylorScale_nonnegative diameterNonnegative) 0 _
          squaredPositive).le
    products := products
    faceBudget := products.first + products.second + products.mixed
    faceBudget_eq := rfl
    faceBudget_le := by apply le_of_eq; dsimp only [products, TriangleProductBudget.uniform]; ring1 }

section
open Purelib.Approximation.Rational
/-- Advance the original retained basis index while preserving its tolerance, depth and exact face budgets.

A later index only decreases the reading allowance; the original preflight scales and Taylor certificate keep the same
geometric subdivision and product data. -/
def refineIndex (budget : PrimitiveSurfaceBudget preflight diameter target) (index : Nat)
    (later : budget.index ≤ index) : PrimitiveSurfaceBudget preflight diameter target where
  diameter_nonnegative := budget.diameter_nonnegative
  target_positive := budget.target_positive
  tolerance := budget.tolerance
  index := index
  basis := PrimitiveBasis.ofPreflight preflight index
  coefficientScale_eq := rfl
  readingScale_eq := rfl
  taylorScale_eq := rfl
  reading_small := by
    rw [PrimitiveBasis.ofPreflight_readingScale, ← budget.readingScale_eq]
    exact (quarterRadius_antitone budget.basis.readingScale_nonnegative later).trans
      budget.reading_small
  depth := budget.depth
  leafDiameter := budget.leafDiameter
  leafDiameter_eq := budget.leafDiameter_eq
  taylor_small := by
    rw [PrimitiveBasis.ofPreflight_taylorScale, ← budget.taylorScale_eq]
    exact budget.taylor_small
  products := budget.products
  faceBudget := budget.faceBudget
  faceBudget_eq := budget.faceBudget_eq
  faceBudget_le := budget.faceBudget_le

/-- The retained geometric leaf diameter is nonnegative. -/
theorem leafDiameter_nonnegative (budget : PrimitiveSurfaceBudget preflight diameter target) : 0 ≤ budget.leafDiameter
  := by
  rw [budget.leafDiameter_eq]
  exact Geometric.Basic.quarterRadius_nonneg budget.diameter_nonnegative budget.depth

end

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Algebra in
/-- The dyadic face count cancels the quarter-radius denominator.

At depth `depth`, multiplying the diameter's quarter-radius scale by twice
four raised to that depth gives twice the original diameter. -/
theorem face_count_cancel (diameter : Fraction.Rational) (depth : Nat) :
    ((2 * 4 ^ depth : Nat) : Fraction.Rational) * Geometric.Basic.quarterRadius diameter depth = 2 * diameter := by
  simp only [NatCast.mul, NatCast.pow, Nat.cast_ofNat, Geometric.Basic.quarterRadius]
  calc
    _ = 2 * ((diameter / (4 : Fraction.Rational) ^ depth) * (4 : Fraction.Rational) ^ depth) := by ring1
    _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _
      (Fraction.Order.Arithmetic.pow_pos_direct (by decide) depth).ne']

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- The original subdivision face count times its retained uniform face budget is below the requested target. -/
theorem total_faceBudget_lt (budget : PrimitiveSurfaceBudget preflight diameter target) :
    ((2 * 4 ^ budget.depth : Nat) : Fraction.Rational) * budget.faceBudget < target := by
  have initial := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct budget.faceBudget_le
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (2 * 4 ^ budget.depth)))
  rw [budget.leafDiameter_eq] at initial
  apply initial.trans_lt
  calc
    _ = budget.tolerance.epsilon * (2 * preflight.coefficientScale + 3) *
        (((2 * 4 ^ budget.depth : Nat) : Fraction.Rational) * Geometric.Basic.quarterRadius diameter budget.depth) := by
          ring1
    _ = budget.tolerance.epsilon * (2 * preflight.coefficientScale + 3) * (2 * diameter) := by rw [face_count_cancel]
    _ = 2 * diameter * (2 * preflight.coefficientScale + 3) * budget.tolerance.epsilon := by ring1
    _ < target := budget.tolerance.accurate

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- An edge within the retained leaf diameter satisfies the original uniform increment-error scale. -/
theorem incrementScale_le (budget : PrimitiveSurfaceBudget preflight diameter target)
    {first second : Gaussian} (distanceLe : normSq (second - first) ≤ budget.leafDiameter) :
    budget.basis.incrementScale first second ≤ 2 * budget.tolerance.epsilon ^ 2 * budget.leafDiameter := by
  have distanceNonnegative := Basic.Canonical.normSq_nonneg (second - first)
  have taylorFirst := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distanceLe
    budget.basis.taylorScale_nonnegative).trans
    budget.taylor_small
  have taylor := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct taylorFirst distanceNonnegative).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distanceLe (Fraction.Order.Arithmetic.sq_nonneg_direct
      _))
  have reading := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct budget.reading_small
    distanceNonnegative).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distanceLe (Fraction.Order.Arithmetic.sq_nonneg_direct
      _))
  calc
    _ = (budget.basis.taylorScale * normSq (second - first)) * normSq (second - first) +
        Geometric.Basic.quarterRadius budget.basis.readingScale budget.index * normSq (second - first) := by
          unfold PrimitiveBasis.incrementScale; ring1
    _ ≤ _ := (add_le_add taylor reading).trans_eq (by ring1)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Energy in
open Purelib.Polynomial in
open Purelib.Riemann.Readings in
/-- Certify one original leaf triangle using the retained uniform surface product budgets.

All points lie in the same continued patch, both edge movements fit the retained leaf diameter, and the root witness is
explicitly possible at the original reading index. -/
def triangleCertificate (budget : PrimitiveSurfaceBudget preflight diameter target) (coefficients : Coefficients count)
    {first second third : Gaussian}
    (firstInside : patch.box.Contains first) (secondInside : patch.box.Contains second) (thirdInside :
      patch.box.Contains third)
    (secondDistance : normSq (second - first) ≤ budget.leafDiameter) (thirdDistance : normSq (third - first) ≤
      budget.leafDiameter)
    (sample : ContinuedNeighborhood.Point patch first) {root : Gaussian}
    (possible : sample.certificate.value.name.process.Possible (sample.readingState budget.index) root) :
    AffineTriangle.AffineTriangleErrorCertificate ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval
      first / root)
      first second third (budget.basis.value coefficients first) (budget.basis.value coefficients second)
        (budget.basis.value coefficients third) := by
  have normNonnegative := PrimitiveBasis.coefficientNorm_nonnegative coefficients
  have coefficientLe := budget.basis.operational_coefficient_bound coefficients firstInside sample (sample.readingState
    budget.index) possible
  rw [budget.coefficientScale_eq] at coefficientLe
  have affineLe {point : Gaussian} (distanceLe : normSq (point - first) ≤ budget.leafDiameter) :
      normSq (AffineTriangle.affinePrimitiveIncrement ((Geometry.EvaluationLower.coefficientPolynomial
        coefficients).eval first / root) first point) ≤
        PreparedObservationCoercivity.coefficientNormSq coefficients * (preflight.coefficientScale *
          budget.leafDiameter) := by
    unfold AffineTriangle.affinePrimitiveIncrement
    rw [← mul_sub, Basic.Canonical.normSq_mul]
    have first := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficientLe
      (Basic.Canonical.normSq_nonneg (point - first))
    have second := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distanceLe
      (Fraction.Order.Arithmetic.mul_nonneg_direct normNonnegative preflight.coefficientScale_nonnegative)
    exact (first.trans second).trans_eq (by ring1)
  have errorLe {point : Gaussian} (inside : patch.box.Contains point) (distanceLe : normSq (point - first) ≤
    budget.leafDiameter) :
      normSq (AffineTriangle.affinePrimitiveIncrementError
        ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval first / root) first point
        (budget.basis.value coefficients first) (budget.basis.value coefficients point)) ≤
      PreparedObservationCoercivity.coefficientNormSq coefficients * (2 * budget.tolerance.epsilon ^ 2 *
        budget.leafDiameter) := by
    have identity : AffineTriangle.affinePrimitiveIncrementError
        ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval first / root) first point
        (budget.basis.value coefficients first) (budget.basis.value coefficients point) =
      budget.basis.value coefficients point - budget.basis.value coefficients first -
        ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval first / root) * (point - first) := by
      unfold AffineTriangle.affinePrimitiveIncrementError AffineTriangle.affinePrimitiveIncrement
      ring1
    rw [identity]
    exact (budget.basis.operational_increment_bound coefficients firstInside inside sample possible).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (budget.incrementScale_le distanceLe) normNonnegative)
  exact budget.products.certificate _ normNonnegative _ first second third _ _ _
    (affineLe secondDistance) (affineLe thirdDistance) (errorLe secondInside secondDistance) (errorLe thirdInside
      thirdDistance)

open Purelib.Riemann.Readings in
/-- The retained leaf-triangle certificate total is coefficient squared norm times the exact original face budget. -/
theorem triangleCertificate_total (budget : PrimitiveSurfaceBudget preflight diameter target) (coefficients :
  Coefficients count)
    {first second third : Gaussian}
    (firstInside : patch.box.Contains first) (secondInside : patch.box.Contains second) (thirdInside :
      patch.box.Contains third)
    (secondDistance : normSq (second - first) ≤ budget.leafDiameter) (thirdDistance : normSq (third - first) ≤
      budget.leafDiameter)
    (sample : ContinuedNeighborhood.Point patch first) {root : Gaussian}
    (possible : sample.certificate.value.name.process.Possible (sample.readingState budget.index) root) :
    (budget.triangleCertificate coefficients firstInside secondInside thirdInside secondDistance thirdDistance sample
      possible).totalBudget =
      PreparedObservationCoercivity.coefficientNormSq coefficients * budget.faceBudget := by
  change PreparedObservationCoercivity.coefficientNormSq coefficients * budget.products.first +
    PreparedObservationCoercivity.coefficientNormSq coefficients * budget.products.second +
    PreparedObservationCoercivity.coefficientNormSq coefficients * budget.products.mixed = _
  rw [budget.faceBudget_eq]
  ring1

end PrimitiveSurfaceBudget

end Purelib.Riemann.Topology
