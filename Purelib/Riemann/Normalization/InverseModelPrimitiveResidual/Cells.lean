module

public import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Continued
public import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
public import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Uniform
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Data.Gaussian.Power
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Power
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Tactic.Ring

/-! # Paid integral cells for finite inverse-root primitive residuals

A polynomial numerator times the original inverse model supplies the endpoint
potential. The same model and cached cube supply its algebraic differential
cell. The original square and differential residual bounds pay their finite
integral discrepancy, and actual continued Points certify its sheet readings.
-/

public section

namespace Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds

open Purelib
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box Model half)
open Purelib.Riemann.Normalization.InverseModelDerivativeBounds (DerivativeBounds)
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual (DifferentialResidualBounds)
open Purelib.Riemann.Normalization.InverseModelPrimitiveBounds (PrimitiveDerivativeBounds)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds UniformRequest)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Algebra.Quadratic.Pair.Gaussian (ReadingPrecision)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

section Models

variable {polynomial numerator : Polynomial} {box : Box}
    {clearance : RegionClearance polynomial box} {initial : Model polynomial box}
    {root : DerivativeBounds clearance initial} {residual : DifferentialResidualBounds initial}
    {primitive : PrimitiveDerivativeBounds root numerator}

/-- The original cleared cubic differential of the numerator-times-inverse potential. -/
def differential (bounds : PrimitiveResidualBounds root residual primitive 0) :
    OddPowerDifferential polynomial :=
  OddPowerDifferential.ofCoefficients polynomial bounds.coefficient 1 half

/-- The differential is the original complete odd-power factory on the retained cleared numerator. -/
private theorem packaged_differential_factory (bounds : PrimitiveResidualBounds root residual primitive 0) :
    bounds.differential = OddPowerDifferential.ofCoefficients polynomial bounds.coefficient 1 half := by rfl

/-- The differential is the original complete odd-power factory on the retained cleared numerator. -/
theorem differential_factory (bounds : PrimitiveResidualBounds root residual primitive 0) :
    bounds.differential = OddPowerDifferential.ofCoefficients polynomial bounds.coefficient 1 half :=
  packaged_differential_factory bounds

/-- The complete inverse, powers, potential, density and original spatial cell at one actual finite stage.

Every table retains its whole factory equation. The potential and density
consume the same retained inverse model, while the density uses the cube
already stored in its original power cache.
-/
@[expose] def Cell (bounds : PrimitiveResidualBounds root residual primitive 0)
    {start finish : Gaussian} (coordinate : Spatial.Coordinate start finish)
    (stage : Nat) (allowance : Coordinate) (nonnegative : 0 ≤ allowance) : Type _ :=
  (inverse : { value : Model polynomial box // value = initial.refine stage }) ×
  (powers : { value : OddPowers inverse.val.value // value = OddPowers.build inverse.val.value }) ×
  (_value : { value : Polynomial // value = numerator * inverse.val.value }) ×
  (density : { value : Polynomial // value = bounds.coefficient.scale half * powers.val.cube }) ×
  { pulled : Spatial.Pullback coordinate density.val allowance //
    pulled = Spatial.Pullback.build coordinate density.val allowance nonnegative }

namespace Cell

variable {bounds : PrimitiveResidualBounds root residual primitive 0}
    {start finish : Gaussian} {coordinate : Spatial.Coordinate start finish}
    {stage : Nat} {allowance : Coordinate} {nonnegative : 0 ≤ allowance}

/-- Read the same finite original inverse model stored by the cell. -/
def inverse (retained : Cell bounds coordinate stage allowance nonnegative) : Model polynomial box :=
  retained.1.val

/-- Read the cached powers of that exact retained inverse model. -/
def powers (retained : Cell bounds coordinate stage allowance nonnegative) :
    OddPowers retained.inverse.value := retained.2.1.val

/-- The retained cube satisfies the original inverse ceiling at every actual model stage.

The estimate reads the same cached cube and inverse model. Its ceiling
depends only on the original cleared root owner, so changing the cell's
finite refinement stage does not require choosing a new bound.
-/
theorem cube_norm_le (retained : Cell bounds coordinate stage allowance nonnegative)
    {point : Gaussian} (inside : box.Contains point) :
    Norm.Basic.normSq (retained.powers.cube.eval point) ≤ root.inverseUpper ^ 3 := by
  have value : Norm.Basic.normSq (retained.inverse.value.eval point) ≤ root.inverseUpper :=
    (Norm.Basic.normSq_eq_canonical _).trans_le (root.value_le retained.inverse inside)
  have cube := congrArg Norm.Basic.normSq (retained.powers.cube_eval point)
  exact cube.trans_le ((Norm.Power.normSq_pow _ 3).trans_le
    (Arithmetic.pow_le_pow_direct (Norm.Basic.normSq_nonneg _) value 3))

/-- Read the numerator-times-inverse potential polynomial stored by the cell. -/
def value (retained : Cell bounds coordinate stage allowance nonnegative) : Polynomial :=
  retained.2.2.1.val

/-- Read the cubic algebraic density using the same model and power cache. -/
def density (retained : Cell bounds coordinate stage allowance nonnegative) : Polynomial :=
  retained.2.2.2.1.val

/-- Read the original compiled integration cell consuming that retained density. -/
def pullback (retained : Cell bounds coordinate stage allowance nonnegative) :
    Spatial.Pullback coordinate retained.density allowance := retained.2.2.2.2.val

/-- The stored inverse is exactly the original finite Newton refinement. -/
private theorem packaged_inverse_eq (retained : Cell bounds coordinate stage allowance nonnegative) :
    retained.inverse = initial.refine stage := retained.1.property

/-- The stored inverse is exactly the original finite Newton refinement. -/
theorem inverse_eq (retained : Cell bounds coordinate stage allowance nonnegative) :
    retained.inverse = initial.refine stage :=
  packaged_inverse_eq retained

/-- The stored power cache is the original complete factory value. -/
private theorem packaged_powers_eq (retained : Cell bounds coordinate stage allowance nonnegative) :
    retained.powers = OddPowers.build retained.inverse.value := retained.2.1.property

/-- The stored power cache is the original complete factory value. -/
theorem powers_eq (retained : Cell bounds coordinate stage allowance nonnegative) :
    retained.powers = OddPowers.build retained.inverse.value :=
  packaged_powers_eq retained

/-- The potential table uses the original numerator and the same retained inverse. -/
private theorem packaged_value_eq (retained : Cell bounds coordinate stage allowance nonnegative) :
    retained.value = numerator * retained.inverse.value := retained.2.2.1.property

/-- The potential table uses the original numerator and the same retained inverse. -/
theorem value_eq (retained : Cell bounds coordinate stage allowance nonnegative) :
    retained.value = numerator * retained.inverse.value :=
  packaged_value_eq retained

/-- The density table uses the original cleared coefficient and retained inverse cube. -/
private theorem packaged_density_eq (retained : Cell bounds coordinate stage allowance nonnegative) :
    retained.density = bounds.coefficient.scale half * retained.powers.cube := retained.2.2.2.1.property

/-- The density table uses the original cleared coefficient and retained inverse cube. -/
theorem density_eq (retained : Cell bounds coordinate stage allowance nonnegative) :
    retained.density = bounds.coefficient.scale half * retained.powers.cube :=
  packaged_density_eq retained

/-- The integration cell is the original complete pullback on the retained coordinate and density. -/
private theorem packaged_pullback_eq (retained : Cell bounds coordinate stage allowance nonnegative) :
    retained.pullback = Spatial.Pullback.build coordinate retained.density allowance nonnegative :=
  retained.2.2.2.2.property

/-- The integration cell is the original complete pullback on the retained coordinate and density. -/
theorem pullback_eq (retained : Cell bounds coordinate stage allowance nonnegative) :
    retained.pullback = Spatial.Pullback.build coordinate retained.density allowance nonnegative :=
  packaged_pullback_eq retained

/-- Construct all five original tables once after the finite stage is fixed. -/
def build (bounds : PrimitiveResidualBounds root residual primitive 0)
    {start finish : Gaussian} (coordinate : Spatial.Coordinate start finish)
    (stage : Nat) (allowance : Coordinate) (nonnegative : 0 ≤ allowance) :
    Cell bounds coordinate stage allowance nonnegative :=
  let inverse := initial.refine stage
  let powers := OddPowers.build inverse.value
  let value := numerator * inverse.value
  let density := bounds.coefficient.scale half * powers.cube
  let pulled := Spatial.Pullback.build coordinate density allowance nonnegative
  ⟨⟨inverse, rfl⟩, ⟨powers, rfl⟩, ⟨value, rfl⟩, ⟨density, rfl⟩, ⟨pulled, rfl⟩⟩

/-- The complete cell contains precisely the five original once-computed factory values. -/
private theorem packaged_build_factory (bounds : PrimitiveResidualBounds root residual primitive 0)
    {start finish : Gaussian} (coordinate : Spatial.Coordinate start finish)
    (stage : Nat) (allowance : Coordinate) (nonnegative : 0 ≤ allowance) :
    build bounds coordinate stage allowance nonnegative =
      (let inverse := initial.refine stage
       let powers := OddPowers.build inverse.value
       let value := numerator * inverse.value
       let density := bounds.coefficient.scale half * powers.cube
       let pulled := Spatial.Pullback.build coordinate density allowance nonnegative
       ⟨⟨inverse, rfl⟩, ⟨powers, rfl⟩, ⟨value, rfl⟩, ⟨density, rfl⟩, ⟨pulled, rfl⟩⟩ :
        Cell bounds coordinate stage allowance nonnegative) := by rfl

/-- The complete cell contains precisely the five original once-computed factory values. -/
theorem build_factory (bounds : PrimitiveResidualBounds root residual primitive 0)
    {start finish : Gaussian} (coordinate : Spatial.Coordinate start finish)
    (stage : Nat) (allowance : Coordinate) (nonnegative : 0 ≤ allowance) :
    build bounds coordinate stage allowance nonnegative =
      (let inverse := initial.refine stage
       let powers := OddPowers.build inverse.value
       let value := numerator * inverse.value
       let density := bounds.coefficient.scale half * powers.cube
       let pulled := Spatial.Pullback.build coordinate density allowance nonnegative
       ⟨⟨inverse, rfl⟩, ⟨powers, rfl⟩, ⟨value, rfl⟩, ⟨density, rfl⟩, ⟨pulled, rfl⟩⟩ :
        Cell bounds coordinate stage allowance nonnegative) :=
  packaged_build_factory bounds coordinate stage allowance nonnegative

/-- The potential table reads the exact original numerator times the same finite inverse. -/
theorem value_eval (retained : Cell bounds coordinate stage allowance nonnegative) (point : Gaussian) :
    retained.value.eval point = numerator.eval point * (initial.refine stage).value.eval point := by
  rewrite [retained.value_eq, eval_mul, retained.inverse_eq]
  rfl

/-- The density table reads the exact cleared cubic coefficient of the same finite inverse. -/
theorem density_eval (retained : Cell bounds coordinate stage allowance nonnegative) (point : Gaussian) :
    retained.density.eval point = half * bounds.coefficient.eval point *
      (initial.refine stage).value.eval point ^ 3 := by
  rewrite [retained.density_eq, eval_mul, eval_scale, retained.powers.cube_eval,
    retained.inverse_eq]
  ring1

/-- Both actual retained tables obey the source-derived square-and-differential residual budget. -/
theorem derivative_error_le (retained : Cell bounds coordinate stage allowance nonnegative)
    {point : Gaussian} (inside : box.Contains point) :
    Norm.Basic.normSq ((Derivative.derivative retained.value).eval point - retained.density.eval point) ≤
      quarterRadius bounds.scale stage := by
  rewrite [Norm.Basic.normSq_eq_canonical]
  apply bounds.cached_refine_bound stage retained.value retained.density
  · intro sample
    have original := retained.value_eval sample
    have power : (initial.refine stage).value.eval sample ^ (0 + 1) =
        (initial.refine stage).value.eval sample := by
      change 1 * (initial.refine stage).value.eval sample = _
      exact Basic.one_mul _
    rewrite [power]
    exact original
  · exact retained.density_eval
  · exact inside

/-- Cache the actual spatial primitive residual using its source-derived uniform bound.

The original potential table and original integration cell are reused. Only
their finite derivative and residual coefficient tables are computed here.
-/
def comparison (retained : Cell bounds coordinate stage allowance nonnegative)
    (startInside : box.Contains start) (finishInside : box.Contains finish) :
    Primitive.Comparison retained.pullback.model :=
  Primitive.Comparison.ofSpatialBound retained.pullback.model retained.value
    (Norm.Basic.normSq coordinate.displacement * quarterRadius bounds.scale stage) (by
      intro parameter inside
      have source := retained.derivative_error_le
        (Geometry.Rational.Box.contains_line startInside finishInside inside)
      rewrite [retained.pullback.start_eq, retained.pullback.displacement_eq,
        coordinate.displacement_eq, retained.pullback.eval_local,
        Polynomial.Dense.Gaussian.GCD.derivative, Norm.Basic.normSq_mul]
      exact Arithmetic.mul_le_mul_of_nonneg_left_direct source (Norm.Basic.normSq_nonneg _))

/-- The actual finite cell integral pays the complete potential increment, without a Taylor error floor. -/
theorem integral_error_le (retained : Cell bounds coordinate stage allowance nonnegative)
    (startInside : box.Contains start) (finishInside : box.Contains finish) :
    Norm.Basic.normSq (retained.value.eval finish - retained.value.eval start -
      retained.pullback.model.integralSample) ≤
      quarterRadius (2 * Norm.Basic.normSq coordinate.displacement * bounds.scale) stage := by
  have estimate := (retained.comparison startInside finishInside).integral_error_le
  change Norm.Basic.normSq
    ((Primitive.spatialPrimitive retained.pullback.model retained.value).eval 1 -
      (Primitive.spatialPrimitive retained.pullback.model retained.value).eval 0 - _) ≤ _ at estimate
  rewrite [Primitive.spatialPrimitive_finish, Primitive.spatialPrimitive_start,
    retained.pullback.start_eq, retained.pullback.finish_eq] at estimate
  exact estimate.trans_eq (by
    change 2 * (Norm.Basic.normSq coordinate.displacement * quarterRadius bounds.scale stage) = _
    rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
    ring1)

/-- Select a whole-cell integral budget before constructing any refined table. -/
def choose (bounds : PrimitiveResidualBounds root residual primitive 0)
    {start finish : Gaussian} (coordinate : Spatial.Coordinate start finish)
    (floor : Nat) (target : Coordinate) (positive : 0 < target) :
    Selection (2 * Norm.Basic.normSq coordinate.displacement * bounds.scale) floor target :=
  Selection.build _
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _))
      bounds.scale_nonnegative) floor target positive

/-- Every later cell on the same original coordinate meets its retained selected integral target. -/
theorem accurate (retained : Cell bounds coordinate stage allowance nonnegative)
    {floor : Nat} {target : Coordinate}
    (selection : Selection (2 * Norm.Basic.normSq coordinate.displacement * bounds.scale) floor target)
    (later : selection.stage ≤ stage) (startInside : box.Contains start) (finishInside : box.Contains finish) :
    Norm.Basic.normSq (retained.value.eval finish - retained.value.eval start -
      retained.pullback.model.integralSample) < target :=
  (retained.integral_error_le startInside finishInside).trans_lt (selection.later_accurate later)

end Cell

end Models

section Continued

variable {genus count floor depth : Nat} {curve : HyperellipticCurve genus}
    {patch : ContinuedNeighborhood curve.polynomial count}
    {clearance : RegionClearance curve.polynomial patch.base.box}
    {root : DerivativeBounds clearance patch.base.model}
    {residual : DifferentialResidualBounds patch.base.model}
    {numerator : Polynomial} {primitive : PrimitiveDerivativeBounds root numerator}
    {bounds : PrimitiveResidualBounds root residual primitive 0}
    {uniform : UniformBounds patch} {allowance : Coordinate} {positive : 0 < allowance}
    {first last : LiftedPoint 2} {coordinate : Spatial.Coordinate first.coordinate last.coordinate}
    {request : UniformRequest uniform 1 (bounds.coefficient.scale half) floor (allowance / 4)}

namespace Cell

/-- Certify one actual cubic-density observation using the supplied original continued Point.

The finite model, powers and density are read from the retained cell. The
new root request and denotation use the same supplied Point, so neither a
replacement Point nor an independent inverse polynomial is acquired.
-/
def observe (retained : Cell bounds coordinate depth allowance positive.le)
    (lifted : LiftedCell first last) (input : Coordinate)
    (sample : ContinuedNeighborhood.Point patch (coordinate.point input))
    (inside : patch.box.Contains (coordinate.point input)) (later : request.selection.stage ≤ depth) :
    Jets.UniformObservation curve bounds.differential lifted retained.pullback.model input := by
  let localBounds := sample.primitiveBounds
  let numerator := bounds.coefficient.scale half
  let factor := numerator.eval (coordinate.point input)
  let original := retainPrimitiveDenotation sample localBounds 1 numerator ⟨factor, rfl⟩
  let ceiling := Norm.Basic.normSq original.value.im
  let precision := ReadingPrecision.build ceiling allowance (Norm.Basic.normSq_nonneg _) positive
  let root := selectPrimitiveRoot sample depth precision.target precision.target_positive
  let reading := root.readModel retained.inverse retained.inverse_eq retained.powers
  have compiled : retained.density.eval (coordinate.point input) = numerator.eval (coordinate.point input) *
      (primitivePolynomial retained.powers 1).eval (coordinate.point input) := by
    rewrite [retained.density_eq, eval_mul]
    rfl
  let value := retainPrimitiveValue reading 1 numerator original retained.density compiled ⟨factor, rfl⟩
  exact Jets.UniformObservation.ofContinuedPrimitive curve bounds.differential 1 rfl lifted
    retained.pullback input sample inside request retained.inverse_eq precision root reading rfl original value
    later (Data.Rat.Fraction.Order.Basic.le_refl _)

/-- The cubic-density observation retains the actual supplied Point's root name. -/
private theorem packaged_observe_root_name (retained : Cell bounds coordinate depth allowance positive.le)
    (lifted : LiftedCell first last) (input : Coordinate)
    (sample : ContinuedNeighborhood.Point patch (coordinate.point input))
    (inside : patch.box.Contains (coordinate.point input)) (later : request.selection.stage ≤ depth) :
    (retained.observe (positive := positive) (request := request)
      lifted input sample inside later).algebraic.sheetValue.value.name =
      sample.certificate.value.name := by
  unfold observe
  apply Jets.UniformObservation.ofContinuedPrimitive_root_name

/-- The cubic-density observation retains the actual supplied Point's root name. -/
theorem observe_root_name (retained : Cell bounds coordinate depth allowance positive.le)
    (lifted : LiftedCell first last) (input : Coordinate)
    (sample : ContinuedNeighborhood.Point patch (coordinate.point input))
    (inside : patch.box.Contains (coordinate.point input)) (later : request.selection.stage ≤ depth) :
    (retained.observe (positive := positive) (request := request)
      lifted input sample inside later).algebraic.sheetValue.value.name =
      sample.certificate.value.name :=
  packaged_observe_root_name (positive := positive) retained lifted input sample inside later

/-- Certify the whole retained cubic cell using actual continued Points along the original segment. -/
def certificate (retained : Cell bounds coordinate depth allowance positive.le)
    (lifted : LiftedCell first last)
    (startInside : patch.box.Contains first.coordinate) (finishInside : patch.box.Contains last.coordinate)
    (samples : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      ContinuedNeighborhood.Point patch (coordinate.point input)) (later : request.selection.stage ≤ depth) :
    Jets.UniformCellCertificate curve bounds.differential lifted retained.pullback.model where
  query := fun input lower upper => retained.observe (positive := positive) (request := request)
    lifted input (samples input lower upper) (coordinate.point_inside startInside finishInside lower upper) later

/-- Every certified query keeps the same original Point from the supplied physical segment. -/
private theorem packaged_certificate_root_name (retained : Cell bounds coordinate depth allowance positive.le)
    (lifted : LiftedCell first last)
    (startInside : patch.box.Contains first.coordinate) (finishInside : patch.box.Contains last.coordinate)
    (samples : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      ContinuedNeighborhood.Point patch (coordinate.point input)) (later : request.selection.stage ≤ depth)
    (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) :
    ((retained.certificate (positive := positive) (request := request)
      lifted startInside finishInside samples later).query
      input lower upper).algebraic.sheetValue.value.name = (samples input lower upper).certificate.value.name := by
  unfold certificate
  exact retained.observe_root_name (positive := positive) lifted input (samples input lower upper)
    (coordinate.point_inside startInside finishInside lower upper) later

/-- Every certified query keeps the same original Point from the supplied physical segment. -/
theorem certificate_root_name (retained : Cell bounds coordinate depth allowance positive.le)
    (lifted : LiftedCell first last)
    (startInside : patch.box.Contains first.coordinate) (finishInside : patch.box.Contains last.coordinate)
    (samples : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      ContinuedNeighborhood.Point patch (coordinate.point input)) (later : request.selection.stage ≤ depth)
    (input : Coordinate) (lower : 0 ≤ input) (upper : input ≤ 1) :
    ((retained.certificate (positive := positive) (request := request)
      lifted startInside finishInside samples later).query
      input lower upper).algebraic.sheetValue.value.name = (samples input lower upper).certificate.value.name :=
  packaged_certificate_root_name (positive := positive)
    retained lifted startInside finishInside samples later input lower upper

end Cell

end Continued

end Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds

end
