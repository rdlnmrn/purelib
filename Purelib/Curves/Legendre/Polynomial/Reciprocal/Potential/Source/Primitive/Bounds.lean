module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Source.Primitive.Requests
import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual
import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.Cells.Numerator
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Uniform
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Physical primitive budgets before reciprocal-cell construction

The three original numerator and residual caches can be constructed from
an actual regular-model sample before choosing a reciprocal stage. Their
two original requests then precede the reciprocal cell. Attachment consumes
those same complete caches and the subsequently constructed original cell.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box half)
open Purelib.Riemann.Normalization.InverseModelPrimitiveBounds (PrimitiveDerivativeBounds)
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual (PrimitiveResidualBounds)
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds (Cell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformRequest)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Approximation.Rational.Geometric.Search (Selection)

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {count : Nat} {center : Gaussian}
    {centerOwner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval center)}
    {terminal : TerminalModels.Terminal cap centerOwner count}
    {sourceDifferential : Curves.Hyperelliptic.Differentials.Basic.Differential 1}
    {numerator : Polynomial} {index : Nat} {regularBox : Box}

/-- The original three complete physical-numerator caches, independent of any reciprocal cell stage.

The first value retains the actual regular sample's physical coefficient.
The other two values are the original derivative and residual owners on the
same reciprocal model; their existing fields and certificates are unchanged.
-/
@[expose] def Bounds (comparison : TerminalComparison.Data terminal sourceDifferential)
    (sample : PolynomialSample cap numerator index regularBox) : Type _ :=
  (coefficient : { value : Polynomial // value = sample.physicalCoefficient }) ×
  (primitive : PrimitiveDerivativeBounds comparison.rootBounds coefficient.val) ×
  PrimitiveResidualBounds comparison.rootBounds terminal.preparation.reciprocal primitive 0

namespace Bounds

/-- Construct the actual physical coefficient and both original budgets once, before any reciprocal cell exists. -/
def build (comparison : TerminalComparison.Data terminal sourceDifferential)
    (sample : PolynomialSample cap numerator index regularBox) : Bounds comparison sample :=
  let coefficient := sample.physicalCoefficient
  let primitive := PrimitiveDerivativeBounds.build comparison.rootBounds coefficient
  let bounds := PrimitiveResidualBounds.build comparison.rootBounds terminal.preparation.reciprocal primitive 0
  ⟨⟨coefficient, rfl⟩, primitive, bounds⟩

/-- The complete budget factory retains exactly the original three ordered cache constructions. -/
private theorem packaged_build_factory (comparison : TerminalComparison.Data terminal sourceDifferential)
    (sample : PolynomialSample cap numerator index regularBox) :
    build comparison sample =
      (let coefficient := sample.physicalCoefficient
       let primitive := PrimitiveDerivativeBounds.build comparison.rootBounds coefficient
       let bounds := PrimitiveResidualBounds.build comparison.rootBounds terminal.preparation.reciprocal primitive 0
       ⟨⟨coefficient, rfl⟩, primitive, bounds⟩ : Bounds comparison sample) := by rfl

/-- The complete budget factory retains exactly the original three ordered cache constructions. -/
theorem build_factory (comparison : TerminalComparison.Data terminal sourceDifferential)
    (sample : PolynomialSample cap numerator index regularBox) :
    build comparison sample =
      (let coefficient := sample.physicalCoefficient
       let primitive := PrimitiveDerivativeBounds.build comparison.rootBounds coefficient
       let bounds := PrimitiveResidualBounds.build comparison.rootBounds terminal.preparation.reciprocal primitive 0
       ⟨⟨coefficient, rfl⟩, primitive, bounds⟩ : Bounds comparison sample) :=
  packaged_build_factory comparison sample

variable {comparison : TerminalComparison.Data terminal sourceDifferential}
    {sample : PolynomialSample cap numerator index regularBox}

/-- Read the same complete certified physical coefficient without reevaluating its sample factory. -/
def coefficient (data : Bounds comparison sample) :
    { value : Polynomial // value = sample.physicalCoefficient } := data.1

/-- Read the same original derivative-budget owner on the retained physical coefficient. -/
def primitive (data : Bounds comparison sample) :
    PrimitiveDerivativeBounds comparison.rootBounds data.1.val := data.2.1

/-- Read the same original residual-budget owner, before its reciprocal stage is selected. -/
def residual (data : Bounds comparison sample) :
    PrimitiveResidualBounds comparison.rootBounds terminal.preparation.reciprocal data.2.1 0 := data.2.2

/-- The coefficient reader retains the whole original certified value. -/
private theorem packaged_coefficient_eq (data : Bounds comparison sample) : data.coefficient = data.1 := by rfl

/-- The coefficient reader retains the whole original certified value. -/
theorem coefficient_eq (data : Bounds comparison sample) : data.coefficient = data.1 := packaged_coefficient_eq data

/-- The derivative-budget reader retains the whole original owner. -/
private theorem packaged_primitive_eq (data : Bounds comparison sample) : data.primitive = data.2.1 := by rfl

/-- The derivative-budget reader retains the whole original owner. -/
theorem primitive_eq (data : Bounds comparison sample) : data.primitive = data.2.1 := packaged_primitive_eq data

/-- The residual-budget reader retains the whole original owner. -/
private theorem packaged_residual_eq (data : Bounds comparison sample) : data.residual = data.2.2 := by rfl

/-- The residual-budget reader retains the whole original owner. -/
theorem residual_eq (data : Bounds comparison sample) : data.residual = data.2.2 := packaged_residual_eq data

/-- Build the two original physical budgets from one retained complete coefficient on the same regular sample.

The coefficient is supplied as its certified exact value. Its polynomial
products are not recomputed; only the comparison-specific derivative and
residual budgets are constructed.
-/
def ofCoefficient (comparison : TerminalComparison.Data terminal sourceDifferential)
    (sample : PolynomialSample cap numerator index regularBox)
    (coefficient : { value : Polynomial // value = sample.physicalCoefficient }) : Bounds comparison sample :=
  let primitive := PrimitiveDerivativeBounds.build comparison.rootBounds coefficient.val
  let bounds := PrimitiveResidualBounds.build comparison.rootBounds terminal.preparation.reciprocal primitive 0
  ⟨coefficient, primitive, bounds⟩

/-- The whole stored coefficient is the exact supplied certified cache. -/
private theorem packaged_ofCoefficient_coefficient (comparison : TerminalComparison.Data terminal sourceDifferential)
    (sample : PolynomialSample cap numerator index regularBox)
    (coefficient : { value : Polynomial // value = sample.physicalCoefficient }) :
    (ofCoefficient comparison sample coefficient).coefficient = coefficient := by rfl

/-- The whole stored coefficient is the exact supplied certified cache. -/
theorem ofCoefficient_coefficient (comparison : TerminalComparison.Data terminal sourceDifferential)
    (sample : PolynomialSample cap numerator index regularBox)
    (coefficient : { value : Polynomial // value = sample.physicalCoefficient }) :
    (ofCoefficient comparison sample coefficient).coefficient = coefficient :=
  packaged_ofCoefficient_coefficient comparison sample coefficient

variable {preparation : PotentialComparison.Preparation comparison}
    {start finish : Gaussian} {coordinate : Spatial.Coordinate start finish}
    {stage : Nat} {allowance : Coordinate} {nonnegative : 0 ≤ allowance}

/-- Attach the same three budgets to one original numerator change on the subsequently supplied reciprocal cell.

Only the tiny returned tuple is exposed, so its residual owner can reduce
in the original request and check types. The original cell factory and
all existing physical-primitive producers remain opaque and unchanged.
-/
@[expose] def attach (data : Bounds comparison sample)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) : PhysicalPrimitive sample retained :=
  let cell := Cell.withNumerator data.2.2 retained
  ⟨data.1, data.2.1, data.2.2, ⟨cell, rfl⟩⟩

/-- The complete attachment contains the same three stored values and one original same-inverse numerator change. -/
private theorem packaged_attach_factory (data : Bounds comparison sample)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) :
    data.attach retained =
      (let cell := Cell.withNumerator data.2.2 retained
       ⟨data.1, data.2.1, data.2.2, ⟨cell, rfl⟩⟩ : PhysicalPrimitive sample retained) := by rfl

/-- The complete attachment contains the same three stored values and one original same-inverse numerator change. -/
theorem attach_factory (data : Bounds comparison sample)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) :
    data.attach retained =
      (let cell := Cell.withNumerator data.2.2 retained
       ⟨data.1, data.2.1, data.2.2, ⟨cell, rfl⟩⟩ : PhysicalPrimitive sample retained) :=
  packaged_attach_factory data retained

/-- Building the three caches and attaching the supplied cell preserves the whole original four-cache factory value. -/
private theorem packaged_attach_build
    (sample : PolynomialSample cap numerator index regularBox)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) :
    (build comparison sample).attach retained =
      (let coefficient := sample.physicalCoefficient
       let primitive := PrimitiveDerivativeBounds.build comparison.rootBounds coefficient
       let bounds := PrimitiveResidualBounds.build comparison.rootBounds terminal.preparation.reciprocal primitive 0
       let cell := Cell.withNumerator bounds retained
       ⟨⟨coefficient, rfl⟩, primitive, bounds, ⟨cell, rfl⟩⟩ : PhysicalPrimitive sample retained) := by rfl

/-- Building and attaching preserves the exact complete original physical-primitive factory value.

This equality does not execute the old factory. The new construction chain
can retain its budget cache and requests while constructing its later cell.
-/
theorem attach_build (sample : PolynomialSample cap numerator index regularBox)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) :
    (build comparison sample).attach retained =
      physicalPrimitive (comparison := comparison) (preparation := preparation) sample retained :=
  (packaged_attach_build (comparison := comparison) sample retained).trans
    (physicalPrimitive_factory (comparison := comparison) (preparation := preparation) sample retained).symm

/-- The attached cell is the original same-inverse numerator factory on the same retained budgets. -/
theorem attach_cell (data : Bounds comparison sample)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) :
    (data.attach retained).cell = Cell.withNumerator data.2.2 retained :=
  (data.attach retained).cell_eq

/-- The two original paid requests depend on the cached budgets and actual preparation, without a reciprocal cell. -/
@[expose] def Requests (data : Bounds comparison sample)
    (preparation : PotentialComparison.Preparation comparison) (coordinate : Spatial.Coordinate start finish)
    (floor : Nat) (target allowance : Coordinate) : Type _ :=
  Selection (2 * Data.Gaussian.Norm.Basic.normSq coordinate.displacement * data.2.2.scale) floor target ×
    UniformRequest preparation.2.2 1 (data.2.2.coefficient.scale half) floor (allowance / 4)

/-- Select both actual request floors before constructing any reciprocal cell or numerator-dependent tables. -/
def requests (data : Bounds comparison sample) (preparation : PotentialComparison.Preparation comparison)
    (coordinate : Spatial.Coordinate start finish) (floor : Nat) (target : Coordinate) (targetPositive : 0 < target)
    (allowance : Coordinate) (positive : 0 < allowance) : Requests data preparation coordinate floor target allowance :=
  let integral := Cell.choose data.2.2 coordinate floor target targetPositive
  let quarterPositive := Data.Rat.Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let uniform := preparation.2.2.request 1 (data.2.2.coefficient.scale half) floor (allowance / 4) quarterPositive
  ⟨integral, uniform⟩

/-- The complete pre-cell request factory retains the two original selections and no cell-model construction. -/
private theorem packaged_requests_factory (data : Bounds comparison sample)
    (preparation : PotentialComparison.Preparation comparison) (coordinate : Spatial.Coordinate start finish)
    (floor : Nat) (target : Coordinate) (targetPositive : 0 < target) (allowance : Coordinate)
    (positive : 0 < allowance) :
    data.requests preparation coordinate floor target targetPositive allowance positive =
      (let integral := Cell.choose data.2.2 coordinate floor target targetPositive
       let quarterPositive := Data.Rat.Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
       let uniform := preparation.2.2.request 1 (data.2.2.coefficient.scale half) floor
         (allowance / 4) quarterPositive
       ⟨integral, uniform⟩ : Requests data preparation coordinate floor target allowance) := by rfl

/-- The complete pre-cell request factory retains the two original selections and no cell-model construction. -/
theorem requests_factory (data : Bounds comparison sample)
    (preparation : PotentialComparison.Preparation comparison) (coordinate : Spatial.Coordinate start finish)
    (floor : Nat) (target : Coordinate) (targetPositive : 0 < target) (allowance : Coordinate)
    (positive : 0 < allowance) :
    data.requests preparation coordinate floor target targetPositive allowance positive =
      (let integral := Cell.choose data.2.2 coordinate floor target targetPositive
       let quarterPositive := Data.Rat.Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
       let uniform := preparation.2.2.request 1 (data.2.2.coefficient.scale half) floor
         (allowance / 4) quarterPositive
       ⟨integral, uniform⟩ : Requests data preparation coordinate floor target allowance) :=
  packaged_requests_factory data preparation coordinate floor target targetPositive allowance positive

/-- The pre-cell selections are the same complete original requests on the attached unchanged reciprocal cell. -/
theorem requests_attach {first last : LiftedPoint 2} (data : Bounds comparison sample)
    (preparation : PotentialComparison.Preparation comparison)
    (coordinate : Spatial.Coordinate first.coordinate last.coordinate)
    (floor : Nat) (target : Coordinate) (targetPositive : 0 < target) (allowance : Coordinate)
    (positive : 0 < allowance)
    (retained : Cell preparation.2.1 coordinate stage allowance positive.le) :
    PhysicalPrimitive.requests (comparison := comparison) (preparation := preparation)
      (first := first) (last := last) (coordinate := coordinate) (positive := positive)
      (data.attach retained) floor target targetPositive =
      data.requests preparation coordinate floor target targetPositive allowance positive :=
  (PhysicalPrimitive.requests_factory (comparison := comparison) (preparation := preparation)
    (first := first) (last := last) (coordinate := coordinate) (positive := positive)
    (data.attach retained) floor target targetPositive).trans
    (requests_factory data preparation coordinate floor target targetPositive allowance positive).symm

end Bounds

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive

end
