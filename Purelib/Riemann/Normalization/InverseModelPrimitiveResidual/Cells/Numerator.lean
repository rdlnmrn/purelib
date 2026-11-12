module

public import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.Cells
import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Riemann.Normalization.InverseModelDerivativeBounds
import Purelib.Riemann.Normalization.InverseModelDifferentialResidual
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial
import Purelib.Polynomial.Dense.Power

/-! # Numerator changes on the same retained primitive-residual cell

Only the numerator-dependent value, density and spatial compilation are
constructed. The complete original inverse model and power bank remain the
actual supplied cache values, with the original refinement and whole-power
factory certificates. No inverse refinement or root observation is replayed.
-/

public section

namespace Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds.Cell

open Purelib
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box Model half)
open Purelib.Riemann.Normalization.InverseModelDerivativeBounds (DerivativeBounds)
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual (DifferentialResidualBounds)
open Purelib.Riemann.Normalization.InverseModelPrimitiveBounds (PrimitiveDerivativeBounds)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance)
open Purelib.Integration.Polynomial.Gaussian.Cell

variable {polynomial originalNumerator numerator : Polynomial} {box : Box}
    {clearance : RegionClearance polynomial box} {initial : Model polynomial box}
    {root : DerivativeBounds clearance initial} {residual : DifferentialResidualBounds initial}
    {originalPrimitive : PrimitiveDerivativeBounds root originalNumerator}
    {primitive : PrimitiveDerivativeBounds root numerator}
    {originalBounds : PrimitiveResidualBounds root residual originalPrimitive 0}
    {start finish : Gaussian} {coordinate : Spatial.Coordinate start finish}
    {stage : Nat} {allowance : Coordinate} {nonnegative : 0 ≤ allowance}

/-- Construct numerator-dependent tables on the same complete original inverse and power caches.

Both primitive budgets retain the same initial model, clearance, derivative
and differential-residual owners. The supplied cell's actual stage and
physical coordinate remain unchanged; this operation does not claim that
its stage pays a newly requested smaller error.
-/
def withNumerator (bounds : PrimitiveResidualBounds root residual primitive 0)
    (retained : Cell originalBounds coordinate stage allowance nonnegative) :
    Cell bounds coordinate stage allowance nonnegative :=
  let value := numerator * retained.inverse.value
  let density := bounds.coefficient.scale half * retained.powers.cube
  let pulled := Spatial.Pullback.build coordinate density allowance nonnegative
  ⟨⟨retained.inverse, retained.inverse_eq⟩, ⟨retained.powers, retained.powers_eq⟩,
    ⟨value, rfl⟩, ⟨density, rfl⟩, ⟨pulled, rfl⟩⟩

/-- Retain the two original caches and exactly three new numerator-dependent values in the whole returned cell. -/
private theorem packaged_withNumerator_factory (bounds : PrimitiveResidualBounds root residual primitive 0)
    (retained : Cell originalBounds coordinate stage allowance nonnegative) :
    withNumerator bounds retained =
      (let value := numerator * retained.inverse.value
       let density := bounds.coefficient.scale half * retained.powers.cube
       let pulled := Spatial.Pullback.build coordinate density allowance nonnegative
       ⟨⟨retained.inverse, retained.inverse_eq⟩, ⟨retained.powers, retained.powers_eq⟩,
         ⟨value, rfl⟩, ⟨density, rfl⟩, ⟨pulled, rfl⟩⟩ : Cell bounds coordinate stage allowance nonnegative) := by rfl

/-- Retain the two original caches and exactly three new numerator-dependent values in the whole returned cell. -/
theorem withNumerator_factory (bounds : PrimitiveResidualBounds root residual primitive 0)
    (retained : Cell originalBounds coordinate stage allowance nonnegative) :
    withNumerator bounds retained =
      (let value := numerator * retained.inverse.value
       let density := bounds.coefficient.scale half * retained.powers.cube
       let pulled := Spatial.Pullback.build coordinate density allowance nonnegative
       ⟨⟨retained.inverse, retained.inverse_eq⟩, ⟨retained.powers, retained.powers_eq⟩,
         ⟨value, rfl⟩, ⟨density, rfl⟩, ⟨pulled, rfl⟩⟩ : Cell bounds coordinate stage allowance nonnegative) :=
  packaged_withNumerator_factory bounds retained

/-- The numerator change retains the complete original finite inverse model at the same actual refinement index. -/
theorem withNumerator_inverse (bounds : PrimitiveResidualBounds root residual primitive 0)
    (retained : Cell originalBounds coordinate stage allowance nonnegative) :
    (withNumerator bounds retained).inverse = retained.inverse :=
  (inverse_eq (withNumerator bounds retained)).trans retained.inverse_eq.symm

/-- Its value table multiplies the new numerator by the same retained original inverse polynomial. -/
theorem withNumerator_value (bounds : PrimitiveResidualBounds root residual primitive 0)
    (retained : Cell originalBounds coordinate stage allowance nonnegative) :
    (withNumerator bounds retained).value = numerator * retained.inverse.value :=
  (value_eq (withNumerator bounds retained)).trans
    (congrArg (fun model : Model polynomial box => numerator * model.value)
      (withNumerator_inverse bounds retained))

/-- Its cubic polynomial is the same original cached cube, without a new power factory. -/
theorem withNumerator_cube (bounds : PrimitiveResidualBounds root residual primitive 0)
    (retained : Cell originalBounds coordinate stage allowance nonnegative) :
    (withNumerator bounds retained).powers.cube = retained.powers.cube := by
  have first := (withNumerator bounds retained).powers.cube_eq.trans
    (congrArg (fun value : Polynomial => value * (withNumerator bounds retained).inverse.value)
      (withNumerator bounds retained).powers.square_eq)
  have last := retained.powers.cube_eq.trans
    (congrArg (fun value : Polynomial => value * retained.inverse.value) retained.powers.square_eq)
  have same := congrArg (fun model : Model polynomial box => model.value * model.value * model.value)
    (withNumerator_inverse bounds retained)
  exact first.trans (same.trans last.symm)

/-- Its density uses the new cleared coefficient and the same original cached cube. -/
theorem withNumerator_density (bounds : PrimitiveResidualBounds root residual primitive 0)
    (retained : Cell originalBounds coordinate stage allowance nonnegative) :
    (withNumerator bounds retained).density = bounds.coefficient.scale half * retained.powers.cube :=
  (density_eq (withNumerator bounds retained)).trans
    (congrArg (fun value : Polynomial => bounds.coefficient.scale half * value)
      (withNumerator_cube bounds retained))

end Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds.Cell

end
