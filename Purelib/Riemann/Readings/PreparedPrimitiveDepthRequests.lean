module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Spatial
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Riemann.Paths.PreparedCheckedPrimitivePaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
public import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-! Later prepared spatial depths preserve the retained polynomial and all
numerical allowances, while the new checked mesh certifies the exact path. -/
section

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Budget.Spatial (SpatialBudget)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (Coordinate)

variable {target movement taylorWeight errorWeight preparedScale denominatorLower : Purelib.Data.Rat.Fraction.Rational}
  {preparationDepth : Purelib.Data.Rat.Fraction.Rational → Nat}

namespace Purelib.Approximation.Rational.Budget.Spatial.SpatialBudget

open Purelib.Approximation in
open Purelib.Data in
/-- Extend a spatial budget to a supplied later depth.

The original polynomial and numerical allowances are retained; nonnegative movement, Taylor weight and prepared scale
transport the spatial payments by quarter-radius monotonicity. -/
@[expose] def atDepth (budget :
  Rational.Budget.Spatial.SpatialBudget target movement taylorWeight errorWeight preparedScale denominatorLower
  preparationDepth)
    (depth : Nat) (later : budget.depth ≤ depth) (movementNonnegative : 0 ≤ movement)
    (taylorNonnegative : 0 ≤ taylorWeight) (scaleNonnegative : 0 ≤ preparedScale) :
    Rational.Budget.Spatial.SpatialBudget target movement taylorWeight errorWeight preparedScale denominatorLower
      preparationDepth :=
  { budget with
    depth := depth
    prepared_depth := budget.prepared_depth.trans later
    modelError_le := (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Rat.Fraction.Order.Arithmetic.add_le_add_direct (quarterRadius_antitone
        movementNonnegative later) le_rfl) scaleNonnegative).trans budget.modelError_le
    taylor_le := (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (quarterRadius_antitone movementNonnegative later) taylorNonnegative).trans
        budget.taylor_le }

end Purelib.Approximation.Rational.Budget.Spatial.SpatialBudget

end

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (directParentBlockAtDepth)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (Request movement_nonnegative preparedScale_nonnegative)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {patch : ContinuedNeighborhood curve.polynomial count} {target :
    Coordinate}

namespace Purelib.Riemann.Readings.PreparedPrimitiveRequests.Request

open Purelib.Data in
/-- Extend a retained primitive request to a supplied later spatial mesh.

The original coefficient, primitive and numerical allowances are reused. Only the checked child block is materialized at
the new depth, for a proper original parent interval. -/
@[expose] def atDepth (request : Request parent patch target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (depth : Nat) (later : request.block.depth ≤ depth) : Request parent patch target :=
  let budget := request.budget.atDepth depth (request.block_depth.symm.trans_le later) (movement_nonnegative parent)
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      request.model.primitive.remainderBound_nonnegative) (movement_nonnegative parent))
    (preparedScale_nonnegative parent)
  let block := directParentBlockAtDepth parent proper budget.rootDiameter budget.rootDiameter_positive depth
    budget.prepared_depth
  { request with budget := budget, block := block, block_depth := rfl, block_rootDiameter := rfl }

/-- Spatial extension retains exactly the supplied later block depth. -/
theorem atDepth_depth (request : Request parent patch target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (depth : Nat) (later : request.block.depth ≤ depth) :
    (request.atDepth proper depth later).block.depth = depth := rfl

open Purelib.Riemann in
open Purelib.Integration in
/-- The extended block's actual endpoint differences equal the dyadic increments on the original parent parameter
interval. -/
theorem atDepth_path (request : Request parent patch target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (depth : Nat) (later : request.block.depth ≤ depth) (value : Gaussian → Gaussian) :
    (request.atDepth proper depth later).block.children.map
      (fun child => value (child.edge.point 1) - value (child.edge.point 0)) =
      Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (parent.edge.point parameter)) depth 0 1
        :=
  Paths.PreparedCheckedPrimitivePaths.PreparedDirectDyadicRefinements.checkedParentBlock_primitive_increments parent _
    value

end Purelib.Riemann.Readings.PreparedPrimitiveRequests.Request

end

section
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {target : Coordinate}

namespace Purelib.Riemann.Readings.UniformPreparedRequests.LocalRequest

/-- Extend the inner spatial request while retaining its original patch, neighborhood and endpoint evidence. -/
@[expose] def atDepth (request : LocalRequest parent count target)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (depth : Nat) (later : request.request.block.depth ≤ depth) : LocalRequest parent count target :=
  { request with request := request.request.atDepth proper depth later }

end Purelib.Riemann.Readings.UniformPreparedRequests.LocalRequest

end

section
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledLocalRequest)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {target coefficientTarget : Coordinate} {minimum : Nat}

namespace Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests.ControlledLocalRequest

/-- Extend spatial depth while preserving the original coefficient-error and polynomial-index controls. -/
@[expose] def atDepth (request : ControlledLocalRequest parent count target coefficientTarget minimum)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (depth : Nat) (later : request.localRequest.request.block.depth ≤ depth) :
    ControlledLocalRequest parent count target coefficientTarget minimum :=
  ⟨request.localRequest.atDepth proper depth later, request.coefficient_accurate, request.index_ge⟩

end Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests.ControlledLocalRequest

end
