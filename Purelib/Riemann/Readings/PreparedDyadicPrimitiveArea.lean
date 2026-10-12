module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
public import Purelib.Riemann.Readings.PreparedRefinementPrimitiveArea
import Purelib.Riemann.Paths.PreparedScheduledPrimitivePaths
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
public import Purelib.Riemann.Paths.PreparedNestedDyadicPaths
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.List.Map

public section

/-! Read the existing retained-primitive comparison on exact dyadic paths,
with each ancestor retaining its own polynomial and its own origin. -/
namespace Purelib.Riemann.Readings.PreparedDyadicPrimitiveArea

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedRefinementPrimitiveArea (refinementAreaPairs)
open Purelib.Riemann.Readings.PreparedNestedPrimitiveArea (descendantPairs)
open Purelib.Integration.Path.BoundaryRibbon (Gaussian)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)
open Purelib.Riemann.Paths.PreparedNestedDyadicPaths (DyadicPaths)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {target : Purelib.Data.Rat.Fraction.Rational}

section
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
/-- Concatenate each original parent's primitive increments at one shared dyadic depth. -/
@[expose] def dyadicPrimitivePath (depth : Nat) : ∀ {parents : List (CenteredEdge curve source)},
    RequestedParents count target parents → List BoundaryRibbon.Gaussian
  | _, .nil => []
  | parent :: _, .cons request tail =>
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => request.request.model.primitive.value.eval
        (parent.edge.point parameter)) depth 0 1 ++
        dyadicPrimitivePath depth tail

/-- Depth-zero child dyadic paths read back their original primitive endpoint differences. -/
private theorem zero_paths (children : List (CenteredEdge curve source)) (value : BoundaryRibbon.Gaussian →
  BoundaryRibbon.Gaussian) :
    (children.map (fun child => DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (child.edge.point
      parameter)) 0 0 1)).flatten =
      children.map (fun child => value (child.edge.point 1) - value (child.edge.point 0)) := by
  induction children with
  | nil => rfl
  | cons child children ih => exact congrArg (List.cons _) ih

end

/-- The retained refinement's primitive components are exactly its shared-depth dyadic primitive path.

The original per-block dyadic readbacks and root-subedge refinement preserve the requested primitive models and ordered
parent/child increments. -/
theorem refinementAreaPairs_dyadic {parents children : List (CenteredEdge curve source)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children)
    {depth : Nat} (paths : DyadicPaths depth refinement) :
    (refinementAreaPairs requests refinement).map Prod.fst = dyadicPrimitivePath depth requests := by
  induction requests generalizing children with
  | nil => cases refinement; rfl
  | cons request tail ih =>
      cases refinement with
      | @cons parent parents block children chain roots remaining =>
          rw [refinementAreaPairs, Map.map_append]
          apply congrArg₂ List.append
          · have path := paths.1 request.request.model.primitive.value.eval 0
            rw [Nat.add_zero, zero_paths] at path
            have readback : (descendantPairs request block).map Prod.fst =
                block.map (fun child => request.request.model.primitive.value.eval (child.edge.point 1) -
                  request.request.model.primitive.value.eval (child.edge.point 0)) := by
              clear path paths chain roots
              induction block with
              | nil => rfl
              | cons child block ih => exact congrArg (List.cons _) ih
            exact readback.trans path
          · exact ih remaining paths.2

end Purelib.Riemann.Readings.PreparedDyadicPrimitiveArea
