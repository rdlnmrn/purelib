module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot

public section

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
open Purelib.Riemann.Normalization

/-!
# Shared prepared, reciprocal-integral and full-area requests

The area criterion is paid before constructing either primitive bank. The
source polynomial, reciprocal cell models and all their indices are shared
with the existing controlled prepared-integral request.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests (CoupledLocalRequest
  CoupledLocalPlan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}

set_option genInjectivity false in
/-- The original controlled integral, reciprocal primitive and complete area requests sharing one source cache.

Exact stage, primitive and total identities retain the common original computation while keeping the five error targets
separate. -/
structure CoupledLocalAreaRequest (cover : UniformReciprocalCover.Cover data) (sourceTarget reciprocalTarget
  coefficientTarget areaTarget totalTarget : InverseRootPolynomial.Coordinate)
    (minimum depth : Nat) where
  /-- The retained original source and reciprocal primitive comparison request. -/ compared :
    PreparedReciprocalControlledRequests.CoupledLocalRequest cover sourceTarget reciprocalTarget coefficientTarget
    minimum
  /-- The complete area request built from those same original primitive caches. -/ area : Cover.AreaRequest cover depth
    areaTarget
  /-- The retained area and reciprocal requests use the exact same polynomial stage. -/ index_eq : area.index =
    compared.reciprocal.index
  /-- The retained area request reuses exactly the original source primitive polynomial. -/ source_eq :
    area.source.primitive.value = compared.reciprocal.source.primitive.value
  /-- The original area source-path total is exactly the retained source increment. -/ left_total_eq : area.left.total =
    compared.reciprocal.sourceIncrement
  /-- The original reciprocal area-path total is exactly the retained reciprocal increment. -/ right_total_eq :
    area.right.total = compared.reciprocal.reciprocalIncrement
  /-- The retained original total-discrepancy bound pays its separate target. -/ total_accurate :
    compared.reciprocal.error < totalTarget

constructive_injectivity CoupledLocalAreaRequest

set_option genInjectivity false in
/-- A numerical plan paying original controlled primitive, complete area and total-discrepancy targets before sampling.

The selected common stage extends the retained primitive plan and preserves its original minimum floor. -/
structure CoupledLocalAreaPlan (data : UniformReciprocalModels.Data patch count)
    (sourceTarget reciprocalTarget coefficientTarget areaTarget totalTarget : InverseRootPolynomial.Coordinate) (minimum
      : Nat) where
  /-- The retained coupled source and reciprocal primitive accuracy plan. -/ primitive :
    PreparedReciprocalControlledRequests.CoupledLocalPlan data sourceTarget reciprocalTarget coefficientTarget minimum
  /-- The common selected polynomial stage paying primitive, area and total obligations. -/ index : Nat
  /-- The common stage extends the retained original primitive-plan stage. -/ local_le : primitive.index ≤ index
  /-- The selected common stage pays the complete original boundary-area error target. -/ area_accurate :
    Geometric.Basic.quarterRadius (ReciprocalBoundaryArea.Data.boundaryAreaScale data) index < areaTarget
  /-- The retained original total-discrepancy bound pays its separate target. -/ total_accurate :
    Geometric.Basic.quarterRadius (UniformReciprocalPrimitives.Data.errorScale data) index < totalTarget

constructive_injectivity CoupledLocalAreaPlan

namespace CoupledLocalAreaPlan

/-- Select one common stage extending the original primitive plan and paying separate area and total targets. -/
@[expose] def build (data : UniformReciprocalModels.Data patch count) (sourceTarget reciprocalTarget coefficientTarget
  areaTarget totalTarget : InverseRootPolynomial.Coordinate)
    (sourcePositive : 0 < sourceTarget) (reciprocalPositive : 0 < reciprocalTarget)
    (coefficientPositive : 0 < coefficientTarget) (areaPositive : 0 < areaTarget) (totalPositive : 0 < totalTarget)
    (minimum : Nat) : Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests.CoupledLocalAreaPlan data
      sourceTarget reciprocalTarget coefficientTarget areaTarget totalTarget minimum := by
  let primitive := CoupledLocalPlan.build data sourceTarget reciprocalTarget coefficientTarget
    sourcePositive reciprocalPositive coefficientPositive minimum
  let areaIndex := Search.firstQuarterBelow (ReciprocalBoundaryArea.Data.boundaryAreaScale data) 0 areaTarget
  let totalIndex := Search.firstQuarterBelow (UniformReciprocalPrimitives.Data.errorScale data) 0 totalTarget
  let index := max primitive.index (max areaIndex totalIndex)
  exact ⟨primitive, index, Data.Nat.Order.le_max_left _ _,
    (quarterRadius_antitone (ReciprocalBoundaryArea.Data.boundaryAreaScale_nonnegative data)
      ((Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _))).trans_lt
        (Search.firstQuarterBelow_accurate _ (ReciprocalBoundaryArea.Data.boundaryAreaScale_nonnegative data) 0 _
          areaPositive),
    (quarterRadius_antitone (UniformReciprocalPrimitives.Data.errorScale_nonnegative data)
      ((Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _))).trans_lt
        (Search.firstQuarterBelow_accurate _ (UniformReciprocalPrimitives.Data.errorScale_nonnegative data) 0 _
          totalPositive)⟩

variable {sourceTarget reciprocalTarget coefficientTarget areaTarget totalTarget :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- Materialize the retained source and reciprocal cells at the shared stage, then build their full fine paths from
those exact cached primitives. -/
@[expose] def evaluate (plan :
  Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests.CoupledLocalAreaPlan data sourceTarget
  reciprocalTarget coefficientTarget areaTarget totalTarget minimum)
    (cover : UniformReciprocalCover.Cover data) (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (index depth : Nat) (later : plan.index ≤ index) :
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests.CoupledLocalAreaRequest cover sourceTarget
      reciprocalTarget coefficientTarget areaTarget totalTarget minimum depth := by
  let compared := plan.primitive.evaluate cover proper (SourcePrimitive.build data index) (plan.local_le.trans later)
  have accurate : Geometric.Basic.quarterRadius (ReciprocalBoundaryArea.Data.boundaryAreaScale data)
    compared.reciprocal.index < areaTarget :=
    (quarterRadius_antitone (ReciprocalBoundaryArea.Data.boundaryAreaScale_nonnegative data) later).trans_lt
      plan.area_accurate
  let area := Cover.AreaRequest.ofPrimitives cover compared.reciprocal.source compared.reciprocal.cells depth areaTarget
    accurate
  refine ⟨compared, area, rfl, rfl, ?_, ?_, ?_⟩
  · exact area.source_total.trans compared.reciprocal.sourceIncrement_eq.symm
  · exact (AreaCells.build_right_total compared.reciprocal.source depth compared.reciprocal.cells).trans
      compared.reciprocal.reciprocalIncrement_eq.symm
  · rw [compared.reciprocal.error_eq]
    exact (quarterRadius_antitone (UniformReciprocalPrimitives.Data.errorScale_nonnegative data)
      later).trans_lt plan.total_accurate

/-- The materialized original area request uses exactly the supplied shared polynomial stage. -/
theorem evaluate_index (plan :
  Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests.CoupledLocalAreaPlan data sourceTarget
  reciprocalTarget coefficientTarget areaTarget totalTarget minimum)
    (cover : UniformReciprocalCover.Cover data) (proper : parent.edge.left.parameter <
      parent.edge.request.endpoint.parameter)
    (index depth : Nat) (later : plan.index ≤ index) : (plan.evaluate cover proper index depth later).area.index = index
      := rfl

end CoupledLocalAreaPlan

namespace CoupledLocalAreaRequest

/-- Select and materialize the original coupled primitive and area caches at their shared paid stage. -/
@[expose] def build (cover : UniformReciprocalCover.Cover data) (sourceTarget reciprocalTarget coefficientTarget
  areaTarget totalTarget : InverseRootPolynomial.Coordinate)
    (sourcePositive : 0 < sourceTarget) (reciprocalPositive : 0 < reciprocalTarget)
    (coefficientPositive : 0 < coefficientTarget) (areaPositive : 0 < areaTarget) (totalPositive : 0 < totalTarget)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) (minimum depth : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests.CoupledLocalAreaRequest cover sourceTarget
      reciprocalTarget coefficientTarget areaTarget totalTarget minimum depth :=
  let plan := Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests.CoupledLocalAreaPlan.build data
    sourceTarget reciprocalTarget coefficientTarget areaTarget totalTarget
    sourcePositive reciprocalPositive coefficientPositive areaPositive totalPositive minimum
  plan.evaluate cover proper plan.index depth le_rfl

end CoupledLocalAreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
