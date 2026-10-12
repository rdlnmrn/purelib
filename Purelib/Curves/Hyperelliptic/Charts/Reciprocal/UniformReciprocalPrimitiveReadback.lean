module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedPrimitiveSamples

public section

/-! Common-cover consumers read already sampled reciprocal cells. Reattaching
an equal canonical owner preserves the inverse, coefficient and primitive. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives

open Purelib.Data.List

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
variable {genus count index : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge}

/-- Retain the original inverse, coefficient, primitive and increment while replacing the cell certificate by its equal
canonical owner.

The two cell-model specification equalities identify the same canonical model. The existing inverse refinement,
coefficient, primitive and increment fields are retained, with only their ownership certificates transported. -/
@[expose] def CellPrimitive.reown (retained : UniformReciprocalPrimitives.CellPrimitive data index edge) (cell :
  UniformReciprocalCover.Cell data edge) : UniformReciprocalPrimitives.CellPrimitive data index edge := by
  have modelEq : retained.cell.model = cell.model := retained.cell.model_eq.trans cell.model_eq.symm
  exact ⟨cell, retained.inverse, retained.inverse_eq.trans (congrArg (fun model => model.refine index) modelEq),
    retained.coefficient, fun point => (retained.coefficient_eq point).trans (by rw [modelEq]),
    retained.primitive, retained.increment, retained.increment_eq⟩

set_option genInjectivity false in
/-- The retained primitive cache for one specified original reciprocal cell.

Its equality witness identifies the cached cell exactly, preserving the original inverse refinement and primitive data.
-/
structure CellPrimitive.Readback (cell : UniformReciprocalCover.Cell data edge) (index : Nat) where
  /-- The original retained primitive cache at the specified shared stage and parameter edge. -/ primitive :
    UniformReciprocalPrimitives.CellPrimitive data index edge
  /-- The cached primitive belongs to exactly the requested original cell. -/ cell_eq : primitive.cell = cell

constructive_injectivity CellPrimitive.Readback

/-- Locate the retained owner by its two executable rational endpoints; membership guarantees success, and no inverse
refinement is repeated.

The scan returns the first cached parameter edge whose endpoint values match the requested edge. Equality transports
that original primitive cache, and reownership retains its inverse, coefficient and primitive data for the specified
cell. -/
@[expose] def PrimitiveCells.readCell (cell : UniformReciprocalCover.Cell data edge) :
    {edges : List Subdivision.ParameterEdge} → UniformReciprocalPrimitives.PrimitiveCells data index edges → edge ∈
      edges → Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.CellPrimitive.Readback cell index
  | [], .nil, member => False.elim (List.not_mem_nil member)
  | head :: remaining, .cons retained tail, member =>
    if same : edge.left.parameter = head.left.parameter ∧ edge.right.parameter = head.right.parameter then
      let primitive : UniformReciprocalPrimitives.CellPrimitive data index edge :=
        (Subdivision.ParameterEdge.eq_of_parameters edge head same).symm ▸ retained
      ⟨primitive.reown cell, rfl⟩
    else
      tail.readCell cell (by
        rcases Membership.mem_cons.mp member with equal | member
        · cases equal; exact False.elim (same ⟨rfl, rfl⟩)
        · exact member)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
