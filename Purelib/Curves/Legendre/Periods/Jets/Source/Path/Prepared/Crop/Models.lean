module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query.Rooted
public import Purelib.Curves.Legendre.Periods.Jets.Source.Row.Queries
public import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive.Restriction
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Restriction
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

/-! # Actual restricted source models on the original affine parent

Seven canonical coefficient restrictions keep the original six differential
models and selected primitive row separate. The child retains the original
sheet transport, and each uniform child query transports its one actual
parent observation at the mapped fraction. The original primitive residual
then pays the actual restricted row-cell integral.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformCellCertificate)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
variable {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}
variable (prepared : PreparedParent patch count floor covered targets) (row : Row)
variable (lower upper : Rational)

/-- The child retains the entire original sheet permutation and both original fraction coordinates. -/
def croppedCell : LiftedCell
    (⟨parent.edge.point lower, parent.edge.sheet⟩ : LiftedPoint 2)
    (⟨parent.edge.point upper, parent.edge.sheet⟩ : LiftedPoint 2) where
  sheetTransport := (liftedCell parent).sheetTransport
  finishSheet_eq := (liftedCell parent).finishSheet_eq

/-- Seven caches restrict the six source integrands and original selected row to one subinterval. -/
@[expose] def CroppedModels :=
  DependentVector (fun channel : Fin 6 =>
    Restriction.Cached (prepared.preparation.cell.models.cell channel).polynomial
      (Cast.Path.ofCoordinate lower) (Cast.Path.ofCoordinate upper)) ×
  Restriction.Cached (row.cell prepared.preparation.cell.models).polynomial
    (Cast.Path.ofCoordinate lower) (Cast.Path.ofCoordinate upper)

namespace CroppedModels

/-- Construct every actual child coefficient table once from the unchanged retained source models. -/
def build : CroppedModels prepared row lower upper :=
  let channels := DependentVector.ofFn (fun channel : Fin 6 =>
    Restriction.Cached.canonical (prepared.preparation.cell.models.cell channel).polynomial
      (Cast.Path.ofCoordinate lower) (Cast.Path.ofCoordinate upper))
  let relation := Restriction.Cached.canonical (row.cell prepared.preparation.cell.models).polynomial
    (Cast.Path.ofCoordinate lower) (Cast.Path.ofCoordinate upper)
  ⟨channels, relation⟩

variable {prepared row lower upper}
variable (cropped : CroppedModels prepared row lower upper)

/-- Read the same actual cached restriction of a differential's original retained polynomial table. -/
abbrev channelCache (channel : Fin 6) := cropped.1.get channel

/-- Read the independent retained coefficient restriction of the original selected primitive row. -/
abbrev rowCache := cropped.2

/-- The actual child differential model reads its retained cache and keeps the original paid local allowance. -/
abbrev cell (channel : Fin 6) :=
  Cell.Restriction.model (prepared.preparation.cell.models.cell channel) (cropped.channelCache channel)

/-- The actual child row model reads the separately retained original relation-polynomial restriction. -/
abbrev relation := Cell.Restriction.model (row.cell prepared.preparation.cell.models) cropped.rowCache

/-- Each restricted differential starts at the same actual original lower parent fraction. -/
theorem cell_start (channel : Fin 6) : (cropped.cell channel).start = parent.edge.point lower :=
  (prepared.preparation.cell.models.cell_point channel lower).trans (prepared.queryPoint_eq lower)

/-- Each restricted differential finishes at the same original upper fraction, preserving its orientation. -/
theorem cell_finish (channel : Fin 6) : (cropped.cell channel).finish = parent.edge.point upper :=
  (prepared.preparation.cell.models.cell_point channel upper).trans (prepared.queryPoint_eq upper)

/-- The actual restricted model reads the original prepared parent at the exact mapped child fraction. -/
theorem cell_point (channel : Fin 6) (input : Rational) :
    (cropped.cell channel).point input = parent.edge.point (Cell.Restriction.parameter lower upper input) :=
  (Cell.Restriction.point_eq (prepared.preparation.cell.models.cell channel) (cropped.channelCache channel) input).trans
    ((prepared.preparation.cell.models.cell_point channel (Cell.Restriction.parameter lower upper input)).trans
      (prepared.queryPoint_eq (Cell.Restriction.parameter lower upper input)))

/-- The restricted row has the same source endpoint as its six retained differential restrictions. -/
theorem relation_start : cropped.relation.start = parent.edge.point lower :=
  (row.cell_point prepared.preparation.cell.models lower).trans (prepared.queryPoint_eq lower)

/-- The restricted row has the same actual target endpoint as the six original source differential restrictions. -/
theorem relation_finish : cropped.relation.finish = parent.edge.point upper :=
  (row.cell_point prepared.preparation.cell.models upper).trans (prepared.queryPoint_eq upper)

/-- The retained original query family supplies all six genuine uniform integrand certificates on the actual child.

The child-indexed producer supplies one retained parent bundle at
lower+t*(upper-lower). It can preserve the two endpoint roles independently.
The existing restriction operation retains that observation's full sheet value,
interpretation, reading state, residual and original allowance. No old
strict-fraction Vertex or new source preparation is used.
-/
def certificates
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (queries : (input : Rational) → (inside : 0 ≤ input ∧ input ≤ 1) →
      RootedQuery (frame := frame) prepared (Cell.Restriction.parameter lower upper input)
        (Cell.Restriction.parameter_inside lowerInside upperInside inside)) :
    DependentVector (fun channel : Fin 6 =>
      UniformCellCertificate (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (croppedCell (frame := frame) (parent := parent) lower upper) (cropped.cell channel)) :=
  DependentVector.ofFn (fun channel =>
    { query := fun input first last =>
        let retained := queries input ⟨first, last⟩
        (retained.observed.channel channel).restrict
          (lifted := liftedCell parent)
          (croppedCell (frame := frame) (parent := parent) lower upper) (cropped.channelCache channel) rfl })

/-- The SAME original primitive residual derives the finite integral remainder for the actual restricted row model. -/
theorem primitive_error_le
    (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1) :
    Norm.Basic.normSq
      ((row.spatial prepared.preparation.cell.request.models).eval
        (prepared.preparation.cell.models.coordinate.point upper) -
       (row.spatial prepared.preparation.cell.request.models).eval
        (prepared.preparation.cell.models.coordinate.point lower) - cropped.relation.integralSample) ≤
      2 * prepared.preparation.cell.primitives.bound * (upper - lower) ^ 2 := by
  have actual := (row.primitive prepared.preparation.cell.primitives).restricted_integral_error_le
    cropped.rowCache lowerInside upperInside
  rewrite [row.primitive_eval prepared.preparation.cell.primitives upper,
    row.primitive_eval prepared.preparation.cell.primitives lower,
    row.bound_eq prepared.preparation.cell.primitives] at actual
  exact actual

end CroppedModels

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
