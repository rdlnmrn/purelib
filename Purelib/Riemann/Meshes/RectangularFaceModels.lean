module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Riemann.Branches.RectangularSheetGauge

import Purelib.Topology.Grid.Signs
public import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
public import Purelib.Riemann.Integration.RectangularRefinementSigns
public import Purelib.Riemann.Normalization.TransportedFaceInverseModels
public import Purelib.Riemann.Normalization.InverseRootComparison

public section

/-!
# Acquired rectangular model banks on cleared faces

A face's existing spatial budget constructs adjacent rectangles. Each cell
transports the retained source owner, caches its seed and polynomial, and
enters the rectangular overlap gauge after two fixed Newton steps. No
per-cell smallness, transition-flatness or successful-search input is needed.

Generated cuts, traces, seeds, model caches and gauge bits may supply the same
semantic interfaces. The gauge is fixed at the source corner and reused at
every later accuracy. Identifying the resulting interior sheet with the
global period boundary still requires the operational continuation comparison.
-/

namespace Purelib.Riemann.Meshes.RectangularFaceModels

open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.RectangularInverseModels
open Purelib.Riemann.Normalization.RegularFaceInverseModels
  (Clearance Bounds Mesh CellGeometry)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Normalization.InverseModelOverlapCocycle.InverseRootPolynomial (OverlapReady)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
open Purelib.Riemann.Integration.RectangularRefinementSigns (SheetCache)
open _root_.Purelib.Data (Vector)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {polynomial : Polynomial} {box : Box} {clearance : Clearance polynomial box}
  {bounds : Bounds clearance} {columns rows : Nat} {geometry : Geometry columns rows}

/-- Certified local geometry for every cell of a rectangular model layout.

Each cell retains refinement into the cleared face and the spatial bound required by the same face budget; equality to a
canonical dyadic list is unnecessary. -/
structure RectangularLayout (bounds : Bounds clearance) (geometry : Geometry columns rows) where
  /-- The exact local geometric certificate for every rectangular cell. -/ cells : ∀ column row, CellGeometry bounds
    (geometry.box column row)

namespace RectangularLayout

open Purelib.Geometry in
/-- The retained face depth supplies a valid uniform rectangular layout.

Properness of the face box and the existing spatial budget prove refinement and smallness for every dyadic rectangle. -/
theorem ofMesh (mesh : Mesh bounds) (proper : box.Proper) :
    RectangularLayout bounds (Geometry.Rectangle.Partition.RectangularUniformGeometry.uniform box proper
      (Geometry.Rectangle.Partition.RectangularUniformGeometry.dyadicSteps mesh.depth)) where
  cells := fun column row =>
    ⟨Geometry.Rectangle.Partition.RectangularUniformGeometry.uniform_refines box proper _ column row,
      (Geometry.Rectangle.Partition.RectangularUniformGeometry.uniform_dyadic_diagonalSq box proper mesh.depth column
        row).trans_le mesh.small⟩

end RectangularLayout

set_option genInjectivity false in
/-- A cell box paired with its retained transported inverse-root data.

The cell shares the supplied source owner and face bounds, allowing dependent cells to be stored in a structural vector.
-/
structure CachedTransportedCell (bounds : Bounds clearance) (source : Owner (polynomial.eval box.anchor)) where
  /-- The retained local model box. -/ box : Box
  /-- The transported inverse-root cell at this exact box. -/ cell : TransportedCell bounds source box

constructive_injectivity CachedTransportedCell

open Purelib.Data in
set_option genInjectivity false in
/-- A structural rectangular bank of transported inverse-root cells.

Every cache shares one source owner and retains its exact box equality to the supplied layout. -/
structure TransportedBank (bounds : Bounds clearance) (source : Owner (polynomial.eval box.anchor))
    (geometry : Geometry columns rows) where
  /-- The nested structural vector of cached boxes and transported cells. -/ cells : Data.Vector
    (Data.Vector (CachedTransportedCell bounds source) (rows + 1)) (columns + 1)
  /-- Each cached box is exactly its corresponding geometric layout box. -/ box_eq : ∀ column row, (cells column
    row).box = geometry.box column row

constructive_injectivity TransportedBank

namespace TransportedBank

variable {source : Owner (polynomial.eval box.anchor)}

/-- Read a cached transported cell at its exact geometric box using the retained equality.

The stored box equality transports the same dependent cell to the displayed
layout box, preserving its source owner and cached model. -/
@[expose] def cell (bank : TransportedBank bounds source geometry) (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    TransportedCell bounds source (geometry.box column row) :=
  (bank.box_eq column row) ▸ (bank.cells column row).cell

section
open Purelib.Data
/-- Materialize a dependent family of transported cells into a structural rectangular cache.

The nested vectors retain every supplied cell and its exact layout box.
Their readback certificates use the original column and row bounds. -/
@[expose] def ofFn (cells : ∀ column row, TransportedCell bounds source (geometry.box column row)) :
    TransportedBank bounds source geometry where
  cells := Vector.Basic.vectorOfFn fun column => Vector.Basic.vectorOfFn fun row => ⟨geometry.box column row, cells
    column row⟩
  box_eq := fun column row => by rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]

/-- Reading a materialized cell returns the original supplied dependent entry.

Vector readback identifies the retained record, and its box equality
transports that same dependent cell without rebuilding the model. -/
theorem cell_ofFn (cells : ∀ column row, TransportedCell bounds source (geometry.box column row))
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) : (ofFn cells).cell column row = cells column row := by
  have cast_eq (entry : CachedTransportedCell bounds source) (boxEq : entry.box = geometry.box column row)
      (equal : entry = ⟨geometry.box column row, cells column row⟩) : boxEq ▸ entry.cell = cells column row := by
    cases equal
    rfl
  apply cast_eq
  change Vector.Basic.vectorOfFn (fun column => Vector.Basic.vectorOfFn fun row =>
    (⟨geometry.box column row, cells column row⟩ : CachedTransportedCell bounds source)) column row = _
  rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]

end

/-- Acquire each layout cell from the same source owner and retain the complete bank.

Every column and row uses its supplied local geometry and the common
source owner; the materializer caches the resulting transported cells. -/
@[expose] def acquire (layout : RectangularLayout bounds geometry) (source : Owner (polynomial.eval box.anchor)) :
    TransportedBank bounds source geometry :=
  ofFn fun column row => TransportedCell.acquire (layout.cells column row) source

end TransportedBank

set_option genInjectivity false in
/-- A transported model bank with one retained sheet gauge and its original source sign.

The analytic models agree pointwise with two refinements of their transported cells; the gauge remains anchored to false
at the origin. -/
structure RectangularPatch (bounds : Bounds clearance) (source : Owner (polynomial.eval box.anchor))
    (geometry : Geometry columns rows) where
  /-- The retained bank of cells transported from the original source owner. -/ transported : TransportedBank bounds
    source geometry
  /-- The cached analytic inverse-root model bank. -/ models : Bank polynomial geometry
  /-- Each analytic model agrees pointwise with two refinements of its transported cell. -/ value_eq : ∀ column row
    point, (models.ready column row).model.value.eval point =
    ((transported.cell column row).model.refine 2).value.eval point
  /-- The retained sheet-transition cache for the analytic model bank. -/ sheets : SheetCache models
  /-- The selected gauge sign at the source corner is false. -/ origin : sheets.gauge.values 0 0 = false

constructive_injectivity RectangularPatch

namespace RectangularPatch

variable {source : Owner (polynomial.eval box.anchor)}

open Purelib.Topology in
/-- Build the analytic bank and source-anchored sheet gauge from retained transported cells.

Each cell is refined twice for the overlap budget; all gauge choices are computed once from those models. -/
@[expose] def ofTransported (transported : TransportedBank bounds source geometry) : RectangularPatch bounds source
  geometry :=
  let models := Bank.ofFn fun column row => TransportedFaceInverseModels.TransportedCell.overlapReady (transported.cell
    column row)
  let sheets := SheetCache.build models false
  { transported := transported
    models := models
    value_eq := fun column row _ => by rw [Bank.ready_ofFn]; rfl
    sheets := sheets
    origin := Grid.Signs.Gauge.build_origin _ false }

/-- Acquire the transported layout and retain its analytic models and source-anchored gauge.

The patch reuses the acquired transported bank. Its analytic models and
sheet cache share the same source-anchored gauge. -/
@[expose] def acquire (layout : RectangularLayout bounds geometry) (source : Owner (polynomial.eval box.anchor)) :
    RectangularPatch bounds source geometry := ofTransported (TransportedBank.acquire layout source)

/-- Each retained patch cell refines the original cleared face box. -/
theorem cell_refines (patch : RectangularPatch bounds source geometry) (column row) :
    (geometry.box column row).Refines box := (patch.transported.cell column row).geometry.refines

/-- Later model refinement preserves the selected source-corner sign. -/
theorem refine_origin (patch : RectangularPatch bounds source geometry) (index : Nat) :
    (patch.sheets.refine index).gauge.values 0 0 = false := patch.origin

/-- Refining twice and then further equals refinement by the summed index.

Structural induction retains the same model and its Newton step at every
additional index, without comparing unrelated model caches. -/
private theorem refine_twice {inner : Box} (model : Model polynomial inner) (index : Nat) :
    (model.refine 2).refine index = model.refine (2 + index) := by
  induction index with
  | zero => rfl
  | succ index ih => rw [Model.refine, ih]; rfl

open Purelib.Riemann in
/-- Refined analytic model values agree with the retained transported models at the combined index.

Only the pointwise cache equation is required; the statement preserves the same cell, point and source-owned model. -/
theorem refine_value (patch : RectangularPatch bounds source geometry) (index : Nat)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (point : Gaussian) :
    ((patch.models.refine index).ready column row).model.value.eval point =
      ((patch.transported.cell column row).model.refine (index + 2)).value.eval point := by
  rw [Integration.RectangularRefinementSigns.Bank.refine_model, Model.refine_eval_eq _ _ _ (patch.value_eq column row
    point) index,
    refine_twice, Nat.add_comm 2 index]

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Bound the source-corner mismatch for the retained oriented inverse-root model.

The root lies in the original transported seed box and has the stated small relative squared residual. The source sign
remains fixed, giving the refined geometric error plus sixteen root-error charges. -/
theorem origin_mismatch (patch : RectangularPatch bounds source geometry)
    (root : Gaussian)
    (inside : (patch.transported.cell 0 0).aligned.seed.owner.track.initial.box.Contains root)
    {rootError : Coordinate} (nonnegative : 0 ≤ rootError) (small : rootError ≤ 1 / 4096)
    (residual : Data.Gaussian.Norm.Basic.normSq (root ^ 2 - polynomial.eval (geometry.box 0 0).anchor) ≤
      rootError * Data.Gaussian.Norm.Basic.normSq (polynomial.eval (geometry.box 0 0).anchor)) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (1 - root * ((Branches.RectangularSheetGauge.Transitions.oriented
      (patch.sheets.refine index).transitions (patch.sheets.refine index).gauge).ready 0 0).model.value.eval
        (geometry.box 0 0).anchor) ≤
      Rational.Geometric.Basic.quarterRadius (1 / 256) (2 + index) + 16 * rootError := by
  rw [Branches.RectangularSheetGauge.Transitions.oriented, Branches.RectangularSheetGauge.Bank.orient_value,
    patch.refine_origin]
  change Data.Gaussian.Norm.Basic.normSq (1 - root * ((patch.models.refine index).ready 0 0).model.value.eval _) ≤ _
  rw [patch.refine_value, Nat.add_comm index 2]
  exact (patch.transported.cell 0 0).refine_anchor_mismatch root inside nonnegative small residual (2 + index)

end RectangularPatch

end Purelib.Riemann.Meshes.RectangularFaceModels
