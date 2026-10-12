module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Topology.Grid.Signs
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Normalization.InverseModelRefinementSigns
public import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Normalization.InverseModelOverlapCocycle
import Purelib.Riemann.Normalization.InverseModelEdgeTransition

/-!
# Reusable rectangular sheet data across accuracy requests

The original finite transition bank and any checked gauge determine all
later polynomial refinements. No new edge comparison or gauge scan is
executed by refinement. In particular, the global sheet at the origin stays
fixed when requesting more accurate primitives or changing their numerator.
-/

@[expose] public section

namespace Purelib.Riemann.Integration.RectangularRefinementSigns

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank Transitions)

variable {polynomial : Polynomial} {columns rows : Nat} {geometry : Geometry columns rows}

namespace Bank

/-- The retained refined rectangular cell is exactly the original cell model refined at the selected depth. -/
theorem refine_model (bank : Bank polynomial geometry) (index : Nat)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) :
    ((bank.refine index).ready column row).model = (bank.ready column row).model.refine index := by
  rw [Bank.refine, Bank.ready_ofFn]
  rfl

open Purelib.Riemann.Normalization
/-- Refining the original bank preserves each adjacent-column alignment sign. -/
theorem refine_horizontal_flip (bank : Bank polynomial geometry) (index : Nat)
    (column : Fin columns) (row : Fin (rows + 1)) :
    ((bank.refine index).horizontalEdge column row).sample.alignment.flip =
      (bank.horizontalEdge column row).sample.alignment.flip := by
  change (OverlapSample.build ((bank.refine index).ready column.castSucc row).model
    ((bank.refine index).ready column.succ row).model (geometry.vertex column.castSucc.succ
      row.castSucc)).alignment.flip = _
  rw [refine_model, refine_model]
  let edge := bank.horizontalEdge column row
  exact InverseModelRefinementSigns.OverlapSample.refine_flip edge.sample edge.leftStart edge.rightStart
    (bank.ready column.castSucc row).small (bank.ready column.succ row).small index index

/-- Refining the original bank preserves each adjacent-row alignment sign. -/
theorem refine_vertical_flip (bank : Bank polynomial geometry) (index : Nat)
    (column : Fin (columns + 1)) (row : Fin rows) :
    ((bank.refine index).verticalEdge column row).sample.alignment.flip =
      (bank.verticalEdge column row).sample.alignment.flip := by
  change (OverlapSample.build ((bank.refine index).ready column row.castSucc).model
    ((bank.refine index).ready column row.succ).model (geometry.vertex column.castSucc
      row.castSucc.succ)).alignment.flip = _
  rw [refine_model, refine_model]
  let edge := bank.verticalEdge column row
  exact InverseModelRefinementSigns.OverlapSample.refine_flip edge.sample edge.leftStart edge.rightStart
    (bank.ready column row.castSucc).small (bank.ready column row.succ).small index index

end Bank

namespace Transitions

variable {bank : Bank polynomial geometry}

open Purelib.Riemann.Integration
/-- Refine the original bank while retaining its exact cached transition signs. -/
def refine (transitions : Transitions bank) (index : Nat) : Transitions (bank.refine index) where
  horizontal := transitions.horizontal
  vertical := transitions.vertical
  horizontal_eq := fun column row => (transitions.horizontal_eq column row).trans
    (RectangularRefinementSigns.Bank.refine_horizontal_flip bank index column row).symm
  vertical_eq := fun column row => (transitions.vertical_eq column row).trans
    (RectangularRefinementSigns.Bank.refine_vertical_flip bank index column row).symm

/-- Refining the retained transitions preserves their exact original flat sign grid. -/
theorem refine_flatGrid (transitions : Transitions bank) (index : Nat) :
    (RectangularRefinementSigns.Transitions.refine transitions index).flatGrid = transitions.flatGrid := rfl

end Transitions

open Purelib in
set_option genInjectivity false in
/-- An original rectangular bank's retained transition signs and gauge on that exact sign grid.

The gauge is indexed by the cached transitions, so later refinement can preserve the same original sheet choices. -/
structure SheetCache (bank : Bank polynomial geometry) where
  /-- The exact original bank's retained transition signs. -/ transitions : Transitions bank
  /-- The retained sheet gauge of those exact cached transitions. -/ gauge : Topology.Grid.Signs.Gauge
    transitions.flatGrid

constructive_injectivity SheetCache

namespace SheetCache

variable {bank : Bank polynomial geometry}

/-- Cache the original rectangular transitions and their gauge with the selected initial sign. -/
def build (bank : Bank polynomial geometry) (initial : Bool := false) : SheetCache bank :=
  let transitions := Transitions.build bank
  ⟨transitions, transitions.gauge initial⟩

open Purelib.Riemann.Integration in
/-- Refine the original cell models while reusing the retained transition signs and exact gauge. -/
def refine (sheets : SheetCache bank) (index : Nat) : SheetCache (bank.refine index) :=
  ⟨RectangularRefinementSigns.Transitions.refine sheets.transitions index, sheets.gauge⟩

/-- Refining the retained sheet cache preserves its exact original gauge-value vector. -/
theorem refine_values (sheets : SheetCache bank) (index : Nat) :
    (sheets.refine index).gauge.values = sheets.gauge.values := rfl

end SheetCache

end Purelib.Riemann.Integration.RectangularRefinementSigns
