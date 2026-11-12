module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedPrimitiveRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedPointRequests
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Paid point-reading requests on one retained entered path

The original domain primitives and numerical point bank travel together
through whole entered-path equality. A finite stage check retains either
the original requested comparison or its actual outstanding grid floor.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {face : RegularFace bank} {models : FaceModels frames face}
variable {ambient : Box} {base finish : Canonical} {path : ClearPath curve.polynomial ambient base finish}
variable {owner : Owner (curve.polynomial.eval base)} {prepared : CoveredTracedPath path owner}
variable {differential : Differential genus} {parentSheet : Fin 2}
variable (entered : EnteredPath models prepared differential parentSheet)
variable (index : Nat) {count : Nat} (points : Fin count → Canonical)

/-- The same original domain primitives and point readings, retaining their dependent numerical owners together. -/
abbrev PointData :=
  Σ data : DomainPrimitives entered.domain differential index, PointReadings data.anchors data.offsets points

/-- Transport both complete numerical caches through equality of the whole original entered path.

Only the dependent type changes. In particular the retained entered path
is not replaced by a factory call in any subsequent executable consumer.
-/
def castPointData {first last : EnteredPath models prepared differential parentSheet} (same : first = last)
    (data : first.PointData index points) : last.PointData index points :=
  Eq.mp (congrArg (fun value => value.PointData index points) same) data

/-- Whole entered-path transport preserves the exact numerical values of the original point bank. -/
theorem castPointData_values {first last : EnteredPath models prepared differential parentSheet} (same : first = last)
    (data : first.PointData index points) : (castPointData index points same data).2.values = data.2.values := by
  cases same
  rfl

namespace PointData

variable {entered index points} (data : entered.PointData index points)
variable {target : Rational} (positive : 0 < target)

section Paid

variable (budget : FragmentAccuracy entered.globalBounds entered.domain.steps
  entered.mesh.splits.pieceCount (target / 4))

/-- Retain the actual requested comparison at a certified sufficient existing primitive stage. -/
abbrev Request (later : budget.grid.index ≤ index) :=
  {value : RequestedFragments entered.mesh entered.bounds entered.globalBounds genus target //
    value = entered.requestShared budget index later data.1}

end Paid

/-- A finite request attempt keeps its original entered path, both numerical caches, actual budget and stopping reason.

Only a sufficient computed grid floor permits new parent requests. A
failed stage check retains that exact outstanding requirement, without
claiming that the old numerical data are globally invalid or unusable.
-/
abbrev RequestAttempt :=
  {value : EnteredPath models prepared differential parentSheet × entered.PointData index points //
    value = (entered, data)} ×
  (Σ budget : {value : FragmentAccuracy entered.globalBounds entered.domain.steps
      entered.mesh.splits.pieceCount (target / 4) //
    value = FragmentAccuracy.build entered.globalBounds entered.domain.steps entered.mesh.splits.pieceCount
      (target / 4) (Field.div_pos_direct positive (of_decide_eq_true rfl))},
  (Σ later : {_value : Unit // budget.val.grid.index ≤ index}, data.Request budget.val later.property) ⊕
    {value : Nat × Nat // value = (budget.val.grid.index, index) ∧ ¬budget.val.grid.index ≤ index})

/-- Compute the actual mesh budget first, then acquire the original same-data request only when its stage is paid.

The existing primitive data are never refined or rebuilt. Successful work
calls requestShared once; an insufficient stage keeps all preparation and
its computed floor for a later explicit refinement decision.
-/
def attempt (target : Rational) (positive : 0 < target) : data.RequestAttempt positive :=
  let budget := FragmentAccuracy.build entered.globalBounds entered.domain.steps entered.mesh.splits.pieceCount
    (target / 4) (Field.div_pos_direct positive (of_decide_eq_true rfl))
  if later : budget.grid.index ≤ index then
    let requested := entered.requestShared budget index later data.1
    (⟨(entered, data), rfl⟩, ⟨⟨budget, rfl⟩, Sum.inl ⟨⟨(), later⟩, ⟨requested, rfl⟩⟩⟩)
  else
    (⟨(entered, data), rfl⟩, ⟨⟨budget, rfl⟩, Sum.inr ⟨(budget.grid.index, index), rfl, later⟩⟩)

namespace Request

variable {data}
variable {budget : FragmentAccuracy entered.globalBounds entered.domain.steps
  entered.mesh.splits.pieceCount (target / 4)} {later : budget.grid.index ≤ index}
variable (requested : data.Request budget later)

/-- The same retained source readings compare to the actual paid source-path primitive sum with the original target.

Both original endpoint incidences remain explicit. The original
requestShared factory proves UsesData internally; no desired analytic
comparison or primitive normalization is supplied as a premise.
-/
theorem accurate (first last : Fin count) (firstEq : points first = base) (lastEq : points last = finish) :
    Norm.Basic.normSq ((data.2.values last - data.2.values first) - requested.val.request.primitiveSum) < target := by
  have shared := entered.requestShared_usesData budget index later data.1
  have retained : entered.UsesData requested.val data.1 :=
    Eq.mpr (congrArg (fun value => entered.UsesData value data.1) requested.property) shared
  exact SharedPointRequests.point_accurate entered requested.val data.1 retained data.2 first last firstEq lastEq

end Request

end PointData

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath

end
