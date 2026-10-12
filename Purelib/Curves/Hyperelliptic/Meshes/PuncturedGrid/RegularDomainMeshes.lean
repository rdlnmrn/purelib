module
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearBoundary
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Tactic.QuotientFreeOmega

section

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-! Whole-face refining meshes on every retained regular face. Unlike an
observation selection, the index bank includes every supplied face position. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List (Meshes.PuncturedGridFaces.RegularFace
      bank)}

set_option genInjectivity false in
/-- Whole-face meshes indexed by every original retained face on the selected sheet.

Each bounded face position reads its own domain and retained observation
mesh. The dependent vector keeps those nominal face and sheet owners. -/
structure RegularMeshes (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces)
  (sheet : Fin 2) where
  /-- The actual dependent observation mesh for each original retained regular-face position. -/ entries :
    Data.Vector.DependentVector (fun position : Fin faces.length =>
    Meshes.RectangularObservationMesh.ObservationMesh ((domains.get position).domain sheet).cuts
      faces[position.val].cell.box)

constructive_injectivity RegularMeshes

namespace RegularMeshes

variable {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces} {sheet : Fin 2}

set_option genInjectivity false in
/-- One finite cut bank covers every face and both sheet occurrences.

The ordered list contains every rectangle-cut point at each bounded face
and sheet index, retaining the original points and containment witnesses. -/
structure CommonCuts (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces) where
  /-- The retained common finite point list covering all original face and sheet rectangle cuts. -/ points : List
    Gaussian.Basic.Canonical
  /-- Every actual rectangle-cut point of either original sheet occurs in the retained common list. -/ includes : ∀
    (position : Fin faces.length) (sheet : Fin 2) point,
    point ∈ ((domains.get position).domain sheet).cuts.rectanglePoints faces[position.val].cell.box → point ∈ points

constructive_injectivity CommonCuts

/-- Collect the complete original rectangle-cut points of every retained face and both sheets. -/
@[expose] def CommonCuts.build (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
  faces) : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains :=
  let points := (List.ofFn (fun position : Fin faces.length => position)).flatMap fun position =>
    (List.ofFn (fun sheet : Fin 2 => sheet)).flatMap fun sheet =>
      ((domains.get position).domain sheet).cuts.rectanglePoints faces[position.val].cell.box
  ⟨points, fun position sheet point member => Data.List.Flatten.mem_flatMap.mpr
    ⟨position, Data.List.OfFn.Basic.mem_ofFn.mpr ⟨position, rfl⟩, Data.List.Flatten.mem_flatMap.mpr
      ⟨sheet, Data.List.OfFn.Basic.mem_ofFn.mpr ⟨sheet, rfl⟩, member⟩⟩⟩

/-- Construct every original whole-face mesh using one retained common cut bank and the supplied finite depth. -/
@[expose] def build (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces) (cuts :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains) (sheet : Fin 2) (depth : Nat)
  : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet :=
  ⟨Data.Vector.DependentVector.ofFn fun position => Meshes.RectangularObservationMesh.ObservationMesh.build
    ((domains.get position).domain sheet).cuts faces[position.val].cell.box faces[position.val].cell.box_proper
    (fun _ inside => ((domains.get position).domain sheet).covers inside)
    cuts.points (cuts.includes position sheet) depth⟩

/-- Each original constructed face mesh uses exactly the retained common point list. -/
theorem build_points (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces) (cuts :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains)
    (sheet : Fin 2) (depth : Nat) (position : Fin faces.length) :
    ((Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet depth).entries.get
      position).points = cuts.points := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build]
  rw [Data.Vector.DependentVector.ofFn_get]
  rfl

/-- Read the original constructed x intervals from the retained face bounds and common real-coordinate cuts. -/
theorem build_x_intervals (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces)
  (cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains)
    (sheet : Fin 2) (depth : Nat) (position : Fin faces.length) :
    ((Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet depth).entries.get
      position).partition.x.intervals =
      (Geometry.Rectangle.AxisPartition.build faces[position.val].cell.box.xLower
        faces[position.val].cell.box.xUpper
        faces[position.val].cell.box_proper.1 (cuts.points.map (fun point => point.re))).intervals := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build]
  rw [Data.Vector.DependentVector.ofFn_get]
  rfl

/-- Read the original constructed y intervals from the retained face bounds and common imaginary-coordinate cuts. -/
theorem build_y_intervals (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces)
  (cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains)
    (sheet : Fin 2) (depth : Nat) (position : Fin faces.length) :
    ((Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet depth).entries.get
      position).partition.y.intervals =
      (Geometry.Rectangle.AxisPartition.build faces[position.val].cell.box.yLower
        faces[position.val].cell.box.yUpper
        faces[position.val].cell.box_proper.2 (cuts.points.map (fun point => point.im))).intervals := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build]
  rw [Data.Vector.DependentVector.ofFn_get]
  rfl

/-- Equal original axis endpoints and the same cuts produce exactly equal finite interval lists. -/
private theorem axis_intervals_eq {firstLower firstUpper lastLower lastUpper : Fraction.Rational}
    (firstProper : firstLower < firstUpper) (lastProper : lastLower < lastUpper)
    (lowerEq : firstLower = lastLower) (upperEq : firstUpper = lastUpper) (cuts : List Fraction.Rational) :
    (Geometry.Rectangle.AxisPartition.build firstLower firstUpper firstProper cuts).intervals =
      (Geometry.Rectangle.AxisPartition.build lastLower lastUpper lastProper cuts).intervals := by
  cases lowerEq
  cases upperEq
  rfl

/-- Original faces with equal horizontal bounds retain equal x interval lists across independent sheets and depths. -/
theorem build_x_compatible (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces)
  (cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains)
    (firstSheet lastSheet : Fin 2) (firstDepth lastDepth : Nat) (first last : Fin faces.length)
    (lowerEq : faces[first.val].cell.box.xLower = faces[last.val].cell.box.xLower)
    (upperEq : faces[first.val].cell.box.xUpper = faces[last.val].cell.box.xUpper) :
    ((Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts firstSheet
      firstDepth).entries.get first).partition.x.intervals =
      ((Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts lastSheet
        lastDepth).entries.get last).partition.x.intervals := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build_x_intervals,
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build_x_intervals]
  exact Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.axis_intervals_eq _ _ lowerEq upperEq _

/-- Original faces with equal vertical bounds retain equal y interval lists across independent sheets and depths. -/
theorem build_y_compatible (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces)
  (cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains)
    (firstSheet lastSheet : Fin 2) (firstDepth lastDepth : Nat) (first last : Fin faces.length)
    (lowerEq : faces[first.val].cell.box.yLower = faces[last.val].cell.box.yLower)
    (upperEq : faces[first.val].cell.box.yUpper = faces[last.val].cell.box.yUpper) :
    ((Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts firstSheet
      firstDepth).entries.get first).partition.y.intervals =
      ((Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts lastSheet
        lastDepth).entries.get last).partition.y.intervals := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build_y_intervals,
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build_y_intervals]
  exact Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.axis_intervals_eq _ _ lowerEq upperEq _

/-- The dependent bank of deferred energy preparations for every original retained face domain. -/
abbrev Preflights (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces) (sheet :
  Fin 2) :=
  Data.Vector.DependentVector (fun position : Fin faces.length => Thunk
    (Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight ((domains.get position).domain sheet)))

/-- Store one deferred original energy preparation for every retained face and selected sheet. -/
@[expose] def preflights (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces)
  (sheet : Fin 2) : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet :=
  Data.Vector.DependentVector.ofFn fun position => ⟨fun _ =>
    Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds.EnergyPreflight.build ((domains.get position).domain sheet)⟩

/-- The original dependent primitive bank for every standard differential at one retained stage. -/
abbrev Numerics (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces) (stage :
  Nat) :=
  Data.Vector.DependentVector (fun row : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (Periods.PeriodMatrix.standardDifferential
    row) stage domains)

/-- Read the original cached standard-differential data at the supplied face position and sheet. -/
@[expose] def Numerics.atDomain {stage : Nat} (cache :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage) (position : Fin
  faces.length) (sheet : Fin 2)
    (row : Fin genus) : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives ((domains.get
      position).domain sheet) (Periods.PeriodMatrix.standardDifferential row) stage :=
  ((cache.get row).get position).atSheet sheet

set_option genInjectivity false in
/-- The original basis readings of every retained whole-face mesh from one actual numerical bank.

Each mesh occurrence reads the same indexed numerical bank. Its dependent
entry preserves the original domain, sheet and cached basis values. -/
structure Samples (meshes : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet) {stage :
  Nat} (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage) where
  /-- The original dependent basis readings for the exact retained face meshes and numerical bank. -/ readings :
    Data.Vector.DependentVector (fun position : Fin faces.length =>
    Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings (cache.atDomain position sheet)
      (meshes.entries.get position).surface)

constructive_injectivity Samples

/-- Construct all retained face-basis readings from the supplied original numerical bank. -/
@[expose] def Samples.ofNumerics (meshes : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains
  sheet) {stage : Nat} (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage) :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Samples meshes cache :=
  ⟨Data.Vector.DependentVector.ofFn fun position =>
    Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings.build
    (cache.atDomain position sheet) (meshes.entries.get position).surface⟩

set_option genInjectivity false in
/-- Count-paid energy requests for every original whole-face mesh.

Retain the original per-face preparations and a stage sufficient for every actual model request. -/
structure Request (coarse : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet) (fixed :
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet) (target :
  Fraction.Rational) where
  /-- The retained energy allowance paid separately for each original face. -/ perFace : Fraction.Rational
  /-- The original per-face energy allowance is strictly positive. -/ positive : 0 < perFace
  /-- The original face count times the retained allowance is strictly below the requested total. -/ paid :
    (faces.length : Fraction.Rational) * perFace < target
  /-- The actual dependent original energy requests for all retained coarse face meshes. -/ entries :
    Data.Vector.DependentVector (fun position : Fin faces.length =>
    Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest (fixed.get position).get (coarse.entries.get
      position) perFace)
  /-- The shared sufficient numerical stage for every original face model request. -/ index : Nat
  /-- Every actual retained model-request stage is at most the original common floor. -/ index_ge : ∀ position,
    (entries.get position).modelRequest.index ≤ index

constructive_injectivity Request

namespace Request

variable {coarse : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet}
  {fixed : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
  {target : Fraction.Rational}

/-- Prepare the original per-face energy requests at a count-paid positive allowance and retain their maximum model
stage. -/
@[expose] def build (coarse : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet) (fixed
  : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet)
    (target : Fraction.Rational) (positive : 0 < target) :
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request coarse fixed target := by
  let count := Rational.Budget.Aggregate.countCoordinate faces.length
  have countEq : count = (faces.length : Fraction.Rational) := Rational.Budget.Aggregate.countCoordinate_eq _
  have countNonnegative : 0 ≤ count :=
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le faces.length)).trans_eq countEq.symm
  let perFace := Rational.Budget.Weighted.allowance target count
  have perFacePositive : 0 < perFace := Rational.Budget.Weighted.allowance_positive positive countNonnegative
  let entries := Data.Vector.DependentVector.ofFn fun position =>
    Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest.build (fixed.get position).get
      (coarse.entries.get position) perFace perFacePositive
  refine ⟨perFace, perFacePositive, ?_, entries,
    entries.maximum (fun _ request => request.modelRequest.index),
    entries.get_le_maximum (fun _ request => request.modelRequest.index)⟩
  rw [← countEq]
  have strict := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    (Fraction.Order.Arithmetic.add_lt_add_left_direct (by decide : (0 : Fraction.Rational) < 1) count) perFacePositive
  rw [show count + 0 = count by ring1] at strict
  apply strict.trans_eq
  change (count + 1) * (target / (count + 1)) = target
  rw [Fraction.Field.mul_comm]
  exact Fraction.Field.div_mul_cancel_of_ne _ _
    (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct countNonnegative (by decide)).ne'

/-- Reuse the retained per-face budgets at one common spatial depth, then
select a numerical index covering all newly required owner-reading errors. -/
@[expose] def atDepth (request : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request coarse
  fixed target) (depth : Nat)
    (later : ∀ position, (request.entries.get position).depth ≤ depth) :
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request coarse fixed target :=
  let entries := Data.Vector.DependentVector.ofFn fun position =>
    (request.entries.get position).refineDepth depth (later position)
  let maximum := entries.maximum (fun _ entry => entry.modelRequest.index)
  { request with
    entries := entries
    index := max request.index maximum
    index_ge := fun position => (entries.get_le_maximum (fun _ entry => entry.modelRequest.index) position).trans
      (Data.Nat.Order.le_max_right _ _) }

/-- Refining to a common depth sets every retained original face request to exactly that depth. -/
theorem atDepth_entry_depth (request : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request
  coarse fixed target) (depth : Nat)
    (later : ∀ position, (request.entries.get position).depth ≤ depth) (position : Fin faces.length) :
    ((request.atDepth depth later).entries.get position).depth = depth := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request.atDepth]
  rw [Data.Vector.DependentVector.ofFn_get]
  rfl

/-- Read the actual refined face meshes retained by the original energy request bank. -/
@[expose] def meshes (request : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request coarse
  fixed target) : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet :=
  ⟨Data.Vector.DependentVector.ofFn fun position => (request.entries.get position).mesh⟩

/-- Indexed lookup in the retained mesh bank returns the exact corresponding original request mesh. -/
theorem mesh_eq (request : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request coarse fixed
  target) (position : Fin faces.length) :
    request.meshes.entries.get position = (request.entries.get position).mesh := Data.Vector.DependentVector.ofFn_get _
      position

/-- Refine the original selected face request to the supplied stage above the retained shared floor. -/
@[expose] def atStage (request : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request coarse
  fixed target) (stage : Nat) (later : request.index ≤ stage)
    (position : Fin faces.length) :=
  (request.entries.get position).refineIndex stage ((request.index_ge position).trans later)

end Request
end RegularMeshes
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

end
