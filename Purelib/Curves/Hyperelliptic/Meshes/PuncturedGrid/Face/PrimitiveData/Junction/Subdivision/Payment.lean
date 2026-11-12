module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Junction.Subdivision.Cells
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Junction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Connections.ContinuedPoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
import Purelib.Data.List.Map

/-! # Checked actual child Entries and paid independent-domain increment drift

Actual Point/Entry/join caches remain input data. Finite sheet checks only
reindex their retained reachability. The original junction pays model and
finish ownership error; the computed opening ownership gap is paid too.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction.Subdivision

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths.RectangularSegmentSplitting
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {leftFace rightFace : RegularFace bank}
variable {leftModels : FaceModels frames leftFace} {rightModels : FaceModels frames rightFace}
variable {leftSheet rightSheet : Fin 2}
variable {leftDomain : PeriodDomain leftModels leftSheet} {rightDomain : PeriodDomain rightModels rightSheet}
variable {differential : Differential genus} {leftIndex rightIndex : Nat}
variable {leftData : DomainPrimitives leftDomain differential leftIndex}
variable {rightData : DomainPrimitives rightDomain differential rightIndex}
variable {ambient : Box} {first last : Canonical} {source : ClearSegment curve.polynomial ambient first last}
variable {leftSize rightSize : Nat} {leftPoints : Fin leftSize → Canonical} {rightPoints : Fin rightSize → Canonical}
variable {leftOld : PointReadings leftData.anchors leftData.offsets leftPoints}
variable {rightOld : PointReadings rightData.anchors rightData.offsets rightPoints}
variable {leftFirst leftLast : Fin leftSize} {rightFirst rightLast : Fin rightSize}
variable {leftFirst_eq : leftPoints leftFirst = first} {leftLast_eq : leftPoints leftLast = last}
variable {rightFirst_eq : rightPoints rightFirst = first} {rightLast_eq : rightPoints rightLast = last}
variable (retained : Subdivision leftData rightData source leftOld rightOld leftFirst leftLast rightFirst rightLast
  leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq)

variable {retained}
variable (child : CommonChild leftDomain.cuts rightDomain.cuts first last retained.common.partition)
variable {child}
variable (cell : Cell retained child)

namespace Cell

include cell in
/-- The retained left original cell proves lower-point containment in its actual old face. -/
theorem left_inside : leftFace.cell.box.Contains (source.pointAt child.1.val.lower) :=
  (leftDomain.patch.cell_refines cell.left.column cell.left.row).contains
    (piece_first_inside (source := source) cell.left child.1.val cell.left_interval)

include cell in
/-- The distinct retained right original cell proves lower-point containment in its actual old face. -/
theorem right_inside : rightFace.cell.box.Contains (source.pointAt child.1.val.lower) :=
  (rightDomain.patch.cell_refines cell.right.column cell.right.row).contains
    (piece_first_inside (source := source) cell.right child.1.val cell.right_interval)

/-- Actual lower-point preparation retains both whole Points, both original Entry acquisitions and their literal join.

No root/Entry equivalence or desired sheet equality is a proof input. The
Entry acquisitions carry their original complete route/frame/selection
factories. The existing join supplies its actual operational comparison.
-/
abbrev LowerData :=
  Entry.JunctionData leftModels rightModels cell.left_inside cell.right_inside

/-- Actual midpoint-owner containment supplies both whole-child model boxes needed by the original junction. -/
theorem end_inside : EndInside leftData rightData cell.leftReadings cell.rightReadings 0 0
    (finish := source.pointAt child.1.val.upper) := by
  have leftOwner := (congrArg (fun value => value.owners 0) cell.left_eq).trans
    (mix_owner_zero leftData retained.left.readings _ _ _ _ _ _ _ _ _)
  have rightOwner := (congrArg (fun value => value.owners 0) cell.right_eq).trans
    (mix_owner_zero rightData retained.right.readings _ _ _ _ _ _ _ _ _)
  change (leftDomain.geometry.box (cell.leftReadings.owners 0).column
    (cell.leftReadings.owners 0).row).Contains _ ∧
    (rightDomain.geometry.box (cell.rightReadings.owners 0).column (cell.rightReadings.owners 0).row).Contains _
  rw [leftOwner, rightOwner]
  exact ⟨piece_last_inside (source := source) cell.left child.1.val cell.left_interval,
    piece_last_inside (source := source) cell.right child.1.val cell.right_interval⟩

variable (lower : LowerData cell)
variable (leftSame : lower.leftAcquired.entry.sheet = leftSheet)
variable (rightSame : lower.rightAcquired.entry.sheet = rightSheet)

/-- The original junction preparation uses actual Entries with checked spelling of their SAME old domain sheets. -/
abbrev Compared :=
  Preparation lower.left.sample lower.right.sample lower.left.inside
    (lower.leftAcquired.entry.withSheet leftSheet leftSame)
    (lower.rightAcquired.entry.withSheet rightSheet rightSame) lower.joined
    leftData rightData cell.leftReadings cell.rightReadings 0 0 rfl rfl cell.end_inside

/-- Run the original junction preparation once on those literal retained Points, Entry reaches and join. -/
def compare : Compared cell lower leftSame rightSame :=
  prepare lower.left.sample lower.right.sample lower.left.inside
    (lower.leftAcquired.entry.withSheet leftSheet leftSame)
    (lower.rightAcquired.entry.withSheet rightSheet rightSame) lower.joined
    leftData rightData cell.leftReadings cell.rightReadings 0 0 rfl rfl cell.end_inside

/-- Retain the original junction/errors factories and the additional computed opening ownership charge. -/
abbrev Ready :=
  Σ compared : {value : Compared cell lower leftSame rightSame // value = compare cell lower leftSame rightSame},
  Σ errors : {value : compared.val.EndpointErrors 2 2 // value = compared.val.endpointErrors 2 2 rfl rfl},
  Σ opening : {value : Canonical // value =
      (cell.leftReadings.values 0 - cell.leftReadings.values 1) -
        (cell.rightReadings.values 0 - cell.rightReadings.values 1)},
    {value : Rational // value = 2 * (errors.val.bound + Norm.Basic.normSq opening.val)}

/-- Prepare the actual finite child comparison and its nonzero opening correction, without upgrading old stages. -/
def ready : Ready cell lower leftSame rightSame :=
  let compared := compare cell lower leftSame rightSame
  let errors := compared.endpointErrors 2 2 rfl rfl
  let opening := (cell.leftReadings.values 0 - cell.leftReadings.values 1) -
    (cell.rightReadings.values 0 - cell.rightReadings.values 1)
  let bound := 2 * (errors.bound + Norm.Basic.normSq opening)
  ⟨⟨compared, rfl⟩, ⟨errors, rfl⟩, ⟨opening, rfl⟩, ⟨bound, rfl⟩⟩

namespace Ready

variable {cell lower leftSame rightSame} (paid : Ready cell lower leftSame rightSame)

/-- Read the one actual retained original junction preparation. -/
abbrev compared : Compared cell lower leftSame rightSame := paid.1.val

/-- Read the SAME original computed finish-owner errors and genuine model charge. -/
abbrev errors : paid.compared.EndpointErrors 2 2 := paid.2.1.val

/-- Read the actual opening ownership discrepancy; it is not assumed zero. -/
abbrev opening : Canonical := paid.2.2.1.val

/-- Read the cached full finite increment allowance. -/
abbrev bound : Rational := paid.2.2.2.val

/-- The actual old-policy increments differ by the computed allowance, including opening and finish ownership errors. -/
theorem increment_le : Norm.Basic.normSq
    ((cell.leftReadings.values 2 - cell.leftReadings.values 1) -
      (cell.rightReadings.values 2 - cell.rightReadings.values 1)) ≤ paid.bound := by
  let middle := (cell.leftReadings.values 2 - cell.leftReadings.values 0) -
    (cell.rightReadings.values 2 - cell.rightReadings.values 0)
  have identity : (cell.leftReadings.values 2 - cell.leftReadings.values 1) -
      (cell.rightReadings.values 2 - cell.rightReadings.values 1) = middle + paid.opening := by
    unfold opening
    rw [paid.2.2.1.property]
    dsimp only [middle]
    ring1
  rw [identity]
  have estimate := Norm.Bounds.normSq_add_le_two middle paid.opening
  have total := estimate.trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct paid.errors.increment_le (Basic.le_refl _))
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2))
  exact total.trans_eq paid.2.2.2.property.symm

/-- Both independent policy banks keep their original cached endpoint values in the actual comparison. -/
theorem policy_increment_le : Norm.Basic.normSq
    ((retained.left.readings.values cell.upper.val.index - retained.left.readings.values cell.lower.val.index) -
      (retained.right.readings.values cell.upper.val.index - retained.right.readings.values cell.lower.val.index)) ≤
      paid.bound := by
  have leftFirst := (congrArg (fun value => value.values 1) cell.left_eq).trans
    (mix_value_one leftData retained.left.readings _ _ _ _ _ _ _ _ _)
  have leftLast := (congrArg (fun value => value.values 2) cell.left_eq).trans
    (mix_value_two leftData retained.left.readings _ _ _ _ _ _ _ _ _)
  have rightFirst := (congrArg (fun value => value.values 1) cell.right_eq).trans
    (mix_value_one rightData retained.right.readings _ _ _ _ _ _ _ _ _)
  have rightLast := (congrArg (fun value => value.values 2) cell.right_eq).trans
    (mix_value_two rightData retained.right.readings _ _ _ _ _ _ _ _ _)
  have original := paid.increment_le
  rw [leftFirst, leftLast, rightFirst, rightLast] at original
  exact original

/-- The original junction payment receives the remaining target after the exact opening charge. -/
abbrev remaining (target : Rational) : Rational := target / 2 - Norm.Basic.normSq paid.opening

/-- Retain the SAME original junction payment/checker factory, without an accuracy assumption. -/
abbrev Payment (target : Rational) :=
  {value : paid.errors.Payment (paid.remaining target) // value = paid.errors.pay (paid.remaining target)}

/-- Check the original model/finish allowance once at the target left by the actual opening charge. -/
def pay (target : Rational) : paid.Payment target := ⟨paid.errors.pay (paid.remaining target), rfl⟩

/-- Actual success of the retained original payment also pays the explicit opening ownership charge. -/
theorem accurate {target : Rational} (sufficient : paid.errors.bound < paid.remaining target) :
    Norm.Basic.normSq
      ((retained.left.readings.values cell.upper.val.index - retained.left.readings.values cell.lower.val.index) -
        (retained.right.readings.values cell.upper.val.index - retained.right.readings.values cell.lower.val.index)) <
      target := by
  apply paid.policy_increment_le.trans_lt
  unfold bound
  rw [paid.2.2.2.property]
  have shifted := Arithmetic.add_lt_add_right_direct sufficient
    (Norm.Basic.normSq paid.opening)
  have reduced : paid.errors.bound + Norm.Basic.normSq paid.opening < target / 2 :=
    shifted.trans_eq (by unfold remaining; ring1)
  have doubled := Arithmetic.mul_lt_mul_of_pos_left_direct
    (of_decide_eq_true rfl : (0 : Rational) < 2) reduced
  exact doubled.trans_eq (by
    have cancel := Field.div_mul_cancel_of_ne target 2
      (of_decide_eq_true rfl : (2 : Rational) ≠ 0)
    exact (show 2 * (target / 2) = (target / 2) * 2 by ring1).trans cancel)

end Ready

/-- The original successful sheet-check payload retains its exact Ready and numerical Payment caches.

This is the existing inner Sigma of Attempt. It names the whole original
payload, including the same checked sheet witnesses and Ready factory law;
no preparation, comparison or payment operation is added.
-/
@[expose] def Prepared (target : Rational) :=
  Σ same : {_value : Unit // lower.leftAcquired.entry.sheet = leftSheet ∧
      lower.rightAcquired.entry.sheet = rightSheet},
  Σ result : {value : Ready cell lower same.property.1 same.property.2 //
      value = ready cell lower same.property.1 same.property.2},
    result.val.Payment target

namespace Prepared

variable {cell lower} {target : Rational} (cached : Prepared cell lower target)

/-- Read the identical retained Ready, with its actual checked sheet witnesses. -/
abbrev ready : Ready cell lower cached.1.property.1 cached.1.property.2 := cached.2.1.val

/-- Read the same complete numerical payment on that original Ready. -/
abbrev payment : cached.ready.Payment target := cached.2.2

end Prepared

/-- A finite child attempt retains the whole cell, actual optional lower caches and both selected sheet indices.

Missing caches request genuine Point/Entry/join preparation. A mismatch
retains the actual caches and failed index condition; it does not declare
the old domain invalid or infer any primitive/root relation.
-/
abbrev Attempt (provided : Option (LowerData cell)) (target : Rational) :=
  {value : Cell retained child × Option (LowerData cell) × Rational // value = (cell, provided, target)} ×
  ((Σ actual : {value : LowerData cell // provided = some value},
      Prepared cell actual.val target ⊕
      {_value : Unit // ¬(actual.val.leftAcquired.entry.sheet = leftSheet ∧
        actual.val.rightAcquired.entry.sheet = rightSheet)}) ⊕ {_value : Unit // provided = none})

/-- Route actual prepared caches through finite index checks and the original junction/payment producer.

No preparation is replayed. Every branch retains the full old numerical
cell and available Point/Entry/join work. The true model charge, both
independent offsets and all opening/finish ownership errors survive.
-/
def attempt (provided : Option (LowerData cell)) (target : Rational) : cell.Attempt provided target :=
  match provided with
  | none => (⟨(cell, none, target), rfl⟩, Sum.inr ⟨(), rfl⟩)
  | some actual =>
    if same : actual.leftAcquired.entry.sheet = leftSheet ∧ actual.rightAcquired.entry.sheet = rightSheet then
      let result := ready cell actual same.1 same.2
      let payment := result.pay target
      (⟨(cell, some actual, target), rfl⟩,
        Sum.inl ⟨⟨actual, rfl⟩, Sum.inl ⟨⟨(), same⟩, ⟨result, rfl⟩, payment⟩⟩)
    else (⟨(cell, some actual, target), rfl⟩, Sum.inl ⟨⟨actual, rfl⟩, Sum.inr ⟨(), same⟩⟩)

namespace Attempt

/-- Read an already successful preparation using the actual supplied attempt and derived source sheets.

The exact original Ready/payment payload is returned. Missing-cache and
mismatched-sheet branches are excluded on abstract original lower data,
without unfolding a concrete Point continuation or executing a factory.
-/
def prepared (initial : LowerData cell) (target : Rational)
    (attempted : Attempt cell (some initial) target)
    (leftSheet_eq : initial.leftAcquired.entry.sheet = leftSheet)
    (rightSheet_eq : initial.rightAcquired.entry.sheet = rightSheet) :
    Σ actual : {value : LowerData cell // some initial = some value}, Prepared cell actual.val target := by
  match attempted.2 with
  | Sum.inr missing => nomatch missing.property
  | Sum.inl acquired =>
    match acquired.2 with
    | Sum.inl ready => exact ⟨acquired.1, ready⟩
    | Sum.inr different =>
      have equal : initial = acquired.1.val := Option.some.inj acquired.1.property
      have left := (congrArg (fun value : LowerData cell => value.leftAcquired.entry.sheet) equal).symm.trans
        leftSheet_eq
      have right := (congrArg (fun value : LowerData cell => value.rightAcquired.entry.sheet) equal).symm.trans
        rightSheet_eq
      exact False.elim (different.property ⟨left, right⟩)

end Attempt

end Cell

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction.Subdivision

end
