module

public import Purelib.RootIsolation.Multiplicity.Circle.Roots.Owners
public import Purelib.Polynomial.Recurrence.Boundary.Hermite.Selected
public import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Map.Ring
import Purelib.Data.List.Reverse
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original boundary coordinates of retained radial root labels

The same original multiplicity input supplies the formal bank and the
geometric inventory. Its retained owner selection supplies the actual
truncated recurrence boundary without any repeated word expansion, filter
or count. These are labelled boundary coordinates; spectral admissibility
requires the separate association with actual root readings.
-/

public section

namespace Purelib.RootIsolation.Multiplicity.Circle.Roots

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (PositiveFamily)
open Dense.Gaussian.Multiplicity.Roots
open Dense.Roots
open Recurrence.Boundary.Hermite (Selected)
open Purelib.Polynomial.Clearance.Circle (Certificate)

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
variable {clearance : Certificate source} {family : PositiveFamily input}

namespace Boundary

/-- The source-derived reading horizon retains every coefficient slot beyond the requested startup rows. -/
@[expose] def horizon (prepared : Prepared input) (rows : Nat) : Nat :=
  rows + prepared.mapped.coeffs.reverse.length

/-- The source-derived horizon counts the same original coefficient slots before their injective scalar map. -/
theorem horizon_eq_source (prepared : Prepared input) (rows : Nat) :
    horizon prepared rows = rows + source.coeffs.length := by
  unfold horizon
  rewrite [Purelib.Data.List.Reverse.length_reverse, prepared.mapped_eq, Dense.Map.map_length]
  rfl

/-- The same retained original mapped polynomial is normalized in its actual final coefficient algebra. -/
theorem mapped_normalized (prepared : Prepared input) : prepared.mapped.normalize = prepared.mapped := by
  rewrite [prepared.mapped_eq]
  exact (Dense.Map.map_normalize _ (Stages.Images.coefficientMap_zero _ rfl)
    (Stages.Images.coefficientMap_injective _ (fun _ _ equal => equal)) source).symm.trans
      (congrArg (Dense.Map.map _) input.sourceNormalized)

/-- The retained mapped source evaluates at zero through the same original composite coefficient map. -/
theorem mapped_constant (prepared : Prepared input) :
    prepared.mapped.eval 0 = Stages.Images.coefficientMap prepared.separation.prepared.stages (source.eval 0) := by
  have same := Dense.Map.map_eval (Stages.Images.coefficientMap prepared.separation.prepared.stages)
    (Stages.Images.coefficientMap_zero _ rfl) (Stages.Images.coefficientMap_add _ (fun _ _ => rfl))
    (Stages.Images.coefficientMap_mul _ (fun _ _ => rfl)) source 0
  rewrite [Stages.Images.coefficientMap_zero _ rfl] at same
  exact (congrArg (fun polynomial => polynomial.eval 0) prepared.mapped_eq).trans same.symm

set_option genInjectivity false in
/-- The actual constant-unit preparation at the original requested startup rows.

Zero rows retain no reciprocal. Positive rows retain one original Gaussian
constant reciprocal and its once-mapped image in the same final algebra;
the original scalar map proves that image is the needed constant unit.
-/
inductive Constant (prepared : Prepared input) : Nat → Type
  /-- Zero startup rows require no source constant or root inverse. -/
  | zero : Constant prepared 0
  /-- Positive rows retain the original Gaussian reciprocal and the same final-algebra image once. -/
  | positive {shift : Nat}
      (coefficientInverse : Canonical) (coefficientInverse_eq : coefficientInverse = (source.eval 0)⁻¹)
      (inverse : prepared.separation.Scalar)
      (inverse_eq : inverse = Stages.Images.coefficientMap prepared.separation.prepared.stages coefficientInverse)
      (unit : prepared.mapped.eval 0 * inverse = 1) : Constant prepared (shift + 1)

constructive_injectivity Constant

namespace Constant

/-- Compute only the reciprocal and coefficient image needed by the actual requested positive rows. -/
@[expose] def prepare (prepared : Prepared input) (rows : Nat)
    (nonzero : 0 < rows → source.eval 0 ≠ 0) : Constant prepared rows :=
  match rows with
  | 0 => .zero
  | shift + 1 =>
      let coefficientInverse := (source.eval 0)⁻¹
      let inverse := Stages.Images.coefficientMap prepared.separation.prepared.stages coefficientInverse
      .positive coefficientInverse rfl inverse rfl (by
        rewrite [mapped_constant]
        exact (Stages.Images.coefficientMap_mul _ (fun _ _ => rfl) (source.eval 0) coefficientInverse).symm.trans
          ((congrArg (Stages.Images.coefficientMap prepared.separation.prepared.stages)
            (Canonical.mul_inv_cancel _ (nonzero (Nat.zero_lt_succ shift)))).trans
              (Stages.Images.coefficientMap_one _ rfl)))

/-- Checked original reciprocal and image caches recover the complete positive-row constant preparation. -/
theorem positive_eq_prepare (prepared : Prepared input) (shift : Nat)
    (nonzero : 0 < shift + 1 → source.eval 0 ≠ 0)
    (coefficientInverse : Canonical) (coefficientInverseEq : coefficientInverse = (source.eval 0)⁻¹)
    (inverse : prepared.separation.Scalar)
    (inverseEq : inverse = Stages.Images.coefficientMap prepared.separation.prepared.stages coefficientInverse)
    (unit : prepared.mapped.eval 0 * inverse = 1) :
    Constant.positive (shift := shift) coefficientInverse coefficientInverseEq inverse inverseEq unit =
      prepare prepared (shift + 1) nonzero := by
  cases coefficientInverseEq
  cases inverseEq
  rfl

/-- Construct the actual original boundary from this same retained constant cache and original selection. -/
@[expose] def select {prepared : Prepared input} {rows : Nat} (constant : Constant prepared rows)
    (selection : Word.Selection prepared.bank) : Selected prepared.bank rows (horizon prepared rows) :=
  match constant with
  | .zero => Selected.ofSelectionZero selection (horizon prepared 0)
  | .positive (shift := shift) _ _ inverse _ unit =>
      Selected.ofSelectionPositive selection (mapped_normalized prepared) shift (horizon prepared (shift + 1))
        (Nat.le_refl _) inverse unit

/-- Both original row branches preserve the complete retained selection unchanged. -/
theorem select_selection {prepared : Prepared input} {rows : Nat} (constant : Constant prepared rows)
    (selection : Word.Selection prepared.bank) : (constant.select selection).selection = selection := by
  cases constant with
  | zero => rfl
  | positive _ _ _ _ _ => exact Selected.ofSelectionPositive_selection _ _ _ _ _ _ _

end Constant
end Boundary

set_option genInjectivity false in
/-- The actual original truncated boundary on the same inventory's retained labelled coordinates.

The same original formal bank and geometric inventory remain correctness
indices through their owner alignment. The actual reading horizon is derived
from the original mapped coefficient table. Its normal form supplies kernel,
image and complement coordinates, independently of any spectral interpretation
of the retained geometric labels.
-/
structure Boundary {prepared : Prepared input} {inventory : PositiveInventory clearance input family}
    (owners : Owners prepared inventory) (rows : Nat) where
  /-- Only positive startup rows require the original Gaussian constant to be nonzero. -/
  constantNonzero : 0 < rows → source.eval 0 ≠ 0
  /-- The actual zero-row branch or once-computed original constant reciprocal and mapped image. -/
  constant : Boundary.Constant prepared rows
  /-- The constant cache is the original procedure at these exact requested rows. -/
  constant_eq : constant = Boundary.Constant.prepare prepared rows constantNonzero
  /-- The actual original selected boundary, including its matrix and computed normal form. -/
  selected : Selected prepared.bank rows (Boundary.horizon prepared rows)
  /-- The same cached selection and same constant cache supply the complete original boundary result. -/
  selected_eq : selected = constant.select owners.selection

constructive_injectivity Boundary

namespace Boundary

variable {prepared : Prepared input} {inventory : PositiveInventory clearance input family}
variable {owners : Owners prepared inventory} {rows : Nat}

/-- Retain checked original constant and boundary caches without repeating either producer. -/
@[expose] def ofSelected (owners : Owners prepared inventory) (rows : Nat)
    (nonzero : 0 < rows → source.eval 0 ≠ 0)
    (constant : Constant prepared rows) (constantEq : constant = Constant.prepare prepared rows nonzero)
    (selected : Selected prepared.bank rows (horizon prepared rows))
    (selectedEq : selected = constant.select owners.selection) : Boundary owners rows :=
  { constantNonzero := nonzero, constant, constant_eq := constantEq, selected, selected_eq := selectedEq }

/-- Construct the actual labelled boundary from the same original retained owner selection.

The zero-row branch accepts true zero roots without any inverse premise.
Positive rows compute one original Gaussian reciprocal and one final-algebra
image, then construct the original boundary at its source-derived horizon.
No word expansion, filter, count, rank or basis is supplied or replayed.
-/
@[expose] def prepare (owners : Owners prepared inventory) (rows : Nat)
    (nonzero : 0 < rows → source.eval 0 ≠ 0) : Boundary owners rows :=
  let constant := Constant.prepare prepared rows nonzero
  let selected := constant.select owners.selection
  ofSelected owners rows nonzero constant rfl selected rfl

/-- Checked retained caches recover the complete same original labelled boundary construction. -/
theorem ofSelected_eq_prepare (owners : Owners prepared inventory) (rows : Nat)
    (nonzero : 0 < rows → source.eval 0 ≠ 0)
    (constant : Constant prepared rows) (constantEq : constant = Constant.prepare prepared rows nonzero)
    (selected : Selected prepared.bank rows (horizon prepared rows))
    (selectedEq : selected = constant.select owners.selection) :
    ofSelected owners rows nonzero constant constantEq selected selectedEq = prepare owners rows nonzero := by
  cases constantEq
  cases selectedEq
  rfl

/-- The actual boundary retains the identical complete original owner selection. -/
theorem selection_eq (boundary : Boundary owners rows) : boundary.selected.selection = owners.selection := by
  rewrite [boundary.selected_eq]
  exact boundary.constant.select_selection owners.selection

/-- The constructed identity-block size follows from the actual normal form and original inside count. -/
theorem rank_eq (boundary : Boundary owners rows) :
    boundary.selected.result.normal.rank = Nat.min rows inventory.insideCount := by
  rewrite [boundary.selected.rank_count, boundary.selection_eq, owners.count_eq]
  rfl

/-- The actual free source-coordinate count is the inside multiplicity left after the constructed identity block. -/
theorem kernel_dimension (boundary : Boundary owners rows) :
    boundary.selected.result.normal.kernelDimension = inventory.insideCount - Nat.min rows inventory.insideCount := by
  change boundary.selected.selection.word.length - boundary.selected.result.normal.rank = _
  rewrite [boundary.rank_eq, boundary.selection_eq, owners.length_eq]
  rfl

/-- The actual complementary target-coordinate count is the requested rows left after the constructed identity block. -/
theorem complement_dimension (boundary : Boundary owners rows) :
    boundary.selected.result.normal.cokernelDimension = rows - Nat.min rows inventory.insideCount := by
  change rows - boundary.selected.result.normal.rank = _
  rewrite [boundary.rank_eq]
  rfl

/-- Actual complementary-target minus kernel coordinates equal rows minus the original weighted inside count.

The normal form supplies both coordinate dimensions before their difference
is read through the retained original selection and independent inventory.
This is a labelled boundary statement; spectral admissibility is separate.
-/
theorem defect_eq (boundary : Boundary owners rows) :
    boundary.selected.result.normal.defect = (rows : Int) - (inventory.insideCount : Int) := by
  rewrite [boundary.selected.defect_count, boundary.selection_eq, owners.count_eq]
  rfl

end Boundary
end Purelib.RootIsolation.Multiplicity.Circle.Roots

end
