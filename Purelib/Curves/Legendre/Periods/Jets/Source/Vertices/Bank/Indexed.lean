module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Bank
public import Purelib.Data.List.Search.Indexed

/-! # Original vertex readings at finite occurrence keys

A bounded occurrence selects its actual complete old bank entry. The full
physical lifted-point equality is a separate certificate, allowing equal
physical keys to keep different original root owners and observations.
The point-only first-match Found and Position APIs remain unchanged.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Vertex.Bank

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)

variable {parameter : Canonical} {allocation : Rational}

/-- An original bounded bank occurrence at its certified complete physical lifted point.

The retained entry is selected by its original position. Its full point
identity transports the original Vertex and Readings together. This is
not a point-only Found and contains no assertion about that other scan.
-/
@[expose] def FoundAt (bank : Vertex.Bank parameter allocation) (point : LiftedPoint 2)
    (key : Fin bank.length) :=
  {selected : Data.List.Search.At bank key // selected.val.point = point}

/-- Read one original occurrence, using its actual full lifted-point readback.

The same stored Vertex, three requests and readings are retained. No entry,
request, point lookup, owner selection or root observation is executed.
-/
def atPoint (bank : Vertex.Bank parameter allocation) (key : Fin bank.length) (point : LiftedPoint 2)
    (physical : (bank[key.val]'key.isLt).point = point) : FoundAt bank point key :=
  let selected := Data.List.Search.select bank key
  ⟨selected, (congrArg (fun entry : Vertex.Entry parameter allocation => entry.point)
    selected.property).trans physical⟩

namespace FoundAt

variable {bank : Vertex.Bank parameter allocation} {point : LiftedPoint 2} {key : Fin bank.length}

/-- Read the unchanged complete original entry selected at this exact finite occurrence. -/
@[expose] def entry (found : FoundAt bank point key) : Vertex.Entry parameter allocation := found.val.val

/-- The occurrence lookup keeps the complete actual original list value at its supplied key. -/
theorem entry_eq (found : FoundAt bank point key) : found.entry = bank[key.val]'key.isLt :=
  found.val.property

/-- The selected occurrence has the certified original whole physical point, including its local sheet. -/
theorem point_eq (found : FoundAt bank point key) : found.entry.point = point := found.property

/-- Transport the same selected Vertex only along its exact whole original point identity. -/
@[expose] def original (found : FoundAt bank point key) : Vertex parameter point :=
  found.point_eq ▸ found.entry.original

/-- Transport the same three actual requests with their same selected Vertex. -/
@[expose] def readings (found : FoundAt bank point key) : Vertex.Readings found.original allocation := by
  cases found with
  | mk selected physical =>
    cases physical
    exact selected.val.readings

/-- Exact whole-point transport keeps the same complete actual occurrence value.

The key and original entry stay fixed. Only the certified physical point
index changes; no positional lookup or bank operation is repeated.
-/
def castPoint (found : FoundAt bank point key) {replacement : LiftedPoint 2} (equal : point = replacement) :
    FoundAt bank replacement key :=
  ⟨found.val, found.property.trans equal⟩

/-- Change only an equal bounded key while retaining the same complete original selected occurrence. -/
def castKey (found : FoundAt bank point key) {replacement : Fin bank.length} (equal : key = replacement) :
    FoundAt bank point replacement := by
  cases equal
  exact found

/-- An equal-key transport preserves the identical actual retained generator name. -/
private theorem packaged_castKey_name (found : FoundAt bank point key) {replacement : Fin bank.length}
    (equal : key = replacement) :
    (found.castKey equal).original.sample.certificate.value.name =
      found.original.sample.certificate.value.name := by
  cases equal
  rfl

/-- An equal-key transport preserves the identical actual retained generator name. -/
theorem castKey_name (found : FoundAt bank point key) {replacement : Fin bank.length}
    (equal : key = replacement) :
    (found.castKey equal).original.sample.certificate.value.name =
      found.original.sample.certificate.value.name := packaged_castKey_name found equal

/-- Point-index transport preserves the same original selected generator name. -/
private theorem packaged_original_name (found : FoundAt bank point key) :
    found.original.sample.certificate.value.name = found.entry.original.sample.certificate.value.name := by
  cases found with
  | mk selected physical =>
    cases physical
    rfl

/-- Point-index transport preserves the same original selected generator name. -/
theorem original_name (found : FoundAt bank point key) :
    found.original.sample.certificate.value.name = found.entry.original.sample.certificate.value.name :=
  packaged_original_name found

/-- Whole-point transport preserves that identical retained generator name. -/
private theorem packaged_castPoint_name (found : FoundAt bank point key) {replacement : LiftedPoint 2}
    (equal : point = replacement) :
    (found.castPoint equal).original.sample.certificate.value.name =
      found.original.sample.certificate.value.name :=
  (found.castPoint equal).original_name.trans found.original_name.symm

/-- Whole-point transport preserves that identical retained generator name. -/
theorem castPoint_name (found : FoundAt bank point key) {replacement : LiftedPoint 2}
    (equal : point = replacement) :
    (found.castPoint equal).original.sample.certificate.value.name =
      found.original.sample.certificate.value.name := packaged_castPoint_name found equal

end FoundAt

/-- The original zero-channel reading at a bounded occurrence, with no point-only rescan. -/
@[expose] def zeroAt (bank : Vertex.Bank parameter allocation) (key : Fin bank.length) : Canonical :=
  (bank[key.val]'key.isLt).readings.zero.reading.value

/-- The original one-channel reading at that same bounded occurrence. -/
@[expose] def oneAt (bank : Vertex.Bank parameter allocation) (key : Fin bank.length) : Canonical :=
  (bank[key.val]'key.isLt).readings.one.reading.value

/-- The original scalar-channel reading at that same bounded occurrence. -/
@[expose] def scalarAt (bank : Vertex.Bank parameter allocation) (key : Fin bank.length) : Canonical :=
  (bank[key.val]'key.isLt).readings.scalar.reading.value

namespace FoundAt

variable {bank : Vertex.Bank parameter allocation} {point : LiftedPoint 2} {key : Fin bank.length}

/-- The positional zero reading consumes the exact original retained request. -/
theorem zero_eq (found : FoundAt bank point key) : found.readings.zero.reading.value = bank.zeroAt key := by
  cases found with
  | mk selected physical =>
    cases physical
    change selected.val.readings.zero.reading.value = _
    exact congrArg (fun entry : Vertex.Entry parameter allocation => entry.readings.zero.reading.value)
      selected.property

/-- The positional one reading consumes the exact original retained request. -/
theorem one_eq (found : FoundAt bank point key) : found.readings.one.reading.value = bank.oneAt key := by
  cases found with
  | mk selected physical =>
    cases physical
    change selected.val.readings.one.reading.value = _
    exact congrArg (fun entry : Vertex.Entry parameter allocation => entry.readings.one.reading.value)
      selected.property

/-- The positional scalar reading consumes the exact original retained request. -/
theorem scalar_eq (found : FoundAt bank point key) :
    found.readings.scalar.reading.value = bank.scalarAt key := by
  cases found with
  | mk selected physical =>
    cases physical
    change selected.val.readings.scalar.reading.value = _
    exact congrArg (fun entry : Vertex.Entry parameter allocation => entry.readings.scalar.reading.value)
      selected.property

end FoundAt

end Purelib.Curves.Legendre.Periods.Jets.Source.Vertex.Bank

end
