module

public import Purelib.Data.Presentation
public import Purelib.Approximation.Rational.Pi.Source
public import Purelib.Integration.Cell.Source
public import Purelib.Integration.Cell.Source.Comparison.Split
public import Purelib.Integration.Partition.Unit.Presentation
import Purelib.Integration.Partition.Unit.Check
public import Purelib.Approximation.AccuracyRequest.Presentation
import Purelib.Data.List.Map

namespace Purelib.Approximation.Rational.Pi.Source.Presentation

open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Integration.Partition

/-- A proposed interval, point and cached rational reading. -/
public abbrev Code := Partition.Interval × Fraction.Rational × Fraction.Rational

/-- A proposed reading is valid when its point lies in its interval and its cache matches the pi source. -/
@[expose] public def Valid (code : Code) : Prop :=
  code.1.start ≤ code.2.1 ∧ code.2.1 ≤ code.1.finish ∧ code.2.2 = value code.2.1

set_option genInjectivity false in
/-- The result of checking a proposed pi source point and its retained cache. -/
public inductive Check (code : Code) where
  /-- Both bounds and the cached reading are correct. -/ | valid (proof : Valid code)
  /-- The point lies below its retained interval. -/ | belowStart (proof : code.2.1 < code.1.start)
  /-- The point lies above its retained interval. -/ | aboveFinish (proof : code.1.finish < code.2.1)
  /-- The cached reading differs from the exact pi source. -/ | wrongReading (proof : code.2.2 ≠ value code.2.1)

/-- Compare retained source-point check outcomes without checking the point again. -/
public def Check.compare {code : Code} (left right : Check code) : Decidable (left = right) := by
  cases left <;> cases right <;> first
    | exact .isTrue rfl
    | exact .isFalse (by intro same; cases same)

/-- Check interval membership and then the cached reading against the exact pi source. -/
@[expose] public def check (code : Code) : Check code :=
  if lower : code.1.start ≤ code.2.1 then
    if upper : code.2.1 ≤ code.1.finish then
      if reading : code.2.2 = value code.2.1 then .valid ⟨lower, upper, reading⟩
      else .wrongReading reading
    else .aboveFinish (lt_of_not_ge upper)
  else .belowStart (lt_of_not_ge lower)

/-- Decide admissibility using the typed source-point checker. -/
@[expose] public def recognize (code : Code) : Decidable (Valid code) :=
  match check code with
  | .valid proof => .isTrue proof
  | .belowStart proof => .isFalse (fun valid => (not_lt_of_ge valid.1) proof)
  | .aboveFinish proof => .isFalse (fun valid => (not_lt_of_ge valid.2.1) proof)
  | .wrongReading proof => .isFalse (fun valid => proof valid.2.2)

/-- Decide the validity of a proposed pi source point. -/
public instance (code : Code) : Decidable (Valid code) := recognize code

/-- Finite proposed data accompanied by their source-bound validity proof. -/
public abbrev Display := {code : Code // Valid code}

/-- Construct the original pi source point using the supplied cached reading. -/
@[expose] public def read (display : Display) : SourcePoint value :=
  ⟨display.val.1, display.val.2.1, display.property.1, display.property.2.1,
    display.val.2.2, display.property.2.2⟩

/-- Quote the original interval, point and saved reading of a pi source point. -/
@[expose] public def quote (point : SourcePoint value) : Display :=
  ⟨(point.interval, point.point, point.reading), point.start_le, point.point_le_finish, point.reading_eq⟩

/-- Equality of the retained interval, point and cached reading. -/
@[expose] public def Same (left right : Display) : Prop := left.val = right.val

/-- Decide exact equality of the retained finite data. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val = right.val))

/-- Decide equality of two accepted pi source-point displays. -/
public instance (left right : Display) : Decidable (Same left right) := compare left right

/-- Reading a quoted point recovers the original source-bound owner. -/
public theorem read_quote (point : SourcePoint value) : read (quote point) = point := by
  cases point
  rfl

/-- Quoting a read display recovers its retained data. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  apply Subtype.ext
  rfl

/-- Exact display equality is equivalent to equality of original source points. -/
public theorem same_iff_read_eq (left right : Display) : Same left right ↔ read left = read right := by
  constructor
  · intro same
    cases Subtype.ext same
    rfl
  · intro same
    have quoted := congrArg quote same
    change left.val = right.val
    simpa only [quote_read] using congrArg Subtype.val quoted

/-- A validated point supplies its original saved reading to the existing cache lookup. -/
public theorem readCached_head (display : Display) (remaining : List (SourcePoint value)) :
    SourcePoint.readCached value (read display :: remaining) (read display).point = display.val.2.2 :=
  SourcePoint.readCached_head (read display) remaining

/-!
The finite code contains the original interval, rational tag and cached rational
reading. `check` rejects a tag outside that interval or a reading differing from
the fixed `Source.value`; it does not assert any universal source-range property.
`read` and `quote` retain the original `SourcePoint value` owner, and `compare`
decides its exact retained-data identity, not equality of different sources or
frontiers. The comparisons and source evaluation terminate through their existing
finite rational owners; their proof and runtime dependencies are not certified by
this presentation alone. `readCached_head` uses the original saved cache path.
-/
/-- The explicit presentation of source points bound to the pi integrand. -/
@[expose] public def sourcePoint : Purelib.Data.Presentation Code where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

namespace Bank

/-- An ordered bank of finite pi source-point proposals. -/
public abbrev Code := List Presentation.Code

/-- Every occurrence in the bank is a valid point for the original pi source. -/
@[expose] public def Valid : Code → Prop
  | [] => True
  | point :: rest => Presentation.Valid point ∧ Valid rest

set_option genInjectivity false in
/-- The first invalid bank occurrence, retaining its precise point failure. -/
public inductive Failure : Code → Type where
  /-- The first point is invalid. -/
  | here (point : Presentation.Code) (rest : Code) (reason : Presentation.Check point)
      (invalid : ¬ Presentation.Valid point) : Failure (point :: rest)
  /-- A later occurrence is invalid after the retained preceding point. -/
  | later (point : Presentation.Code) {rest : Code} (failure : Failure rest) : Failure (point :: rest)

/-- Compare located bank failures, retaining the reason and ordered occurrence. -/
public def Failure.compare {code : Code} (left right : Failure code) : Decidable (left = right) := by
  cases left with
  | here point rest reason invalid =>
    cases right with
    | here _ _ other _ =>
      match Presentation.Check.compare reason other with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    | _ => exact .isFalse (by intro same; cases same)
  | later point failure =>
    cases right with
    | later _ other =>
      match Failure.compare failure other with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    | _ => exact .isFalse (by intro same; cases same)
termination_by structural left

/-- A located bank failure disproves validity of the entire ordered bank. -/
public theorem Failure.notValid {code : Code} (failure : Failure code) : ¬ Valid code := by
  induction failure with
  | here _ _ _ invalid => exact fun valid => invalid valid.1
  | later _ _ ih => exact fun valid => ih valid.2

set_option genInjectivity false in
/-- Finite bank recognition returns validity or a located proved failure. -/
public inductive Check (code : Code) where
  /-- Every point is valid. -/ | accepted (valid : Valid code)
  /-- One retained occurrence fails its point check. -/ | rejected (failure : Failure code)

/-- Check point occurrences in their original order. -/
@[expose] public def check : (code : Code) → Check code
  | [] => .accepted True.intro
  | point :: rest =>
    let reason := Presentation.check point
    match reason with
    | .belowStart proof => .rejected (.here point rest reason (fun valid => (not_lt_of_ge valid.1) proof))
    | .aboveFinish proof => .rejected (.here point rest reason (fun valid => (not_lt_of_ge valid.2.1) proof))
    | .wrongReading proof => .rejected (.here point rest reason (fun valid => proof valid.2.2))
    | .valid valid =>
      match check rest with
      | .accepted tail => .accepted ⟨valid, tail⟩
      | .rejected failure => .rejected (.later point failure)

/-- Reconstruct an ordered bank using the exact checked point data. -/
@[expose] public def read : (code : Code) → Valid code → List (SourcePoint value)
  | [], _ => []
  | point :: rest, valid => Presentation.read ⟨point, valid.1⟩ :: read rest valid.2

/-- Quote the original bank in its retained order without evaluating its source again. -/
@[expose] public def quote : List (SourcePoint value) → Code
  | [] => []
  | point :: rest => (Presentation.quote point).val :: quote rest

/-- Quoted original points always satisfy the finite bank contract. -/
public theorem quote_valid : ∀ points, Valid (quote points)
  | [] => True.intro
  | point :: rest => ⟨(Presentation.quote point).property, quote_valid rest⟩

/-- Reading a quoted bank recovers its original ordered source points. -/
public theorem read_quote : ∀ (points : List (SourcePoint value)) (valid : Valid (quote points)),
    read (quote points) valid = points
  | [], _ => rfl
  | point :: rest, valid => by
      change Presentation.read ⟨(Presentation.quote point).val, valid.1⟩ :: read (quote rest) valid.2 = _
      rw [show Presentation.read ⟨(Presentation.quote point).val, valid.1⟩ = point from Presentation.read_quote point,
        read_quote rest valid.2]

/-- Quoting reconstructed points recovers the submitted ordered finite data. -/
public theorem quote_read : ∀ (code : Code) (valid : Valid code), quote (read code valid) = code
  | [], _ => rfl
  | point :: rest, valid => by
      change (Presentation.quote (Presentation.read ⟨point, valid.1⟩)).val :: quote (read rest valid.2) = _
      exact congrArg₂ List.cons (congrArg Subtype.val (Presentation.quote_read ⟨point, valid.1⟩))
        (quote_read rest valid.2)

end Bank

namespace Preparation

open Purelib.Approximation
open Purelib.Integration.SourceFrontier

/-- A rational request and the retained variation, mesh and original partition. -/
public abbrev Code := Fraction.Rational × Fraction.Rational ×
  Fraction.Rational × Unit.Normalized

/-- The retained fields agree with the original pi modulus and grid construction. -/
@[expose] public def Valid (code : Code) : Prop :=
  AccuracyRequest.Presentation.Valid code.1 ∧ code.2.1 = code.1 / 4 ∧ code.2.2.1 = modulus.radius code.2.1 ∧
    code.2.2.2 = Partition.Uniform.Grid.forWidth code.2.2.1

set_option genInjectivity false in
/-- The result identifies which retained preparation field differs from its defining value. -/
public inductive Check (code : Code) where
  /-- Every retained field matches the original construction. -/ | valid (proof : Valid code)
  /-- The requested tolerance is not positive. -/
  | nonpositiveRequest (proof : code.1 ≤ 0)
  /-- The variation differs from the request's quarter budget. -/
  | wrongVariation (proof : code.2.1 ≠ code.1 / 4)
  /-- The mesh differs from the original modulus response. -/
  | wrongMesh (proof : code.2.2.1 ≠ modulus.radius code.2.1)
  /-- The retained partition differs from the original selected grid. -/
  | wrongPartition (proof : code.2.2.2 ≠ Partition.Uniform.Grid.forWidth code.2.2.1)

/-- Compare retained preparation-check outcomes without recomputing the grid. -/
public def Check.compare {code : Code} (left right : Check code) : Decidable (left = right) := by
  cases left <;> cases right <;> first
    | exact .isTrue rfl
    | exact .isFalse (by intro same; cases same)

/-- Check retained fields in construction order, comparing original partitions by their cuts. -/
@[expose] public def check (code : Code) : Check code :=
  match AccuracyRequest.Presentation.check code.1 with
  | .nonpositive proof => .nonpositiveRequest proof
  | .valid positive =>
    if variation : code.2.1 = code.1 / 4 then
      if mesh : code.2.2.1 = modulus.radius code.2.1 then
        match Unit.Presentation.compare
            (Unit.Presentation.quote code.2.2.2)
            (Unit.Presentation.quote (Partition.Uniform.Grid.forWidth code.2.2.1)) with
        | .isTrue cuts => .valid ⟨positive, variation, mesh, Unit.Normalized.ext_cuts cuts⟩
        | .isFalse different => .wrongPartition (fun equal => different (congrArg Unit.Normalized.cuts equal))
      else .wrongMesh mesh
    else .wrongVariation variation

/-- Decide validity using the same typed preparation check. -/
@[expose] public def recognize (code : Code) : Decidable (Valid code) :=
  match check code with
  | .valid proof => .isTrue proof
  | .nonpositiveRequest proof => .isFalse (fun valid => (not_lt_of_ge proof) valid.1)
  | .wrongVariation proof => .isFalse (fun valid => proof valid.2.1)
  | .wrongMesh proof => .isFalse (fun valid => proof valid.2.2.1)
  | .wrongPartition proof => .isFalse (fun valid => proof valid.2.2.2)

/-- A preparation display retains its exact original fields and their checked equations. -/
public abbrev Display := {code : Code // Valid code}

/-- Construct the original pi preparation without replacing the supplied partition cache. -/
@[expose] public def read (display : Display) : Continuous.Preparation modulus :=
  ⟨AccuracyRequest.Presentation.read ⟨display.val.1, display.property.1⟩, display.val.2.1, display.property.2.1,
    display.val.2.2.1, display.property.2.2.1, display.val.2.2.2, display.property.2.2.2⟩

/-- Quote the retained request, variation, mesh and original partition directly. -/
@[expose] public def quote (prepared : Continuous.Preparation modulus) : Display :=
  ⟨(prepared.request.tolerance, prepared.variation, prepared.mesh, prepared.partition),
    prepared.request.positive, prepared.variation_eq, prepared.mesh_eq, prepared.partition_eq⟩

/-- A preparation's original request determines all its retained computational fields. -/
public theorem eq_of_request_eq (left right : Continuous.Preparation modulus)
    (equal : left.request = right.request) : left = right := by
  cases left with
  | mk leftRequest leftVariation leftVariationEq leftMesh leftMeshEq leftPartition leftPartitionEq =>
    cases right with
    | mk rightRequest rightVariation rightVariationEq rightMesh rightMeshEq rightPartition rightPartitionEq =>
      cases equal
      cases leftVariationEq
      cases rightVariationEq
      cases leftMeshEq
      cases rightMeshEq
      cases leftPartitionEq
      cases rightPartitionEq
      rfl

/-- Two valid preparations agree exactly when their retained request tolerances agree. -/
@[expose] public def Same (left right : Display) : Prop := left.val.1 = right.val.1

/-- Compare valid preparations by their retained request tolerances. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val.1 = right.val.1))

/-- Reading a quoted preparation recovers the original owner and its retained cache. -/
public theorem read_quote (prepared : Continuous.Preparation modulus) : read (quote prepared) = prepared :=
  eq_of_request_eq _ _ (AccuracyRequest.eq_of_tolerance_eq rfl)

/-- Quoting a read display recovers all of its originally retained fields. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  apply Subtype.ext
  rfl

/-- The comparison relation is exactly equality of the original preparations. -/
public theorem same_iff_read_eq (left right : Display) : Same left right ↔ read left = read right := by
  constructor
  · intro equal
    apply eq_of_request_eq
    exact AccuracyRequest.eq_of_tolerance_eq equal
  · intro equal
    exact congrArg (fun prepared => prepared.request.tolerance) equal

/-- The explicit finite presentation of pi source preparations. -/
@[expose] public def preparation : Purelib.Data.Presentation Code where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-!
The request is a rational tolerance. The check first rejects nonpositive values,
then validates
retained variation, modulus response and partition against the original pi
construction, with a proved mismatch for each field. It compares existing
partition cuts directly and retains the supplied partition and its interval
cache. The defining equations make the request tolerance determine preparation
identity; `same_iff_read_eq` is not equality of arbitrary source procedures.
Finite rational decisions and the original grid builder supply execution; their
proof and native-runtime dependencies remain separate audit obligations.
-/

end Preparation

namespace Cell

/-- Proposed source-point data, weight and lower and upper range readings. -/
public abbrev Code := Presentation.Code × Fraction.Rational × Fraction.Rational × Fraction.Rational

/-- The payload is valid, the weight is nonnegative and the range endpoints are ordered. -/
@[expose] public def Valid (code : Code) : Prop :=
  Presentation.Valid code.1 ∧ 0 ≤ code.2.1 ∧ code.2.2.1 ≤ code.2.2.2

set_option genInjectivity false in
/-- A finite cell check, preserving the precise source-point or scalar failure. -/
public inductive Check (code : Code) where
  /-- The payload, weight and ordered range are valid. -/ | valid (proof : Valid code)
  /-- The source tag is below its interval. -/ | belowStart (proof : code.1.2.1 < code.1.1.start)
  /-- The source tag is above its interval. -/ | aboveFinish (proof : code.1.1.finish < code.1.2.1)
  /-- The saved reading differs from the pi source. -/ | wrongReading (proof : code.1.2.2 ≠ value code.1.2.1)
  /-- The retained weight is negative. -/ | negativeWeight (proof : code.2.1 < 0)
  /-- The retained lower endpoint exceeds the upper endpoint. -/ | reversedRange (proof : code.2.2.2 < code.2.2.1)

/-- Decide whether two retained cell-check results have the same constructor.

The proposed cell is the shared index; proof witnesses do not distinguish
results. This compares the outcomes directly without repeating the check. -/
public def Check.compare {code : Code} (left right : Check code) : Decidable (left = right) := by
  cases left <;> cases right <;> first
    | exact .isTrue rfl
    | exact .isFalse (by intro same; cases same)

/-- Check the source point first, then the weight and range, retaining a proved failure. -/
@[expose] public def check (code : Code) : Check code :=
  match Presentation.check code.1 with
  | .belowStart proof => .belowStart proof
  | .aboveFinish proof => .aboveFinish proof
  | .wrongReading proof => .wrongReading proof
  | .valid point =>
    if weight : 0 ≤ code.2.1 then
      if range : code.2.2.1 ≤ code.2.2.2 then .valid ⟨point, weight, range⟩
      else .reversedRange (lt_of_not_ge range)
    else .negativeWeight (lt_of_not_ge weight)

/-- Decide finite cell validity from the same typed checker. -/
@[expose] public def recognize (code : Code) : Decidable (Valid code) :=
  match check code with
  | .valid proof => .isTrue proof
  | .belowStart proof => .isFalse (fun valid => (not_lt_of_ge valid.1.1) proof)
  | .aboveFinish proof => .isFalse (fun valid => (not_lt_of_ge valid.1.2.1) proof)
  | .wrongReading proof => .isFalse (fun valid => proof valid.1.2.2)
  | .negativeWeight proof => .isFalse (fun valid => (not_lt_of_ge valid.2.1) proof)
  | .reversedRange proof => .isFalse (fun valid => (not_lt_of_ge valid.2.2) proof)

/-- Decide the validity of the finite fields of a pi integration cell. -/
public instance (code : Code) : Decidable (Valid code) := recognize code

/-- Proposed finite cell data with the checked payload and scalar conditions. -/
public abbrev Display := {code : Code // Valid code}

/-- Construct the original integration cell with the supplied retained fields. -/
@[expose] public def read (display : Display) : IntegrationCell (SourcePoint value) :=
  ⟨Presentation.read ⟨display.val.1, display.property.1⟩, display.val.2.1,
    display.property.2.1, display.val.2.2.1, display.val.2.2.2, display.property.2.2⟩

/-- Quote an original cell's source point, weight and range endpoints. -/
@[expose] public def quote (cell : IntegrationCell (SourcePoint value)) : Display :=
  ⟨((Presentation.quote cell.item).val, cell.weight, cell.lower, cell.upper),
    (Presentation.quote cell.item).property, cell.weight_nonnegative, cell.range_valid⟩

/-- Two displays agree exactly when all their retained finite fields agree. -/
@[expose] public def Same (left right : Display) : Prop := left.val = right.val

/-- Compare retained cell data using the original finite field decisions. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val = right.val))

/-- Decide exact equality of accepted pi integration-cell data. -/
public instance (left right : Display) : Decidable (Same left right) := compare left right

/-- Reading a quoted cell recovers the original owner and its proof fields. -/
public theorem read_quote (cell : IntegrationCell (SourcePoint value)) : read (quote cell) = cell := by
  cases cell with
  | mk item weight weight_nonnegative lower upper range_valid =>
    cases item
    rfl

/-- Quoting a read cell recovers the original displayed fields. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  apply Subtype.ext
  rfl

/-- Display equality agrees exactly with original integration-cell equality. -/
public theorem same_iff_read_eq (left right : Display) : Same left right ↔ read left = read right := by
  constructor
  · intro same
    cases Subtype.ext same
    rfl
  · intro same
    have quoted := congrArg quote same
    change left.val = right.val
    simpa only [quote_read] using congrArg Subtype.val quoted

/-- The original cache lookup consumes the validated cell's saved source reading. -/
public theorem readCached_head (display : Display) (remaining : List (SourcePoint value)) :
    SourcePoint.readCached value ((read display).item :: remaining) (read display).item.point =
      display.val.1.2.2 :=
  Presentation.readCached_head ⟨display.val.1, display.property.1⟩ remaining

/-!
The finite check validates the original source point and the cell's weight and
range fields. It does not decide `IntegrationCell.Source.Admitted`: equality of
the weight to the interval length and source containment throughout the interval
remain separate certificates. Nor does it validate a `SourceFrontier`'s
partition, ordered domains or universal source-range proof. The exact retained
fields determine original cell equality, while the proof and runtime boundaries
of the underlying rational decisions and pi source remain inherited.
-/
/-- The explicit finite-field presentation of pi integration cells. -/
@[expose] public def cell : Purelib.Data.Presentation Code where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

end Cell

namespace Frontier

/-- The finite alignment conditions for proposed cells and original partition intervals. -/
@[expose] public def Aligned : List Cell.Code → List Partition.Interval → Prop
  | [], [] => True
  | cell :: cells, interval :: intervals =>
      Cell.Valid cell ∧ cell.1.1 = interval ∧ cell.2.1 = cell.1.1.signedLength ∧
        Aligned cells intervals
  | _, _ => False

set_option genInjectivity false in
/-- A located failure in the ordered cell/domain scan.

Each `later` constructor retains one preceding cell and interval, so repeated
equal cells remain distinguishable by their original occurrence. -/
public inductive Failure : List Cell.Code → List Partition.Interval → Type where
  /-- The partition retains an interval with no corresponding cell. -/
  | missingCell (interval : Partition.Interval) (intervals : List Partition.Interval) :
      Failure [] (interval :: intervals)
  /-- A proposed cell has no corresponding partition interval. -/
  | extraCell (cell : Cell.Code) (cells : List Cell.Code) : Failure (cell :: cells) []
  /-- The current cell fails its original payload or scalar check. -/
  | badCell (cell : Cell.Code) (cells : List Cell.Code) (interval : Partition.Interval)
      (intervals : List Partition.Interval) (reason : Cell.Check cell) (invalid : ¬ Cell.Valid cell) :
      Failure (cell :: cells) (interval :: intervals)
  /-- The current cell's domain differs from the current original interval. -/
  | wrongDomain (cell : Cell.Code) (cells : List Cell.Code) (interval : Partition.Interval)
      (intervals : List Partition.Interval) (different : cell.1.1 ≠ interval) :
      Failure (cell :: cells) (interval :: intervals)
  /-- The current cell's weight differs from its domain's exact signed length. -/
  | wrongWeight (cell : Cell.Code) (cells : List Cell.Code) (interval : Partition.Interval)
      (intervals : List Partition.Interval) (different : cell.2.1 ≠ cell.1.1.signedLength) :
      Failure (cell :: cells) (interval :: intervals)
  /-- A failure occurs after the displayed first cell and interval. -/
  | later (cell : Cell.Code) (interval : Partition.Interval) {cells : List Cell.Code}
      {intervals : List Partition.Interval} (failure : Failure cells intervals) :
      Failure (cell :: cells) (interval :: intervals)

/-- Compare located failures against the same original cell and interval lists.

The recursive comparison retains the ordered occurrence and any cell-check
reason; proof witnesses do not distinguish outcomes. No scan is repeated. -/
public def Failure.compare {cells : List Cell.Code} {intervals : List Partition.Interval}
    (left right : Failure cells intervals) : Decidable (left = right) := by
  cases left with
  | missingCell interval intervals =>
    cases right
    exact .isTrue rfl
  | extraCell cell cells =>
    cases right
    exact .isTrue rfl
  | badCell cell cells interval intervals reason invalid =>
    cases right with
    | badCell _ _ _ _ other _ =>
      match Cell.Check.compare reason other with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    | _ => exact .isFalse (by intro same; cases same)
  | wrongDomain cell cells interval intervals different =>
    cases right <;> first
      | exact .isTrue rfl
      | exact .isFalse (by intro same; cases same)
  | wrongWeight cell cells interval intervals different =>
    cases right <;> first
      | exact .isTrue rfl
      | exact .isFalse (by intro same; cases same)
  | later cell interval failure =>
    cases right with
    | later _ _ other =>
      match Failure.compare failure other with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    | _ => exact .isFalse (by intro same; cases same)
termination_by structural left

/-- Every located scan failure proves that the proposed lists are not aligned. -/
public theorem Failure.notAligned {cells : List Cell.Code} {intervals : List Partition.Interval}
    (failure : Failure cells intervals) : ¬ Aligned cells intervals := by
  induction failure with
  | missingCell => exact fun invalid => invalid
  | extraCell => exact fun invalid => invalid
  | badCell _ _ _ _ _ invalid => exact fun aligned => invalid aligned.1
  | wrongDomain _ _ _ _ different => exact fun aligned => different aligned.2.1
  | wrongWeight _ _ _ _ different => exact fun aligned => different aligned.2.2.1
  | later _ _ _ ih => exact fun aligned => ih aligned.2.2.2

set_option genInjectivity false in
/-- A total finite scan returns alignment or a located, proved failure. -/
public inductive Check (cells : List Cell.Code) (intervals : List Partition.Interval) where
  /-- All original occurrences and exact weights align. -/ | accepted (aligned : Aligned cells intervals)
  /-- A specific occurrence or list-length mismatch was found. -/ | rejected (failure : Failure cells intervals)

/-- Check cells and partition intervals together in their original order. -/
@[expose] public def check : (cells : List Cell.Code) → (intervals : List Partition.Interval) → Check cells intervals
  | [], [] => .accepted True.intro
  | [], interval :: intervals => .rejected (.missingCell interval intervals)
  | cell :: cells, [] => .rejected (.extraCell cell cells)
  | cell :: cells, interval :: intervals =>
      match Cell.check cell with
      | .belowStart proof => .rejected (.badCell cell cells interval intervals (.belowStart proof)
          (fun valid => (not_lt_of_ge valid.1.1) proof))
      | .aboveFinish proof => .rejected (.badCell cell cells interval intervals (.aboveFinish proof)
          (fun valid => (not_lt_of_ge valid.1.2.1) proof))
      | .wrongReading proof => .rejected (.badCell cell cells interval intervals (.wrongReading proof)
          (fun valid => proof valid.1.2.2))
      | .negativeWeight proof => .rejected (.badCell cell cells interval intervals (.negativeWeight proof)
          (fun valid => (not_lt_of_ge valid.2.1) proof))
      | .reversedRange proof => .rejected (.badCell cell cells interval intervals (.reversedRange proof)
          (fun valid => (not_lt_of_ge valid.2.2) proof))
      | .valid valid =>
        if domain : cell.1.1 = interval then
          if weight : cell.2.1 = cell.1.1.signedLength then
            match check cells intervals with
            | .accepted tail => .accepted ⟨valid, domain, weight, tail⟩
            | .rejected failure => .rejected (.later cell interval failure)
          else .rejected (.wrongWeight cell cells interval intervals weight)
        else .rejected (.wrongDomain cell cells interval intervals domain)

/-- Decide finite alignment using the same located scan. -/
@[expose] public def recognize (cells : List Cell.Code) (intervals : List Partition.Interval) :
    Decidable (Aligned cells intervals) :=
  match check cells intervals with
  | .accepted aligned => .isTrue aligned
  | .rejected failure => .isFalse failure.notAligned

/-- Reconstruct the original ordered cells from aligned finite data. -/
@[expose] public def readCells : (cells : List Cell.Code) → (intervals : List Partition.Interval) →
    Aligned cells intervals → List (IntegrationCell (SourcePoint value))
  | [], _, _ => []
  | _ :: _, [], impossible => False.elim impossible
  | cell :: cells, _ :: intervals, aligned =>
      Cell.read ⟨cell, aligned.1⟩ :: readCells cells intervals aligned.2.2.2

/-- Reconstructed cell domains retain the exact original interval order. -/
public theorem readCells_domains : ∀ (cells : List Cell.Code) (intervals : List Partition.Interval)
    (aligned : Aligned cells intervals),
    (readCells cells intervals aligned).map (fun cell => cell.item.interval) = intervals
  | [], [], _ => rfl
  | [], _ :: _, impossible => False.elim impossible
  | _ :: _, [], impossible => False.elim impossible
  | cell :: cells, interval :: intervals, aligned => by
      change cell.1.1 :: (readCells cells intervals aligned.2.2.2).map (fun cell => cell.item.interval) =
        interval :: intervals
      exact congrArg₂ List.cons aligned.2.1 (readCells_domains cells intervals aligned.2.2.2)

/-- Every reconstructed cell retains its exact domain weight. -/
public theorem readCells_weights : ∀ (cells : List Cell.Code) (intervals : List Partition.Interval)
    (aligned : Aligned cells intervals) (cell : IntegrationCell (SourcePoint value)),
    cell ∈ readCells cells intervals aligned → cell.weight = cell.item.interval.signedLength
  | [], _, _, _, member => by nomatch member
  | _ :: _, [], impossible, _, _ => False.elim impossible
  | head :: cells, _ :: intervals, aligned, cell, member => by
      change cell ∈ Cell.read ⟨head, aligned.1⟩ :: readCells cells intervals aligned.2.2.2 at member
      cases member with
      | head => exact aligned.2.2.1
      | tail _ member => exact readCells_weights cells intervals aligned.2.2.2 cell member

/-- Project the original ordered cell data without changing their owners. -/
@[expose] public def quoteCells (cells : List (IntegrationCell (SourcePoint value))) : List Cell.Code :=
  cells.map (fun cell => (Cell.quote cell).val)

/-- Original aligned domains and weights validate their projected finite cell data. -/
public theorem aligned_quoteCells : ∀ (cells : List (IntegrationCell (SourcePoint value)))
    (intervals : List Partition.Interval),
    cells.map (fun cell => cell.item.interval) = intervals →
    (∀ cell ∈ cells, cell.weight = cell.item.interval.signedLength) → Aligned (quoteCells cells) intervals
  | [], [], _, _ => True.intro
  | [], _ :: _, domains, _ => by cases domains
  | _ :: _, [], domains, _ => by cases domains
  | cell :: cells, interval :: intervals, domains, weights => by
      have first : cell.item.interval = interval := (List.cons.inj domains).1
      have rest : cells.map (fun cell => cell.item.interval) = intervals := (List.cons.inj domains).2
      exact ⟨(Cell.quote cell).property, first, weights cell List.mem_cons_self,
        aligned_quoteCells cells intervals rest (fun other member => weights other (List.mem_cons_of_mem cell member))⟩

/-- Reconstructing projected aligned cell data recovers the original ordered cells. -/
public theorem readCells_quoteCells : ∀ (cells : List (IntegrationCell (SourcePoint value)))
    (intervals : List Partition.Interval) (aligned : Aligned (quoteCells cells) intervals),
    readCells (quoteCells cells) intervals aligned = cells
  | [], [], _ => rfl
  | [], _ :: _, impossible => False.elim impossible
  | _ :: _, [], impossible => False.elim impossible
  | cell :: cells, _ :: intervals, aligned => by
      change Cell.read ⟨(Cell.quote cell).val, aligned.1⟩ ::
        readCells (quoteCells cells) intervals aligned.2.2.2 = cell :: cells
      rw [show Cell.read ⟨(Cell.quote cell).val, aligned.1⟩ = cell from Cell.read_quote cell,
        readCells_quoteCells cells intervals aligned.2.2.2]

/-- Projecting reconstructed cells returns their original ordered finite data. -/
public theorem quoteCells_readCells : ∀ (cells : List Cell.Code) (intervals : List Partition.Interval)
    (aligned : Aligned cells intervals), quoteCells (readCells cells intervals aligned) = cells
  | [], [], _ => rfl
  | [], _ :: _, impossible => False.elim impossible
  | _ :: _, [], impossible => False.elim impossible
  | cell :: cells, _ :: intervals, aligned => by
      change (Cell.quote (Cell.read ⟨cell, aligned.1⟩)).val ::
        quoteCells (readCells cells intervals aligned.2.2.2) = cell :: cells
      exact congrArg₂ List.cons (congrArg Subtype.val (Cell.quote_read ⟨cell, aligned.1⟩))
        (quoteCells_readCells cells intervals aligned.2.2.2)

/-- Proposed ordered cell data attached to the original cached partition. -/
public abbrev Code := Unit.Normalized × List Cell.Code

/-- Build a proposed frontier from an already checked normalized-cut display. -/
@[expose] public def fromCuts (partition : Unit.Presentation.Display) (cells : List Cell.Code) : Code :=
  (Unit.Presentation.read partition, cells)

/-- Check ordered proposed cells against the original partition's retained interval cache. -/
@[expose] public def checkCode (code : Code) : Check code.2 code.1.intervals := check code.2 code.1.intervals

/-- The proposed cells align with the original partition's retained intervals. -/
@[expose] public def Valid (code : Code) : Prop := Aligned code.2 code.1.intervals

/-- Decide the finite frontier conditions through the located alignment check. -/
@[expose] public def validDecision (code : Code) : Decidable (Valid code) := recognize code.2 code.1.intervals

/-- Decide finite frontier validity by the original ordered intervals and cells. -/
public instance (code : Code) : Decidable (Valid code) := validDecision code

/-- A partition and ordered cell data with exact finite alignment. -/
public abbrev Display := {code : Code // Valid code}

/-- The universal source-range certificate required for these exact reconstructed cells. -/
@[expose] public def SourceRange (display : Display) : Prop :=
  ∀ cell ∈ readCells display.val.2 display.val.1.intervals display.property,
    ∀ point, cell.item.interval.start ≤ point → point ≤ cell.item.interval.finish →
      cell.lower ≤ value point ∧ value point ≤ cell.upper

/-- The endpoint inequalities for each retained cell in its original order. -/
@[expose] public def EndpointRange : List (IntegrationCell (SourcePoint value)) → Prop
  | [] => True
  | cell :: cells => cell.lower ≤ value cell.item.interval.finish ∧
      value cell.item.interval.start ≤ cell.upper ∧ EndpointRange cells

set_option genInjectivity false in
/-- A located endpoint failure retains every earlier cell occurrence. -/
public inductive RangeFailure : List (IntegrationCell (SourcePoint value)) → Type where
  /-- The lower bound exceeds the source at the finishing endpoint. -/
  | lower (cell : IntegrationCell (SourcePoint value)) (cells : List (IntegrationCell (SourcePoint value)))
      (violation : value cell.item.interval.finish < cell.lower) : RangeFailure (cell :: cells)
  /-- The upper bound is below the source at the starting endpoint. -/
  | upper (cell : IntegrationCell (SourcePoint value)) (cells : List (IntegrationCell (SourcePoint value)))
      (violation : cell.upper < value cell.item.interval.start) : RangeFailure (cell :: cells)
  /-- A later occurrence fails after the retained preceding cell. -/
  | later (cell : IntegrationCell (SourcePoint value)) {cells : List (IntegrationCell (SourcePoint value))}
      (failure : RangeFailure cells) : RangeFailure (cell :: cells)

/-- Decide equality of two retained endpoint failures on the same ordered cells.

The comparison preserves the endpoint and original occurrence while ignoring
proof witnesses. It traverses the failure values without checking the source again. -/
public def RangeFailure.compare {cells : List (IntegrationCell (SourcePoint value))}
    (left right : RangeFailure cells) : Decidable (left = right) := by
  cases left with
  | lower cell cells violation =>
    cases right <;> first
      | exact .isTrue rfl
      | exact .isFalse (by intro same; cases same)
  | upper cell cells violation =>
    cases right <;> first
      | exact .isTrue rfl
      | exact .isFalse (by intro same; cases same)
  | later cell failure =>
    cases right with
    | later _ other =>
      match RangeFailure.compare failure other with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    | _ => exact .isFalse (by intro same; cases same)
termination_by structural left

/-- Every located endpoint failure disproves the corresponding endpoint conditions. -/
public theorem RangeFailure.notEndpointRange {cells : List (IntegrationCell (SourcePoint value))}
    (failure : RangeFailure cells) : ¬ EndpointRange cells := by
  induction failure with
  | lower _ _ violation => exact fun range => (not_lt_of_ge range.1) violation
  | upper _ _ violation => exact fun range => (not_lt_of_ge range.2.1) violation
  | later _ _ ih => exact fun range => ih range.2.2

set_option genInjectivity false in
/-- The finite endpoint scan either accepts all cells or locates a proved violation. -/
public inductive RangeCheck (cells : List (IntegrationCell (SourcePoint value))) where
  /-- All retained endpoint inequalities hold. -/ | accepted (proof : EndpointRange cells)
  /-- A specific retained occurrence violates an endpoint inequality. -/ | rejected (failure : RangeFailure cells)

/-- Check both endpoint inequalities of every original cell, preserving occurrence order. -/
@[expose] public def checkEndpoints : (cells : List (IntegrationCell (SourcePoint value))) → RangeCheck cells
  | [] => .accepted True.intro
  | cell :: cells =>
    if lower : cell.lower ≤ value cell.item.interval.finish then
      if upper : value cell.item.interval.start ≤ cell.upper then
        match checkEndpoints cells with
        | .accepted tail => .accepted ⟨lower, upper, tail⟩
        | .rejected failure => .rejected (.later cell failure)
      else .rejected (.upper cell cells (lt_of_not_ge upper))
    else .rejected (.lower cell cells (lt_of_not_ge lower))

/-- On valid unit intervals, endpoint conditions exactly characterize source containment. -/
private theorem sourceRange_iff_endpoints_list (cells : List (IntegrationCell (SourcePoint value))) :
    (∀ cell ∈ cells, cell.item.interval.Valid) →
    ((∀ cell ∈ cells, ∀ point, cell.item.interval.start ≤ point → point ≤ cell.item.interval.finish →
      cell.lower ≤ value point ∧ value point ≤ cell.upper) ↔ EndpointRange cells) := by
  induction cells with
  | nil =>
    intro _
    constructor
    · intro _; exact True.intro
    · intro _ cell member; nomatch member
  | cons cell cells ih =>
    intro valid
    have cellValid := valid cell List.mem_cons_self
    have tailValid : ∀ other ∈ cells, other.item.interval.Valid :=
      fun other member => valid other (List.mem_cons_of_mem cell member)
    constructor
    · intro range
      have lower := (range cell List.mem_cons_self cell.item.interval.finish cellValid.2.1.le le_rfl).1
      have upper := (range cell List.mem_cons_self cell.item.interval.start le_rfl cellValid.2.1.le).2
      exact ⟨lower, upper, (ih tailValid).mp (fun other member => range other (List.mem_cons_of_mem cell member))⟩
    · intro endpoints other member point start finish
      cases member with
      | head =>
        exact ⟨endpoints.1.trans (value_antitone (cellValid.1.trans start) finish),
          (value_antitone cellValid.1 start).trans endpoints.2.1⟩
      | tail _ member => exact (ih tailValid).mpr endpoints.2.2 other member point start finish

/-- Endpoint conditions are equivalent to source containment for the retained partition. -/
public theorem sourceRange_iff_endpoints (display : Display) :
    SourceRange display ↔ EndpointRange (readCells display.val.2 display.val.1.intervals display.property) := by
  apply sourceRange_iff_endpoints_list
  intro cell member
  apply display.val.1.valid
  rw [← readCells_domains display.val.2 display.val.1.intervals display.property]
  exact Purelib.Data.List.Map.mem_map_of_mem member

/-- Accepted endpoint data supply the original universal source-range certificate. -/
public theorem sourceRange_of_endpoints (display : Display)
    (endpoints : EndpointRange (readCells display.val.2 display.val.1.intervals display.property)) :
    SourceRange display := (sourceRange_iff_endpoints display).mpr endpoints

set_option genInjectivity false in
/-- The fixed-source scan returns the original range proof or a located failure. -/
public inductive SourceRangeCheck (display : Display) where
  /-- The exact original cells satisfy source containment. -/ | accepted (proof : SourceRange display)
  /-- A retained cell occurrence has an invalid endpoint bound. -/
  | rejected (failure : RangeFailure (readCells display.val.2 display.val.1.intervals display.property))

/-- Check the fixed-source range of the original aligned frontier cells. -/
@[expose] public def checkSourceRange (display : Display) : SourceRangeCheck display :=
  match checkEndpoints (readCells display.val.2 display.val.1.intervals display.property) with
  | .accepted endpoints => .accepted (sourceRange_of_endpoints display endpoints)
  | .rejected failure => .rejected failure

/-- A located endpoint violation disproves the original source-range certificate. -/
public theorem RangeFailure.notSourceRange (display : Display)
    (failure : RangeFailure (readCells display.val.2 display.val.1.intervals display.property)) :
    ¬ SourceRange display := fun range => failure.notEndpointRange ((sourceRange_iff_endpoints display).mp range)

/-- Construct the original frontier using a separately supplied source-range proof. -/
@[expose] public def read (display : Display) (range : SourceRange display) : SourceFrontier value where
  partition := display.val.1
  cells := readCells display.val.2 display.val.1.intervals display.property
  domains_eq := readCells_domains display.val.2 display.val.1.intervals display.property
  weight_eq := readCells_weights display.val.2 display.val.1.intervals display.property
  source_range := range

/-- Quote an original frontier by its existing partition and ordered cell fields. -/
@[expose] public def quote (frontier : SourceFrontier value) : Display :=
  ⟨(frontier.partition, quoteCells frontier.cells),
    aligned_quoteCells frontier.cells frontier.partition.intervals frontier.domains_eq frontier.weight_eq⟩

/-- A quoted frontier retains its original universal source-range certificate. -/
public theorem quote_sourceRange (frontier : SourceFrontier value) : SourceRange (quote frontier) := by
  change ∀ cell ∈ readCells (quoteCells frontier.cells) frontier.partition.intervals _, _
  rw [readCells_quoteCells]
  exact frontier.source_range

/-- Reading a quoted frontier recovers the original partition, cells and proof fields. -/
public theorem read_quote (frontier : SourceFrontier value) (range : SourceRange (quote frontier)) :
    read (quote frontier) range = frontier := by
  apply SourceFrontier.ext
  · rfl
  · exact readCells_quoteCells frontier.cells frontier.partition.intervals _

/-- Quoting a reconstructed frontier recovers the original displayed finite fields. -/
public theorem quote_read (display : Display) (range : SourceRange display) : quote (read display range) = display := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact quoteCells_readCells display.val.2 display.val.1.intervals display.property

/-- Two frontier displays retain the same partition cuts and ordered cell data. -/
@[expose] public def Same (left right : Display) : Prop :=
  left.val.1.cuts = right.val.1.cuts ∧ left.val.2 = right.val.2

/-- Compare the original partition cuts and all ordered cell data. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val.1.cuts = right.val.1.cuts ∧ left.val.2 = right.val.2))

/-- Exact finite frontier equality agrees with equality of the original certified owners. -/
public theorem same_iff_read_eq (left right : Display) (leftRange : SourceRange left)
    (rightRange : SourceRange right) : Same left right ↔ read left leftRange = read right rightRange := by
  constructor
  · intro same
    have partition : left.val.1 = right.val.1 := Unit.Normalized.ext_cuts same.1
    have displays : left = right := Subtype.ext (Prod.ext partition same.2)
    cases displays
    rfl
  · intro same
    have quoted := congrArg quote same
    rw [quote_read, quote_read] at quoted
    exact ⟨congrArg (fun display : Display => display.val.1.cuts) quoted,
      congrArg (fun display : Display => display.val.2) quoted⟩

/-- The finite presentation of pi frontier data, before supplying universal source bounds. -/
@[expose] public def frontier : Purelib.Data.Presentation Code where
  Valid := Valid
  recognize := validDecision
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
    fun h k => ⟨h.1.trans k.1, h.2.trans k.2⟩⟩

set_option genInjectivity false in
/-- The result of checking raw frontier cuts and ordered cell data. -/
public inductive RawCheck (cuts : Unit.Presentation.Code) (cells : List Cell.Code) where
  /-- The original cut checker identifies and proves an invalid input. -/
  | invalidCuts (reason : Unit.Presentation.Check cuts) (invalid : ¬ Unit.Presentation.Valid cuts)
  /-- The constructed partition is valid, but an ordered cell fails. -/
  | invalidCells (code : Code) (cutsEq : code.1.cuts = cuts) (cellsEq : code.2 = cells)
      (failure : Failure code.2 code.1.intervals)
  /-- The checked display retains the constructed original partition and cells. -/
  | accepted (display : Display) (cutsEq : display.val.1.cuts = cuts) (cellsEq : display.val.2 = cells)

/-- Check raw cuts, then check cells against the one constructed partition cache.

Existing partitions can still use `checkCode` directly. Source containment is
separate evidence for the accepted display, not a result of this finite scan. -/
@[expose] public def checkRaw (cuts : Unit.Presentation.Code) (cells : List Cell.Code) : RawCheck cuts cells :=
  let reason := Unit.Presentation.check cuts
  match reason with
  | .outOfRange index failed =>
      .invalidCuts reason (fun valid => failed (valid.2 (cuts.get index) (List.getElem_mem index.isLt)))
  | .badAdjacent _ _ _ _ _ _ notSorted => .invalidCuts reason (fun valid => notSorted valid.1)
  | .accepted valid =>
      let partition : Unit.Presentation.Display := ⟨cuts, valid⟩
      let code := fromCuts partition cells
      match checkCode code with
      | .rejected failure => .invalidCells code (Unit.Presentation.read_cuts partition) rfl failure
      | .accepted aligned => .accepted ⟨code, aligned⟩ (Unit.Presentation.read_cuts partition) rfl

set_option genInjectivity false in
/-- Complete checking of an existing partition and its proposed source cells. -/
public inductive CompleteCheck (code : Code) where
  /-- The proposed cells do not align with the retained partition. -/
  | invalidCells (failure : Failure code.2 code.1.intervals)
  /-- An aligned cell has an invalid source bound at an endpoint. -/
  | invalidRange (aligned : Valid code)
      (failure : RangeFailure (readCells code.2 code.1.intervals aligned))
  /-- The accepted original frontier retains the checked partition and cells. -/
  | accepted (aligned : Valid code) (range : SourceRange ⟨code, aligned⟩)
      (owner : SourceFrontier value) (readback : owner = read ⟨code, aligned⟩ range)

/-- Check alignment and source containment using their existing finite scans. -/
@[expose] public def checkComplete (code : Code) : CompleteCheck code :=
  match checkCode code with
  | .rejected failure => .invalidCells failure
  | .accepted aligned =>
    let display : Display := ⟨code, aligned⟩
    match checkSourceRange display with
    | .rejected failure => .invalidRange aligned failure
    | .accepted range => .accepted aligned range (read display range) rfl

/-- Checking the quotation of an original frontier accepts and recovers that frontier. -/
public theorem checkComplete_quote (frontier : SourceFrontier value) :
    ∃ (aligned : Valid (quote frontier).val) (range : SourceRange ⟨(quote frontier).val, aligned⟩)
      (owner : SourceFrontier value) (readback : owner = read ⟨(quote frontier).val, aligned⟩ range),
      checkComplete (quote frontier).val = .accepted aligned range owner readback ∧ owner = frontier := by
  cases checked : checkComplete (quote frontier).val with
  | invalidCells failure => exact False.elim (failure.notAligned (quote frontier).property)
  | invalidRange aligned failure =>
      exact False.elim (failure.notSourceRange ⟨(quote frontier).val, aligned⟩ (quote_sourceRange frontier))
  | accepted aligned range owner readback =>
      exact ⟨aligned, range, owner, readback, rfl, readback.trans (read_quote frontier range)⟩

set_option genInjectivity false in
/-- Complete checking of raw cuts and ordered source cells. -/
public inductive CompleteRawCheck (cuts : Unit.Presentation.Code) (cells : List Cell.Code) where
  /-- The cut checker identifies and proves an invalid input. -/
  | invalidCuts (reason : Unit.Presentation.Check cuts) (invalid : ¬ Unit.Presentation.Valid cuts)
  /-- The cells do not align with the constructed partition cache. -/
  | invalidCells (code : Code) (cutsEq : code.1.cuts = cuts) (cellsEq : code.2 = cells)
      (failure : Failure code.2 code.1.intervals)
  /-- A retained cell fails a source endpoint bound. -/
  | invalidRange (display : Display) (cutsEq : display.val.1.cuts = cuts) (cellsEq : display.val.2 = cells)
      (failure : RangeFailure (readCells display.val.2 display.val.1.intervals display.property))
  /-- The checked original frontier uses the constructed partition and proposed cells. -/
  | accepted (display : Display) (cutsEq : display.val.1.cuts = cuts) (cellsEq : display.val.2 = cells)
      (range : SourceRange display) (owner : SourceFrontier value) (readback : owner = read display range)

/-- Check raw cuts and cells, then the source bounds, without rebuilding the partition. -/
@[expose] public def checkCompleteRaw (cuts : Unit.Presentation.Code) (cells : List Cell.Code) :
    CompleteRawCheck cuts cells :=
  match checkRaw cuts cells with
  | .invalidCuts reason invalid => .invalidCuts reason invalid
  | .invalidCells code cutsEq cellsEq failure => .invalidCells code cutsEq cellsEq failure
  | .accepted display cutsEq cellsEq =>
    match checkSourceRange display with
    | .rejected failure => .invalidRange display cutsEq cellsEq failure
    | .accepted range => .accepted display cutsEq cellsEq range (read display range) rfl

/-!
The `check` scan follows both finite lists structurally. `Failure.later`
retains the original occurrence preceding a bad cell, wrong domain or wrong
weight; missing and extra cells retain the remaining list. `fromCuts` composes
the existing normalized-partition presentation with this scan, while `quote`
projects an existing frontier's original partition without rebuilding its cache.
`checkSourceRange` decides `SourceRange` for the fixed pi source by its exact
endpoint criterion and retains the occurrence and inequality of any failure.
`checkComplete` combines the original alignment and range checks for an existing
partition; `checkCompleteRaw` first checks cuts and builds one partition cache.
Both return an original frontier on success and a located proved failure otherwise.
This finite criterion does not recognize arbitrary independently supplied proofs
or decide source containment for arbitrary source functions. `read_quote`,
`quote_read` and `same_iff_read_eq` preserve the original frontier owner and its
proof-field convention. The underlying proof-system and runtime dependencies
remain inherited, not certified by this presentation alone.
-/

end Frontier

namespace Result

open Purelib.Integration.SourceFrontier

/-- A checked pi preparation and an independently supplied finite frontier display. -/
public abbrev Code := Preparation.Display × Frontier.Display

/-- The supplied frontier has the exact retained data of the preparation's output. -/
@[expose] public def Valid (code : Code) : Prop :=
  Frontier.Same code.2 (Frontier.quote (Preparation.read code.1).frontier)

set_option genInjectivity false in
/-- Checking a result either establishes its original binding or proves a frontier mismatch. -/
public inductive Check (code : Code) where
  /-- The supplied frontier is exactly the preparation's output. -/ | valid (proof : Valid code)
  /-- The supplied frontier differs in its retained partition or ordered cell data. -/
  | wrongFrontier (proof : ¬ Valid code)

/-- Compare the supplied frontier with the actual original preparation output. -/
@[expose] public def check (code : Code) : Check code :=
  match Frontier.compare code.2 (Frontier.quote (Preparation.read code.1).frontier) with
  | .isTrue equal => .valid equal
  | .isFalse different => .wrongFrontier different

/-- Derive the binding decision from the detailed result check. -/
@[expose] public def Check.decision {code : Code} (result : Check code) : Decidable (Valid code) :=
  match result with
  | .valid proof => .isTrue proof
  | .wrongFrontier proof => .isFalse proof

/-- Decide the binding using the same typed frontier comparison. -/
@[expose] public def recognize (code : Code) : Decidable (Valid code) := (check code).decision

/-- Compare proposed result fields before deciding their preparation/frontier binding. -/
@[expose] public def compareCode (left right : Code) : Decidable (left = right) := by
  match Preparation.compare left.1 right.1 with
  | .isFalse different =>
      exact .isFalse (fun equal => different (by cases equal; rfl))
  | .isTrue same =>
      have prepEqual : left.1 = right.1 := by
        have readings := (Preparation.same_iff_read_eq left.1 right.1).mp same
        have quoted := congrArg Preparation.quote readings
        rw [Preparation.quote_read, Preparation.quote_read] at quoted
        exact quoted
      match Frontier.compare left.2 right.2 with
      | .isFalse different => exact .isFalse (fun equal => different (by cases equal; exact ⟨rfl, rfl⟩))
      | .isTrue sameFrontier =>
          have frontierEqual : left.2 = right.2 :=
            Subtype.ext (Prod.ext (Unit.Normalized.ext_cuts sameFrontier.1) sameFrontier.2)
          exact .isTrue (Prod.ext prepEqual frontierEqual)

/-- A checked preparation/frontier pair with its exact original binding. -/
public abbrev Display := {code : Code // Valid code}

/-- A checked binding equates the supplied and computed finite frontier displays. -/
public theorem frontier_display_eq (display : Display) :
    display.val.2 = Frontier.quote (Preparation.read display.val.1).frontier := by
  apply Subtype.ext
  exact Prod.ext (Unit.Normalized.ext_cuts display.property.1) display.property.2

/-- The checked binding supplies source containment for the exact retained cells. -/
public theorem sourceRange (display : Display) : Frontier.SourceRange display.val.2 := by
  rw [frontier_display_eq display]
  exact Frontier.quote_sourceRange (Preparation.read display.val.1).frontier

/-- Reading the supplied frontier recovers the preparation's original output. -/
public theorem frontier_eq (display : Display) :
    Frontier.read display.val.2 (sourceRange display) = (Preparation.read display.val.1).frontier := by
  exact ((Frontier.same_iff_read_eq display.val.2
    (Frontier.quote (Preparation.read display.val.1).frontier) (sourceRange display)
    (Frontier.quote_sourceRange (Preparation.read display.val.1).frontier)).mp display.property).trans
      (Frontier.read_quote _ _)

/-- Construct the original result using the supplied retained frontier and its checked binding. -/
@[expose] public def read (display : Display) : Continuous.Result modulus where
  preparation := Preparation.read display.val.1
  frontier := Frontier.read display.val.2 (sourceRange display)
  frontier_eq := frontier_eq display
  accurate := (frontier_eq display).symm ▸ (Preparation.read display.val.1).frontier_width_lt

/-- Quote the original preparation and frontier without rebuilding their retained caches. -/
@[expose] public def quote (result : Continuous.Result modulus) : Display := by
  refine ⟨(Preparation.quote result.preparation, Frontier.quote result.frontier), ?_⟩
  change Frontier.Same (Frontier.quote result.frontier)
    (Frontier.quote (Preparation.read (Preparation.quote result.preparation)).frontier)
  rw [Preparation.read_quote, result.frontier_eq]
  exact ⟨rfl, rfl⟩

/-- The retained preparation determines the original continuous result. -/
public theorem eq_of_preparation_eq (left right : Continuous.Result modulus)
    (equal : left.preparation = right.preparation) : left = right := by
  apply Continuous.Result.ext left right equal
  rw [left.frontier_eq, right.frontier_eq, equal]

/-- Two checked results agree when their retained preparations agree. -/
@[expose] public def Same (left right : Display) : Prop := Preparation.Same left.val.1 right.val.1

/-- Compare checked results through the original preparation comparison. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  Preparation.compare left.val.1 right.val.1

/-- Reading an original result's quotation recovers that original result. -/
public theorem read_quote (result : Continuous.Result modulus) : read (quote result) = result :=
  eq_of_preparation_eq _ _ (Preparation.read_quote result.preparation)

/-- Quoting a reconstructed result recovers its original preparation and frontier displays. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  apply Subtype.ext
  apply Prod.ext
  · exact Preparation.quote_read display.val.1
  · exact Frontier.quote_read display.val.2 (sourceRange display)

/-- The result comparison agrees exactly with equality of original continuous results. -/
public theorem same_iff_read_eq (left right : Display) : Same left right ↔ read left = read right := by
  constructor
  · intro equal
    exact eq_of_preparation_eq _ _ ((Preparation.same_iff_read_eq _ _).mp equal)
  · intro equal
    apply (Preparation.same_iff_read_eq _ _).mpr
    exact congrArg Continuous.Result.preparation equal

/-- The finite presentation of pi results with their checked preparation/frontier binding. -/
@[expose] public def result : Purelib.Data.Presentation Code where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-!
The preparation and frontier are supplied through their existing finite
presentations. `check` compares the original preparation's actual frontier with
the supplied partition and ordered cell data, returning a proved mismatch when
they differ. The checked equality supplies the universal source range and paid
width from the original preparation; it does not decide source containment for
an arbitrary frontier. `read` keeps the supplied partition and cell data, and
quotation projects the original caches. The finite builders and comparison
inherit their existing proof and native-execution obligations.
-/

namespace Input

/-- Proposed preparation and frontier fields before their finite checks. -/
public abbrev Code := Preparation.Code × Frontier.Code

/-- Both finite fields are valid and their reconstructed displays have the original binding. -/
@[expose] public def Valid (code : Code) : Prop :=
  Preparation.Valid code.1 ∧ Frontier.Valid code.2 ∧
    ∀ prepared : Preparation.Valid code.1, ∀ frontier : Frontier.Valid code.2,
      Result.Valid (⟨code.1, prepared⟩, ⟨code.2, frontier⟩)

set_option genInjectivity false in
/-- The first failed finite check, or the checked original result binding. -/
public inductive Check (code : Code) where
  /-- Both finite checks and the original binding hold. -/ | valid (proof : Valid code)
  /-- The preparation check identifies the incorrect retained field. -/
  | invalidPreparation (reason : Preparation.Check code.1) (invalid : ¬ Preparation.Valid code.1)
  /-- The frontier scan identifies the offending original occurrence. -/
  | invalidFrontier (failure : Frontier.Failure code.2.2 code.2.1.intervals)
  /-- Both finite fields pass, but the frontier differs from the preparation output. -/
  | wrongFrontier (prepared : Preparation.Valid code.1) (frontier : Frontier.Valid code.2)
      (different : ¬ Result.Valid (⟨code.1, prepared⟩, ⟨code.2, frontier⟩))

/-- Compare retained result-input checks, including their nested first failure. -/
public def Check.compare {code : Code} (left right : Check code) : Decidable (left = right) := by
  cases left with
  | valid proof =>
    cases right <;> first
      | exact .isTrue rfl
      | exact .isFalse (by intro same; cases same)
  | invalidPreparation reason invalid =>
    cases right with
    | invalidPreparation other _ =>
      match Preparation.Check.compare reason other with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    | _ => exact .isFalse (by intro same; cases same)
  | invalidFrontier failure =>
    cases right with
    | invalidFrontier other =>
      match Frontier.Failure.compare failure other with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    | _ => exact .isFalse (by intro same; cases same)
  | wrongFrontier prepared frontier different =>
    cases right <;> first
      | exact .isTrue rfl
      | exact .isFalse (by intro same; cases same)

/-- Check the existing preparation and frontier validators before checking their binding. -/
@[expose] public def check (code : Code) : Check code :=
  match Preparation.check code.1 with
  | .nonpositiveRequest proof => .invalidPreparation (.nonpositiveRequest proof)
      (fun valid => (not_lt_of_ge proof) valid.1)
  | .wrongVariation proof => .invalidPreparation (.wrongVariation proof) (fun valid => proof valid.2.1)
  | .wrongMesh proof => .invalidPreparation (.wrongMesh proof) (fun valid => proof valid.2.2.1)
  | .wrongPartition proof => .invalidPreparation (.wrongPartition proof) (fun valid => proof valid.2.2.2)
  | .valid prepared =>
    match Frontier.checkCode code.2 with
    | .rejected failure => .invalidFrontier failure
    | .accepted frontier =>
      match Result.check (⟨code.1, prepared⟩, ⟨code.2, frontier⟩) with
      | .wrongFrontier different => .wrongFrontier prepared frontier different
      | .valid binding => .valid ⟨prepared, frontier, fun _ _ => binding⟩

/-- The decision is derived from the detailed first-failure result. -/
@[expose] public def Check.decision {code : Code} (result : Check code) : Decidable (Valid code) :=
  match result with
  | .valid proof => .isTrue proof
  | .invalidPreparation _ invalid => .isFalse (fun valid => invalid valid.1)
  | .invalidFrontier failure => .isFalse (fun valid => failure.notAligned valid.2.1)
  | .wrongFrontier prepared frontier different => .isFalse (fun valid => different (valid.2.2 prepared frontier))

/-- A proposed result whose finite fields and binding passed their checks. -/
public abbrev Display := {code : Code // Valid code}

/-- Recover the existing checked result display from the same input fields. -/
@[expose] public def checked (display : Display) : Result.Display :=
  ⟨(⟨display.val.1, display.property.1⟩, ⟨display.val.2, display.property.2.1⟩),
    display.property.2.2 display.property.1 display.property.2.1⟩

/-- Read the original result through its existing presentation. -/
@[expose] public def read (display : Display) : Continuous.Result modulus := Result.read (checked display)

/-- Quote the original retained preparation and frontier fields. -/
@[expose] public def quote (result : Continuous.Result modulus) : Display :=
  let original := Result.quote result
  ⟨(original.val.1.val, original.val.2.val),
    original.val.1.property, original.val.2.property, fun _ _ => original.property⟩

/-- Reading a quotation recovers the original result and retained caches. -/
public theorem read_quote (result : Continuous.Result modulus) : read (quote result) = result :=
  Result.read_quote result

/-- Quotation after readback recovers the original unchecked finite input. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  apply Subtype.ext
  have equal := congrArg (fun d : Result.Display => (d.val.1.val, d.val.2.val))
    (Result.quote_read (checked display))
  exact equal

/-- Result identity compares the retained original preparations. -/
@[expose] public def Same (left right : Display) : Prop := Result.Same (checked left) (checked right)

/-- Compare checked inputs using the existing result decision. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  Result.compare (checked left) (checked right)

/-- Input equality agrees with equality of the original result owners. -/
public theorem same_iff_read_eq (left right : Display) : Same left right ↔ read left = read right :=
  Result.same_iff_read_eq (checked left) (checked right)

/-- Compare all proposed input fields, including the original retained partitions. -/
@[expose] public def compareCode (left right : Code) : Decidable (left = right) := by
  if request : left.1.1 = right.1.1 then
    if variation : left.1.2.1 = right.1.2.1 then
      if mesh : left.1.2.2.1 = right.1.2.2.1 then
        if preparedCuts : left.1.2.2.2.cuts = right.1.2.2.2.cuts then
          if frontierCuts : left.2.1.cuts = right.2.1.cuts then
            if cells : left.2.2 = right.2.2 then
              exact .isTrue (Prod.ext
                (Prod.ext request
                  (Prod.ext variation (Prod.ext mesh (Unit.Normalized.ext_cuts preparedCuts))))
                (Prod.ext (Unit.Normalized.ext_cuts frontierCuts) cells))
            else exact .isFalse (fun same => cells (congrArg (fun code : Code => code.2.2) same))
          else exact .isFalse (fun same => frontierCuts (congrArg (fun code : Code => code.2.1.cuts) same))
        else exact .isFalse (fun same => preparedCuts (congrArg (fun code : Code => code.1.2.2.2.cuts) same))
      else exact .isFalse (fun same => mesh (congrArg (fun code : Code => code.1.2.2.1) same))
    else exact .isFalse (fun same => variation (congrArg (fun code : Code => code.1.2.1) same))
  else exact .isFalse (fun same => request (congrArg (fun code : Code => code.1.1) same))

end Input

end Result

namespace CommonReading

open Purelib.Integration.SourceFrontier

/-- Finite identity data for a common reading retain its child, parents and tag. -/
public abbrev Code := Partition.Interval × Nat × Partition.Interval × Nat × Partition.Interval × Fraction.Rational

/-- Project a common reading's original child, both indexed parents and its tag. -/
@[expose] public def code {left right : SourceFrontier value}
    (reading : SourceFrontier.CommonReading left right) : Code :=
  (reading.entry.child, reading.entry.leftOwner.index, reading.entry.leftOwner.parent,
    reading.entry.rightOwner.index, reading.entry.rightOwner.parent, reading.tag)

/-- The original indexed child and tag determine the entire common reading. -/
public theorem eq_of_code_eq {left right : SourceFrontier value}
    (first second : SourceFrontier.CommonReading left right) (equal : code first = code second) : first = second := by
  have entryEqual : first.entry = second.entry := Unit.Common.CommonEntry.eq_of_fields first.entry second.entry
    (congrArg (fun c : Code => c.1) equal)
    (congrArg (fun c : Code => c.2.1) equal)
    (congrArg (fun c : Code => c.2.2.2.1) equal)
  have tagEqual : first.tag = second.tag := congrArg (fun c : Code => c.2.2.2.2.2) equal
  cases first with
  | mk firstEntry firstValid firstTag firstInside firstLeft firstRight firstLeftReading firstRightReading
      firstLeftEq firstRightEq firstLeftInside firstRightInside =>
    cases second with
    | mk secondEntry secondValid secondTag secondInside secondLeft secondRight secondLeftReading secondRightReading
        secondLeftEq secondRightEq secondLeftInside secondRightInside =>
      cases entryEqual
      cases tagEqual
      have leftCell : firstLeft = secondLeft := Subtype.ext
        (Option.some.inj (firstLeft.property.1.symm.trans secondLeft.property.1))
      have rightCell : firstRight = secondRight := Subtype.ext
        (Option.some.inj (firstRight.property.1.symm.trans secondRight.property.1))
      cases leftCell
      cases rightCell
      cases firstLeftEq
      cases secondLeftEq
      cases firstRightEq
      cases secondRightEq
      rfl

/-- Decide exact common-reading identity by its finite original child, parents and tag. -/
@[expose] public def compare {left right : SourceFrontier value}
    (first second : SourceFrontier.CommonReading left right) : Decidable (first = second) :=
  if equal : code first = code second then .isTrue (eq_of_code_eq first second equal)
  else .isFalse (fun same => equal (congrArg code same))

set_option genInjectivity false in
/-- Proposed common-child data and both supplied original-source readings. -/
public structure Input where
  /-- The proposed positive unit child interval. -/ child : Partition.Interval
  /-- The original left parent occurrence. -/ leftIndex : Nat
  /-- The proposed left parent interval at that occurrence. -/ leftParent : Partition.Interval
  /-- The original right parent occurrence. -/ rightIndex : Nat
  /-- The proposed right parent interval at that occurrence. -/ rightParent : Partition.Interval
  /-- The common tag retained for both readings. -/ tag : Fraction.Rational
  /-- The supplied left reading. -/ leftReading : Fraction.Rational
  /-- The supplied right reading. -/ rightReading : Fraction.Rational
deriving DecidableEq

/-- A supplied reading matches the actual cell selected at the original occurrence. -/
@[expose] public def CellValid (frontier : SourceFrontier value) (index : Nat)
    (parent : Partition.Interval) (tag reading : Fraction.Rational) : Prop :=
  match Purelib.Data.List.getElem? frontier.cells index with
  | none => False
  | some cell => cell.item.interval = parent ∧ reading = cell.item.readAt tag

/-- Decide an indexed cell lookup and its exact parent and cached reading. -/
@[expose] public def cellRecognize (frontier : SourceFrontier value) (index : Nat)
    (parent : Partition.Interval) (tag reading : Fraction.Rational) :
    Decidable (CellValid frontier index parent tag reading) := by
  unfold CellValid
  split <;> infer_instance

set_option genInjectivity false in
/-- The finite checks required to reconstruct an original common reading. -/
public structure Valid (left right : SourceFrontier value) (input : Input) : Prop where
  /-- The child is a positive unit interval. -/ child : input.child.Valid
  /-- The left occurrence is in range. -/ leftIndex : input.leftIndex < left.partition.intervals.length
  /-- The left occurrence contains the supplied original parent. -/
  leftParent : Purelib.Data.List.getElem? left.partition.intervals input.leftIndex = some input.leftParent
  /-- The left parent contains the entire child. -/
  leftContains : input.leftParent.start ≤ input.child.start ∧ input.child.finish ≤ input.leftParent.finish
  /-- The right occurrence is in range. -/ rightIndex : input.rightIndex < right.partition.intervals.length
  /-- The right occurrence contains the supplied original parent. -/
  rightParent : Purelib.Data.List.getElem? right.partition.intervals input.rightIndex = some input.rightParent
  /-- The right parent contains the entire child. -/
  rightContains : input.rightParent.start ≤ input.child.start ∧ input.child.finish ≤ input.rightParent.finish
  /-- The common tag lies in the child. -/ tag : input.child.start ≤ input.tag ∧ input.tag ≤ input.child.finish
  /-- The left original cell and supplied reading match. -/
  leftCell : CellValid left input.leftIndex input.leftParent input.tag input.leftReading
  /-- The right original cell and supplied reading match. -/
  rightCell : CellValid right input.rightIndex input.rightParent input.tag input.rightReading

set_option genInjectivity false in
/-- A finite common-reading check identifies and proves its first failed condition. -/
public inductive Check (left right : SourceFrontier value) (input : Input) where
  /-- Every finite condition holds. -/ | valid (proof : Valid left right input)
  /-- The child is not a positive unit interval. -/ | invalidChild (proof : ¬ input.child.Valid)
  /-- The left occurrence is outside the original interval list. -/
  | leftIndex (proof : ¬ input.leftIndex < left.partition.intervals.length)
  /-- The left occurrence does not have the supplied parent. -/
  | leftParent (proof : Purelib.Data.List.getElem? left.partition.intervals input.leftIndex ≠ some input.leftParent)
  /-- The supplied left parent does not contain the child. -/
  | leftContains (proof : ¬ (input.leftParent.start ≤ input.child.start ∧ input.child.finish ≤ input.leftParent.finish))
  /-- The right occurrence is outside the original interval list. -/
  | rightIndex (proof : ¬ input.rightIndex < right.partition.intervals.length)
  /-- The right occurrence does not have the supplied parent. -/
  | rightParent (proof : Purelib.Data.List.getElem? right.partition.intervals input.rightIndex ≠ some input.rightParent)
  /-- The supplied right parent does not contain the child. -/
  | rightContains (proof : ¬ (input.rightParent.start ≤ input.child.start ∧
      input.child.finish ≤ input.rightParent.finish))
  /-- The common tag is outside the supplied child. -/
  | invalidTag (proof : ¬ (input.child.start ≤ input.tag ∧ input.tag ≤ input.child.finish))
  /-- The original left cell or supplied reading mismatches. -/
  | leftCell (proof : ¬ CellValid left input.leftIndex input.leftParent input.tag input.leftReading)
  /-- The original right cell or supplied reading mismatches. -/
  | rightCell (proof : ¬ CellValid right input.rightIndex input.rightParent input.tag input.rightReading)

/-- Compare common-reading checks for the same two owners and retained input. -/
public def Check.compare {left right : SourceFrontier value} {input : Input}
    (first second : Check left right input) : Decidable (first = second) := by
  cases first <;> cases second <;> first
    | exact .isTrue rfl
    | exact .isFalse (by intro same; cases same)

/-- Check the original indexed parents, containment, tag and both exact cell readings. -/
@[expose] public def check (left right : SourceFrontier value) (input : Input) : Check left right input :=
  letI : Decidable input.child.Valid := inferInstanceAs
    (Decidable (0 ≤ input.child.start ∧ input.child.start < input.child.finish ∧ input.child.finish ≤ 1))
  letI := cellRecognize left input.leftIndex input.leftParent input.tag input.leftReading
  letI := cellRecognize right input.rightIndex input.rightParent input.tag input.rightReading
  if child : input.child.Valid then
    if leftIndex : input.leftIndex < left.partition.intervals.length then
      if leftParent : Purelib.Data.List.getElem? left.partition.intervals input.leftIndex = some input.leftParent then
        if leftContains : input.leftParent.start ≤ input.child.start ∧ input.child.finish ≤ input.leftParent.finish then
          if rightIndex : input.rightIndex < right.partition.intervals.length then
            if rightParent : Purelib.Data.List.getElem? right.partition.intervals input.rightIndex =
                some input.rightParent then
              if rightContains : input.rightParent.start ≤ input.child.start ∧
                  input.child.finish ≤ input.rightParent.finish then
                if tag : input.child.start ≤ input.tag ∧ input.tag ≤ input.child.finish then
                  if leftCell : CellValid left input.leftIndex input.leftParent input.tag input.leftReading then
                    if rightCell : CellValid right input.rightIndex input.rightParent input.tag input.rightReading then
                      .valid ⟨child, leftIndex, leftParent, leftContains, rightIndex, rightParent, rightContains,
                        tag, leftCell, rightCell⟩
                    else .rightCell rightCell
                  else .leftCell leftCell
                else .invalidTag tag
              else .rightContains rightContains
            else .rightParent rightParent
          else .rightIndex rightIndex
        else .leftContains leftContains
      else .leftParent leftParent
    else .leftIndex leftIndex
  else .invalidChild child

/-- Derive a validity decision from the original detailed check result. -/
@[expose] public def Check.decision {left right : SourceFrontier value} {input : Input}
    (result : Check left right input) : Decidable (Valid left right input) :=
  match result with
  | .valid proof => .isTrue proof
  | .invalidChild failure => .isFalse (fun valid => failure valid.child)
  | .leftIndex failure => .isFalse (fun valid => failure valid.leftIndex)
  | .leftParent failure => .isFalse (fun valid => failure valid.leftParent)
  | .leftContains failure => .isFalse (fun valid => failure valid.leftContains)
  | .rightIndex failure => .isFalse (fun valid => failure valid.rightIndex)
  | .rightParent failure => .isFalse (fun valid => failure valid.rightParent)
  | .rightContains failure => .isFalse (fun valid => failure valid.rightContains)
  | .invalidTag failure => .isFalse (fun valid => failure valid.tag)
  | .leftCell failure => .isFalse (fun valid => failure valid.leftCell)
  | .rightCell failure => .isFalse (fun valid => failure valid.rightCell)

/-- Decide validity with the same typed finite checker. -/
@[expose] public def recognize (left right : SourceFrontier value) (input : Input) :
    Decidable (Valid left right input) := (check left right input).decision

/-- A checked proposal at the two exact source frontiers. -/
public abbrev Display (left right : SourceFrontier value) := {input : Input // Valid left right input}

/-- Construct the original common entry using both supplied indexed parents. -/
@[expose] public def entry {left right : SourceFrontier value} (display : Display left right) :
    Unit.Common.CommonEntry left.partition right.partition :=
  ⟨display.val.child,
    ⟨display.val.leftIndex, display.val.leftParent, display.property.leftParent,
      display.property.leftContains.1, display.property.leftContains.2⟩,
    ⟨display.val.rightIndex, display.val.rightParent, display.property.rightParent,
      display.property.rightContains.1, display.property.rightContains.2⟩⟩

/-- Build the original common reading, retaining the proposed tag and both supplied readings. -/
@[expose] public def read {left right : SourceFrontier value} (display : Display left right) :
    SourceFrontier.CommonReading left right := by
  let commonEntry := entry display
  let leftCell := left.partitioned.cellAtOwner commonEntry.leftOwner
  let rightCell := right.partitioned.cellAtOwner commonEntry.rightOwner
  have leftValid := display.property.leftCell
  have rightValid := display.property.rightCell
  unfold CellValid at leftValid rightValid
  have leftAt : Purelib.Data.List.getElem? left.cells display.val.leftIndex = some leftCell.val :=
    leftCell.property.1
  have rightAt : Purelib.Data.List.getElem? right.cells display.val.rightIndex = some rightCell.val :=
    rightCell.property.1
  rw [leftAt] at leftValid
  rw [rightAt] at rightValid
  exact SourceFrontier.readCommonFromPair left right commonEntry display.property.child display.val.tag
    display.property.tag ⟨(display.val.leftReading, display.val.rightReading), leftValid.2, rightValid.2⟩

/-- Project all finite data and supplied readings from the original common reading. -/
@[expose] public def input {left right : SourceFrontier value}
    (reading : SourceFrontier.CommonReading left right) : Input :=
  ⟨reading.entry.child, reading.entry.leftOwner.index, reading.entry.leftOwner.parent,
    reading.entry.rightOwner.index, reading.entry.rightOwner.parent, reading.tag, reading.leftReading,
    reading.rightReading⟩

/-- An original common reading satisfies every finite check on its projected input. -/
public theorem valid_input {left right : SourceFrontier value} (reading : SourceFrontier.CommonReading left right) :
    Valid left right (input reading) := by
  refine ⟨reading.valid, ?_, reading.entry.leftOwner.at_index,
    ⟨reading.entry.leftOwner.start_le, reading.entry.leftOwner.finish_le⟩, ?_,
    reading.entry.rightOwner.at_index, ⟨reading.entry.rightOwner.start_le, reading.entry.rightOwner.finish_le⟩,
    reading.tag_inside, ?_, ?_⟩
  · exact Purelib.Data.List.index_lt_length_of_getElem? _ _ _ reading.entry.leftOwner.at_index
  · exact Purelib.Data.List.index_lt_length_of_getElem? _ _ _ reading.entry.rightOwner.at_index
  · change CellValid left reading.entry.leftOwner.index reading.entry.leftOwner.parent reading.tag reading.leftReading
    unfold CellValid
    rw [reading.leftCell.property.1]
    exact ⟨reading.leftCell.property.2, reading.left_reading_eq⟩
  · change CellValid right reading.entry.rightOwner.index reading.entry.rightOwner.parent
      reading.tag reading.rightReading
    unfold CellValid
    rw [reading.rightCell.property.1]
    exact ⟨reading.rightCell.property.2, reading.right_reading_eq⟩

/-- Quote the exact finite fields and readings of an original common reading. -/
@[expose] public def quote {left right : SourceFrontier value}
    (reading : SourceFrontier.CommonReading left right) : Display left right := ⟨input reading, valid_input reading⟩

/-- Reading an original quotation recovers its original common-reading owner. -/
public theorem read_quote {left right : SourceFrontier value} (reading : SourceFrontier.CommonReading left right) :
    read (quote reading) = reading := by
  apply eq_of_code_eq
  rfl

/-- Quoting a reconstructed reading recovers every supplied finite field and reading. -/
public theorem quote_read {left right : SourceFrontier value} (display : Display left right) :
    quote (read display) = display := by
  apply Subtype.ext
  cases display with
  | mk input valid => cases input; rfl

/-- Presentations agree exactly when their supplied finite fields agree. -/
@[expose] public def Same {left right : SourceFrontier value} (first second : Display left right) : Prop :=
  first.val = second.val

/-- Decide equality of the supplied finite common-reading data. -/
@[expose] public def compareDisplay {left right : SourceFrontier value} (first second : Display left right) :
    Decidable (Same first second) := inferInstanceAs (Decidable (first.val = second.val))

/-- Presentation equality agrees with equality of original common-reading owners. -/
public theorem same_iff_read_eq {left right : SourceFrontier value} (first second : Display left right) :
    Same first second ↔ read first = read second := by
  constructor
  · intro same
    have equal : first = second := Subtype.ext same
    cases equal
    rfl
  · intro same
    have quoted := congrArg quote same
    rw [quote_read, quote_read] at quoted
    exact congrArg Subtype.val quoted

/-- The finite common-reading presentation at the exact original source frontiers. -/
@[expose] public def commonReading (left right : SourceFrontier value) : Purelib.Data.Presentation Input where
  Valid := Valid left right
  recognize := recognize left right
  Same := Same
  compare := compareDisplay
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-!
The finite input retains the child, both original parent occurrences, common
tag and both supplied readings. `check` decides the child, index, parent,
containment and tag conditions, then checks both original cell lookups and
their readings. Each rejection carries the failed condition. `read` uses the
original `readCommonFromPair` constructor and the supplied readings, while
`quote`, `read_quote`, `quote_read` and `same_iff_read_eq` preserve the original
owner. Source containment at every rational point comes from the two fixed
frontiers; it is not decided by this finite checker. Their proof-presentation
and native-runtime obligations remain separate.
-/

end CommonReading

namespace CommonReadings

open Purelib.Integration.SourceFrontier

/-- Equal ordered common readings and common-partition cuts determine the original collection. -/
public theorem eq_of_fields {left right : SourceFrontier value}
    (first second : SourceFrontier.CommonReadings left right)
    (cuts : first.refinement.partition.cuts = second.refinement.partition.cuts)
    (readings : first.readings = second.readings) : first = second := by
  apply SourceFrontier.CommonReadings.ext first second
  · apply Unit.Common.CommonRefinement.eq_of_fields
    · exact Unit.Normalized.ext_cuts cuts
    · exact first.entries_eq.symm.trans ((congrArg (List.map SourceFrontier.CommonReading.entry) readings).trans
        second.entries_eq)
  · exact readings

/-- Decide equality of the original ordered common readings and their retained partition. -/
@[expose] public def compare {left right : SourceFrontier value}
    (first second : SourceFrontier.CommonReadings left right) : Decidable (first = second) := by
  letI (a b : SourceFrontier.CommonReading left right) : Decidable (a = b) := CommonReading.compare a b
  if cuts : first.refinement.partition.cuts = second.refinement.partition.cuts then
    if readings : first.readings = second.readings then
      exact .isTrue (eq_of_fields first second cuts readings)
    else
      exact .isFalse (fun equal => readings (congrArg SourceFrontier.CommonReadings.readings equal))
  else
    exact .isFalse (fun equal => cuts (congrArg (fun common => common.refinement.partition.cuts) equal))

/-- Ordered proposed readings align with the exact intervals retained by a common partition. -/
@[expose] public def Aligned (left right : SourceFrontier value) :
    List CommonReading.Input → List Partition.Interval → Prop
  | [], [] => True
  | input :: inputs, interval :: intervals =>
      CommonReading.Valid left right input ∧ input.child = interval ∧ Aligned left right inputs intervals
  | _, _ => False

set_option genInjectivity false in
/-- A located failure in the original ordered common-reading and interval lists. -/
public inductive Failure (left right : SourceFrontier value) :
    List CommonReading.Input → List Partition.Interval → Type where
  /-- An original interval has no proposed reading. -/
  | missingReading (interval : Partition.Interval) (intervals : List Partition.Interval) :
      Failure left right [] (interval :: intervals)
  /-- A proposed reading has no original interval. -/
  | extraReading (input : CommonReading.Input) (inputs : List CommonReading.Input) :
      Failure left right (input :: inputs) []
  /-- The current original child, parents, tag or reading fails its finite check. -/
  | badReading (input : CommonReading.Input) (inputs : List CommonReading.Input)
      (interval : Partition.Interval) (intervals : List Partition.Interval)
      (reason : CommonReading.Check left right input)
      (invalid : ¬ CommonReading.Valid left right input) : Failure left right (input :: inputs) (interval :: intervals)
  /-- The current reading belongs to a different child than the current retained interval. -/
  | wrongChild (input : CommonReading.Input) (inputs : List CommonReading.Input)
      (interval : Partition.Interval) (intervals : List Partition.Interval) (different : input.child ≠ interval) :
      Failure left right (input :: inputs) (interval :: intervals)
  /-- A later occurrence fails after the displayed original reading and interval. -/
  | later (input : CommonReading.Input) (interval : Partition.Interval) {inputs : List CommonReading.Input}
      {intervals : List Partition.Interval} (failure : Failure left right inputs intervals) :
      Failure left right (input :: inputs) (interval :: intervals)

/-- Compare located common-reading failures with their original owners and indices. -/
public def Failure.compare {left right : SourceFrontier value} {inputs : List CommonReading.Input}
    {intervals : List Partition.Interval} (first second : Failure left right inputs intervals) :
    Decidable (first = second) := by
  cases first with
  | missingReading interval intervals =>
    cases second
    exact .isTrue rfl
  | extraReading input inputs =>
    cases second
    exact .isTrue rfl
  | badReading input inputs interval intervals reason invalid =>
    cases second with
    | badReading _ _ _ _ other _ =>
      match CommonReading.Check.compare reason other with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    | _ => exact .isFalse (by intro same; cases same)
  | wrongChild input inputs interval intervals different =>
    cases second <;> first
      | exact .isTrue rfl
      | exact .isFalse (by intro same; cases same)
  | later input interval failure =>
    cases second with
    | later _ _ other =>
      match Failure.compare failure other with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    | _ => exact .isFalse (by intro same; cases same)
termination_by structural first

/-- Every located failure proves that the proposed lists are not aligned. -/
public theorem Failure.notAligned {left right : SourceFrontier value}
    {inputs : List CommonReading.Input} {intervals : List Partition.Interval}
    (failure : Failure left right inputs intervals) : ¬ Aligned left right inputs intervals := by
  induction failure with
  | missingReading => exact fun invalid => invalid
  | extraReading => exact fun invalid => invalid
  | badReading _ _ _ _ _ invalid => exact fun aligned => invalid aligned.1
  | wrongChild _ _ _ _ different => exact fun aligned => different aligned.2.1
  | later _ _ _ ih => exact fun aligned => ih aligned.2.2

set_option genInjectivity false in
/-- A total finite scan returns original ordered alignment or a located failure. -/
public inductive Check (left right : SourceFrontier value)
    (inputs : List CommonReading.Input) (intervals : List Partition.Interval) where
  /-- Every original reading and child interval aligns. -/ | accepted (aligned : Aligned left right inputs intervals)
  /-- A specific input or occurrence fails. -/ | rejected (failure : Failure left right inputs intervals)

/-- Scan the supplied readings and retained intervals together in order. -/
@[expose] public def check (left right : SourceFrontier value) :
    (inputs : List CommonReading.Input) → (intervals : List Partition.Interval) → Check left right inputs intervals
  | [], [] => .accepted True.intro
  | [], interval :: intervals => .rejected (.missingReading interval intervals)
  | input :: inputs, [] => .rejected (.extraReading input inputs)
  | input :: inputs, interval :: intervals =>
      let reason := CommonReading.check left right input
      match reason.decision with
      | .isFalse invalid => .rejected (.badReading input inputs interval intervals reason invalid)
      | .isTrue valid =>
        if child : input.child = interval then
          match check left right inputs intervals with
          | .accepted tail => .accepted ⟨valid, child, tail⟩
          | .rejected failure => .rejected (.later input interval failure)
        else .rejected (.wrongChild input inputs interval intervals child)

/-- Decide finite ordered alignment using the same located check. -/
@[expose] public def recognize (left right : SourceFrontier value) (inputs : List CommonReading.Input)
    (intervals : List Partition.Interval) : Decidable (Aligned left right inputs intervals) :=
  match check left right inputs intervals with
  | .accepted aligned => .isTrue aligned
  | .rejected failure => .isFalse failure.notAligned

/-- Reconstruct the original common readings from their aligned proposed inputs. -/
@[expose] public def readReadings (left right : SourceFrontier value) :
    (inputs : List CommonReading.Input) → (intervals : List Partition.Interval) →
      Aligned left right inputs intervals → List (SourceFrontier.CommonReading left right)
  | [], _, _ => []
  | _ :: _, [], impossible => False.elim impossible
  | input :: inputs, _ :: intervals, aligned =>
      CommonReading.read ⟨input, aligned.1⟩ :: readReadings left right inputs intervals aligned.2.2

/-- Reconstructed children are exactly the supplied original interval occurrences. -/
public theorem readReadings_children (left right : SourceFrontier value) :
    ∀ (inputs : List CommonReading.Input) (intervals : List Partition.Interval)
      (aligned : Aligned left right inputs intervals),
      (readReadings left right inputs intervals aligned).map (fun reading => reading.entry.child) = intervals
  | [], [], _ => rfl
  | [], _ :: _, impossible => False.elim impossible
  | _ :: _, [], impossible => False.elim impossible
  | input :: inputs, interval :: intervals, aligned => by
      change input.child :: (readReadings left right inputs intervals aligned.2.2).map
        (fun reading => reading.entry.child) = interval :: intervals
      exact congrArg₂ List.cons aligned.2.1 (readReadings_children left right inputs intervals aligned.2.2)

/-- Project the retained finite fields of every original common reading in order. -/
@[expose] public def quoteReadings {left right : SourceFrontier value}
    (readings : List (SourceFrontier.CommonReading left right)) : List CommonReading.Input :=
  readings.map CommonReading.input

/-- Original readings whose children match the intervals satisfy the finite alignment scan. -/
public theorem aligned_quoteReadings {left right : SourceFrontier value} :
    ∀ (readings : List (SourceFrontier.CommonReading left right)) (intervals : List Partition.Interval),
      readings.map (fun reading => reading.entry.child) = intervals →
        Aligned left right (quoteReadings readings) intervals
  | [], [], _ => True.intro
  | [], _ :: _, equal => by cases equal
  | _ :: _, [], equal => by cases equal
  | reading :: readings, interval :: intervals, equal =>
      ⟨CommonReading.valid_input reading, (List.cons.inj equal).1,
        aligned_quoteReadings readings intervals (List.cons.inj equal).2⟩

/-- Reconstructing projected readings recovers the original ordered reading owners. -/
public theorem readReadings_quoteReadings {left right : SourceFrontier value} :
    ∀ (readings : List (SourceFrontier.CommonReading left right)) (intervals : List Partition.Interval)
      (aligned : Aligned left right (quoteReadings readings) intervals),
      readReadings left right (quoteReadings readings) intervals aligned = readings
  | [], [], _ => rfl
  | [], _ :: _, impossible => False.elim impossible
  | _ :: _, [], impossible => False.elim impossible
  | reading :: readings, _ :: intervals, aligned => by
      change CommonReading.read ⟨CommonReading.input reading, aligned.1⟩ ::
        readReadings left right (quoteReadings readings) intervals aligned.2.2 = reading :: readings
      rw [show CommonReading.read ⟨CommonReading.input reading, aligned.1⟩ = reading from
        CommonReading.read_quote reading, readReadings_quoteReadings readings intervals aligned.2.2]

/-- Projecting reconstructed readings recovers their exact supplied finite fields. -/
public theorem quoteReadings_readReadings (left right : SourceFrontier value) :
    ∀ (inputs : List CommonReading.Input) (intervals : List Partition.Interval)
      (aligned : Aligned left right inputs intervals),
      quoteReadings (readReadings left right inputs intervals aligned) = inputs
  | [], [], _ => rfl
  | [], _ :: _, impossible => False.elim impossible
  | _ :: _, [], impossible => False.elim impossible
  | input :: inputs, _ :: intervals, aligned => by
      change (CommonReading.quote (CommonReading.read ⟨input, aligned.1⟩)).val ::
        quoteReadings (readReadings left right inputs intervals aligned.2.2) = input :: inputs
      exact congrArg₂ List.cons (congrArg Subtype.val (CommonReading.quote_read ⟨input, aligned.1⟩))
        (quoteReadings_readReadings left right inputs intervals aligned.2.2)

/-- Proposed ordered readings retain an original normalized common partition and its interval cache. -/
public abbrev Code := Unit.Normalized × List CommonReading.Input

/-- Construct a fresh proposed common partition from an already checked cut display. -/
@[expose] public def fromCuts (partition : Unit.Presentation.Display)
    (inputs : List CommonReading.Input) : Code := (Unit.Presentation.read partition, inputs)

/-- Check proposed readings against the original common partition's retained interval cache. -/
@[expose] public def checkCode (left right : SourceFrontier value) (code : Code) :
    Check left right code.2 code.1.intervals := check left right code.2 code.1.intervals

/-- Every proposed reading aligns with its retained original child interval. -/
@[expose] public def Valid (left right : SourceFrontier value) (code : Code) : Prop :=
  Aligned left right code.2 code.1.intervals

/-- Decide collection validity through the same located ordered scan. -/
@[expose] public def validDecision (left right : SourceFrontier value) (code : Code) :
    Decidable (Valid left right code) := recognize left right code.2 code.1.intervals

/-- An original common partition and its checked ordered finite readings. -/
public abbrev Display (left right : SourceFrontier value) := {code : Code // Valid left right code}

/-- Construct the original common-reading collection, retaining the supplied partition and readings. -/
@[expose] public def read {left right : SourceFrontier value} (display : Display left right) :
    SourceFrontier.CommonReadings left right := by
  let readings := readReadings left right display.val.2 display.val.1.intervals display.property
  have children : (readings.map SourceFrontier.CommonReading.entry).map
      Unit.Common.CommonEntry.child = display.val.1.intervals := by
    rw [Purelib.Data.List.Map.map_map]
    exact readReadings_children left right display.val.2 display.val.1.intervals display.property
  exact ⟨⟨display.val.1, readings.map SourceFrontier.CommonReading.entry, children⟩, readings, rfl⟩

/-- Quote the original retained partition and ordered reading fields without rebuilding its cache. -/
@[expose] public def quote {left right : SourceFrontier value}
    (common : SourceFrontier.CommonReadings left right) : Display left right := by
  refine ⟨(common.refinement.partition, quoteReadings common.readings), ?_⟩
  apply aligned_quoteReadings
  have children := congrArg (List.map Unit.Common.CommonEntry.child) common.entries_eq
  rw [Purelib.Data.List.Map.map_map] at children
  exact children.trans common.refinement.children_eq

/-- Reading a quoted collection recovers its exact original partition, entries and readings. -/
public theorem read_quote {left right : SourceFrontier value} (common : SourceFrontier.CommonReadings left right) :
    read (quote common) = common := by
  apply eq_of_fields
  · rfl
  · exact readReadings_quoteReadings common.readings common.refinement.partition.intervals _

/-- Quoting a reconstructed collection recovers its supplied partition and ordered readings. -/
public theorem quote_read {left right : SourceFrontier value} (display : Display left right) :
    quote (read display) = display := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact quoteReadings_readReadings left right display.val.2 display.val.1.intervals display.property

/-- Displays agree when their original partition cuts and every ordered reading field agree. -/
@[expose] public def Same {left right : SourceFrontier value} (first second : Display left right) : Prop :=
  first.val.1.cuts = second.val.1.cuts ∧ first.val.2 = second.val.2

/-- Compare retained partition cuts and ordered common-reading inputs. -/
@[expose] public def compareDisplay {left right : SourceFrontier value} (first second : Display left right) :
    Decidable (Same first second) := inferInstanceAs
      (Decidable (first.val.1.cuts = second.val.1.cuts ∧ first.val.2 = second.val.2))

/-- Display equality agrees exactly with equality of original common-reading collections. -/
public theorem same_iff_read_eq {left right : SourceFrontier value} (first second : Display left right) :
    Same first second ↔ read first = read second := by
  constructor
  · intro same
    have partition : first.val.1 = second.val.1 := Unit.Normalized.ext_cuts same.1
    have equal : first = second := Subtype.ext (Prod.ext partition same.2)
    cases equal
    rfl
  · intro same
    have quoted := congrArg quote same
    rw [quote_read, quote_read] at quoted
    exact ⟨congrArg (fun display : Display left right => display.val.1.cuts) quoted,
      congrArg (fun display : Display left right => display.val.2) quoted⟩

/-- The finite presentation of original common-reading collections at fixed pi frontiers. -/
@[expose] public def commonReadings (left right : SourceFrontier value) : Purelib.Data.Presentation Code where
  Valid := Valid left right
  recognize := validDecision left right
  Same := Same
  compare := compareDisplay
  same_laws := ⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
    fun h k => ⟨h.1.trans k.1, h.2.trans k.2⟩⟩

set_option genInjectivity false in
/-- The result of checking raw common-partition cuts and ordered readings. -/
public inductive RawCheck (left right : SourceFrontier value)
    (cuts : Unit.Presentation.Code) (inputs : List CommonReading.Input) where
  /-- The original cut checker identifies and proves an invalid input. -/
  | invalidCuts (reason : Unit.Presentation.Check cuts) (invalid : ¬ Unit.Presentation.Valid cuts)
  /-- The constructed partition is valid, but an ordered reading fails. -/
  | invalidReadings (code : Code) (cutsEq : code.1.cuts = cuts) (inputsEq : code.2 = inputs)
      (failure : Failure left right code.2 code.1.intervals)
  /-- The checked display retains the constructed original partition and readings. -/
  | accepted (display : Display left right) (cutsEq : display.val.1.cuts = cuts)
      (inputsEq : display.val.2 = inputs)

/-- Check raw cuts, then check readings against the one constructed partition cache.

The existing cached-owner `checkCode` remains available when a partition is
already retained. Rejected cuts keep the original located failure; accepted
cuts build one original partition whose intervals are used by the reading scan. -/
@[expose] public def checkRaw (left right : SourceFrontier value)
    (cuts : Unit.Presentation.Code) (inputs : List CommonReading.Input) : RawCheck left right cuts inputs :=
  let reason := Unit.Presentation.check cuts
  match reason with
  | .outOfRange index failed =>
      .invalidCuts reason (fun valid => failed (valid.2 (cuts.get index) (List.getElem_mem index.isLt)))
  | .badAdjacent _ _ _ _ _ _ notSorted => .invalidCuts reason (fun valid => notSorted valid.1)
  | .accepted valid =>
      let partition : Unit.Presentation.Display := ⟨cuts, valid⟩
      let code := fromCuts partition inputs
      match checkCode left right code with
      | .rejected failure => .invalidReadings code (Unit.Presentation.read_cuts partition) rfl failure
      | .accepted aligned => .accepted ⟨code, aligned⟩ (Unit.Presentation.read_cuts partition) rfl

/-!
The supplied normalized partition is the original owner, including its cached
intervals; its cuts have the existing unit-partition presentation. `fromCuts`
constructs a fresh owner only for an actual raw-cut request. The scan follows
the supplied reading inputs and cached intervals structurally, checking each
original common reading and its child. Missing, extra and wrong-order children
are located failures. `read` retains the supplied partition and reconstructed
original indexed entries without requiring the canonical common refinement.
Universal source-range certificates remain inherited from the two fixed
frontiers; proof-presentation and native-runtime obligations remain separate.
-/

end CommonReadings

namespace Continuation

open Purelib.Approximation
open Purelib.Integration.SourceFrontier

set_option genInjectivity false in
/-- Proposed continuation fields at the exact saved frontier.

The refined case retains the original bank, fresh result and indexed common
readings. Its split certificate is supplied for those exact retained data. -/
public inductive Code (previous : SourceFrontier value) where
  /-- A request proposed to reuse the saved frontier. -/
  | reused (request : AccuracyRequest)
  /-- A request with its retained bank, fresh result and common observations. -/
  | refined (request : AccuracyRequest) (cached : List (SourcePoint value))
      (fresh : Continuous.Result modulus) (common : SourceFrontier.CommonReadings previous fresh.frontier)
      (split : IntegrationFrontierRefines common.intersection.cells previous.cells)

/-- The proposed branch pays the request or retains the fresh result for that request. -/
@[expose] public def Valid {previous : SourceFrontier value} : Code previous → Prop
  | .reused request => (integralBound previous.cells).width < request.tolerance
  | .refined request _ fresh _ _ => fresh.preparation.request = request

set_option genInjectivity false in
/-- A continuation check returns the exact branch-specific failure. -/
public inductive Check {previous : SourceFrontier value} (code : Code previous) where
  /-- The proposed branch satisfies its finite binding. -/ | valid (proof : Valid code)
  /-- The reused frontier does not pay the proposed request. -/ | invalidReuse (proof : ¬ Valid code)
  /-- The fresh result retains a different request. -/ | wrongFresh (proof : ¬ Valid code)

/-- Check the saved width or compare the fresh result's original request. -/
@[expose] public def check {previous : SourceFrontier value} (code : Code previous) : Check code :=
  match code with
  | .reused request =>
      if accurate : (integralBound previous.cells).width < request.tolerance then .valid accurate
      else .invalidReuse accurate
  | .refined request _ fresh _ _ =>
      if equal : fresh.preparation.request = request then .valid equal else .wrongFresh equal

/-- Decide the branch binding with the same typed check. -/
@[expose] public def recognize {previous : SourceFrontier value} (code : Code previous) : Decidable (Valid code) :=
  match check code with
  | .valid proof => .isTrue proof
  | .invalidReuse proof => .isFalse proof
  | .wrongFresh proof => .isFalse proof

/-- A proposed continuation with its checked branch binding. -/
public abbrev Display (previous : SourceFrontier value) := {code : Code previous // Valid code}

/-- The request determines the original cached producer result. -/
public theorem fresh_eq_iff (previous : SourceFrontier value) (request : AccuracyRequest)
    (cached : List (SourcePoint value)) (fresh : Continuous.Result modulus) :
    fresh = producer.requestCached (Producer.effectiveBank previous cached) request ↔
      fresh.preparation.request = request := by
  constructor
  · intro equal
    have requests := congrArg (fun result : Continuous.Result modulus => result.preparation.request) equal
    rw [producer.requestCached_eq] at requests
    exact requests
  · intro equal
    apply Result.eq_of_preparation_eq
    apply Preparation.eq_of_request_eq
    rw [producer.requestCached_eq]
    exact equal

/-- Construct the original continuation, preserving its supplied bank and indexed common readings. -/
@[expose] public def read {previous : SourceFrontier value} (display : Display previous) :
    Producer.Continuation producer previous :=
  match display with
  | ⟨.reused request, accurate⟩ => .reused request accurate
  | ⟨.refined request cached fresh common split, equal⟩ =>
      .refined request cached fresh ((fresh_eq_iff previous request cached fresh).mpr equal) common split

/-- Quote either original continuation branch and its exact retained data. -/
@[expose] public def quote {previous : SourceFrontier value}
    (continuation : Producer.Continuation producer previous) : Display previous :=
  match continuation with
  | .reused request accurate => ⟨.reused request, accurate⟩
  | .refined request cached fresh freshEq common split =>
      ⟨.refined request cached fresh common split, (fresh_eq_iff previous request cached fresh).mp freshEq⟩

/-- Reading the quotation recovers the original indexed continuation. -/
public theorem read_quote {previous : SourceFrontier value} (continuation : Producer.Continuation producer previous) :
    read (quote continuation) = continuation := by
  cases continuation <;> rfl

/-- Quoting a reconstructed continuation recovers its retained branch and data. -/
public theorem quote_read {previous : SourceFrontier value} (display : Display previous) :
    quote (read display) = display := by
  cases display with
  | mk code valid =>
    cases code <;> rfl

/-- Decide equality of original source points through their finite presentations. -/
@[expose] public def comparePoint (first second : SourcePoint value) : Decidable (first = second) :=
  match Presentation.compare (Presentation.quote first) (Presentation.quote second) with
  | .isTrue same => .isTrue ((Presentation.read_quote first).symm.trans
      (((Presentation.same_iff_read_eq _ _).mp same).trans (Presentation.read_quote second)))
  | .isFalse different => .isFalse (fun equal => different (congrArg (fun p => (Presentation.quote p).val) equal))

/-- Decide equality of original continuous results through their retained requests. -/
@[expose] public def compareResult (first second : Continuous.Result modulus) : Decidable (first = second) :=
  if equal : first.preparation.request = second.preparation.request then
    .isTrue (Result.eq_of_preparation_eq first second
      (Preparation.eq_of_request_eq first.preparation second.preparation equal))
  else .isFalse (fun same => equal (congrArg (fun r => r.preparation.request) same))

/-- Decide original continuation equality, retaining branch, request, bank and indexed common readings. -/
@[expose] public def compareOwner {previous : SourceFrontier value}
    (first second : Producer.Continuation producer previous) : Decidable (first = second) := by
  letI (a b : SourcePoint value) : Decidable (a = b) := comparePoint a b
  cases first with
  | reused firstRequest firstAccurate =>
    cases second with
    | reused secondRequest secondAccurate =>
      if equal : firstRequest = secondRequest then
        cases equal
        exact .isTrue rfl
      else
        exact .isFalse (fun same => equal (congrArg Producer.Continuation.request same))
    | refined => exact .isFalse (fun same => by cases same)
  | refined firstRequest firstCached firstFresh firstFreshEq firstCommon firstSplit =>
    cases second with
    | reused => exact .isFalse (fun same => by cases same)
    | refined secondRequest secondCached secondFresh secondFreshEq secondCommon secondSplit =>
      if requestEqual : firstRequest = secondRequest then
        cases requestEqual
        if cachedEqual : firstCached = secondCached then
          cases cachedEqual
          match compareResult firstFresh secondFresh with
          | .isFalse different =>
            exact .isFalse (fun same => by cases same; exact different rfl)
          | .isTrue freshEqual =>
            cases freshEqual
            match CommonReadings.compare firstCommon secondCommon with
            | .isFalse different =>
              exact .isFalse (fun same => by cases same; exact different rfl)
            | .isTrue commonEqual =>
              cases commonEqual
              exact .isTrue rfl
        else
          exact .isFalse (fun same => by cases same; exact cachedEqual rfl)
      else
        exact .isFalse (fun same => requestEqual (congrArg Producer.Continuation.request same))

/-- Two continuation displays are the same exactly when their original owners are equal. -/
@[expose] public def Same {previous : SourceFrontier value} (first second : Display previous) : Prop :=
  read first = read second

/-- Presentation equality is exactly equality of the original continuations. -/
public theorem same_iff_read_eq {previous : SourceFrontier value} (first second : Display previous) :
    Same first second ↔ read first = read second := Iff.rfl

/-- Decide original continuation equality on accepted displays. -/
@[expose] public def compare {previous : SourceFrontier value}
    (first second : Display previous) : Decidable (Same first second) := compareOwner (read first) (read second)

/-- The finite presentation of continuations at their exact saved frontier. -/
@[expose] public def continuation (previous : SourceFrontier value) : Purelib.Data.Presentation (Code previous) where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

end Continuation

namespace Continuation

/-- Decide literal continuation-code equality while retaining all original data and indices. -/
@[expose] public def compareCode {previous : SourceFrontier value}
    (first second : Code previous) : Decidable (first = second) := by
  letI (a b : SourcePoint value) : Decidable (a = b) := comparePoint a b
  cases first with
  | reused firstRequest =>
    cases second with
    | reused secondRequest =>
      if equal : firstRequest = secondRequest then
        cases equal
        exact .isTrue rfl
      else exact .isFalse (fun same => by cases same; exact equal rfl)
    | refined => exact .isFalse (fun same => by cases same)
  | refined firstRequest firstCached firstFresh firstCommon firstSplit =>
    cases second with
    | reused => exact .isFalse (fun same => by cases same)
    | refined secondRequest secondCached secondFresh secondCommon secondSplit =>
      if requestEqual : firstRequest = secondRequest then
        cases requestEqual
        if cachedEqual : firstCached = secondCached then
          cases cachedEqual
          match compareResult firstFresh secondFresh with
          | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
          | .isTrue freshEqual =>
            cases freshEqual
            match CommonReadings.compare firstCommon secondCommon with
            | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
            | .isTrue commonEqual =>
              cases commonEqual
              exact .isTrue rfl
        else exact .isFalse (fun same => by cases same; exact cachedEqual rfl)
      else exact .isFalse (fun same => by cases same; exact requestEqual rfl)

end Continuation

namespace Continuation.Proposal

open Purelib.Approximation
open Purelib.Integration.SourceFrontier

set_option genInjectivity false in
/-- A continuation proposal whose refined branch contains unchecked result and ordered reading data.

The original split certificate is derived from the validated ordered common
collection, retaining its original partition and indexed parent cells. -/
public inductive Code (previous : SourceFrontier value) where
  /-- Reuse the saved frontier for the proposed request. -/ | reused (request : AccuracyRequest)
  /-- Retain the original bank, fresh result and collection input. -/
  | refined (request : AccuracyRequest) (cached : Bank.Code)
      (fresh : Result.Input.Code) (common : CommonReadings.Code)

/-- Rebind the finite proposal data to the frontier against which it will be checked. -/
@[expose] public def rebind {previous next : SourceFrontier value} : Code previous → Code next
  | .reused request => .reused request
  | .refined request cached fresh common => .refined request cached fresh common

/-- Rebinding twice preserves every finite proposal field. -/
public theorem rebind_rebind {first second third : SourceFrontier value} (code : Code first) :
    rebind (next := third) (rebind (next := second) code) = rebind code := by
  cases code <;> rfl

/-- Rebinding to the same frontier preserves the finite proposal. -/
public theorem rebind_self {previous : SourceFrontier value} (code : Code previous) :
    rebind (next := previous) code = code := by
  cases code <;> rfl

/-- A proposal pays the saved request or binds its fresh result and collection to their original owners. -/
@[expose] public def Valid {previous : SourceFrontier value} : Code previous → Prop
  | .reused request => (integralBound previous.cells).width < request.tolerance
  | .refined request cached fresh common =>
      Bank.Valid cached ∧ Result.Input.Valid fresh ∧ ∀ freshValid : Result.Input.Valid fresh,
        (Result.Input.read ⟨fresh, freshValid⟩).preparation.request = request ∧
          CommonReadings.Valid previous (Result.Input.read ⟨fresh, freshValid⟩).frontier common

/-- A checked continuation proposal at its exact saved frontier. -/
public abbrev Display (previous : SourceFrontier value) := {code : Code previous // Valid code}

/-- Reconstruct the original continuation using the checked common collection and its derived split. -/
@[expose] public def read {previous : SourceFrontier value} (display : Display previous) :
    Producer.Continuation producer previous :=
  match display with
  | ⟨.reused request, accurate⟩ => .reused request accurate
  | ⟨.refined request cached fresh common, valid⟩ =>
      let bank := Bank.read cached valid.1
      let freshOwner := Result.Input.read ⟨fresh, valid.2.1⟩
      .refined request bank freshOwner
        ((Continuation.fresh_eq_iff previous request bank freshOwner).mpr (valid.2.2 valid.2.1).1)
        (CommonReadings.read ⟨common, (valid.2.2 valid.2.1).2⟩)
        (CommonReadings.read ⟨common, (valid.2.2 valid.2.1).2⟩).intersection_split

set_option genInjectivity false in
/-- The first proved failure of a continuation proposal, including the nested collection failure. -/
public inductive Check {previous : SourceFrontier value} : (code : Code previous) → Type where
  /-- All finite bindings hold; the reconstructed original continuation is retained. -/
  | accepted {code} (valid : Valid code) (value : Producer.Continuation producer previous)
      (readback : value = read ⟨code, valid⟩) : Check code
  /-- The saved frontier does not meet the requested tolerance. -/
  | invalidReuse (request : AccuracyRequest) (failure : ¬ Valid (Code.reused (previous := previous) request)) :
      Check (.reused request)
  /-- The ordered cache bank contains a located invalid source point. -/
  | invalidBank (request : AccuracyRequest) (cached : Bank.Code)
      (fresh : Result.Input.Code) (common : CommonReadings.Code) (failure : Bank.Failure cached) :
      Check (.refined request cached fresh common)
  /-- The supplied fresh result disagrees with its preparation. -/
  | invalidResult (request : AccuracyRequest) (cached : Bank.Code)
      (fresh : Result.Input.Code) (common : CommonReadings.Code)
      (reason : Result.Input.Check fresh) (failure : ¬ Result.Input.Valid fresh) :
      Check (.refined request cached fresh common)
  /-- The fresh result belongs to another request. -/
  | wrongFresh (request : AccuracyRequest) (cached : Bank.Code)
      (fresh : Result.Input.Code) (common : CommonReadings.Code) (freshValid : Result.Input.Valid fresh)
      (different : (Result.Input.read ⟨fresh, freshValid⟩).preparation.request ≠ request) :
      Check (.refined request cached fresh common)
  /-- The original ordered common readings fail at a located entry. -/
  | invalidCommon (request : AccuracyRequest) (cached : Bank.Code)
      (fresh : Result.Input.Code) (common : CommonReadings.Code) (freshValid : Result.Input.Valid fresh)
      (failure : CommonReadings.Failure previous (Result.Input.read ⟨fresh, freshValid⟩).frontier
        common.2 common.1.intervals) :
      Check (.refined request cached fresh common)

/-- Check the request and the ordered collection against the saved and fresh frontiers. -/
@[expose] public def check {previous : SourceFrontier value} : (code : Code previous) → Check code
  | .reused request =>
      if accurate : (integralBound previous.cells).width < request.tolerance then
        .accepted accurate (.reused request accurate) rfl
      else .invalidReuse request accurate
  | .refined request cached fresh common =>
    match Bank.check cached with
    | .rejected failure => .invalidBank request cached fresh common failure
    | .accepted bankValid =>
      let result := Result.Input.check fresh
      match result.decision with
      | .isFalse failure => .invalidResult request cached fresh common result failure
      | .isTrue freshValid =>
        let freshOwner := Result.Input.read ⟨fresh, freshValid⟩
        if equal : freshOwner.preparation.request = request then
          match CommonReadings.checkCode previous freshOwner.frontier common with
          | .accepted valid =>
              .accepted ⟨bankValid, freshValid, fun _ => ⟨equal, valid⟩⟩
                (.refined request (Bank.read cached bankValid) freshOwner
                  ((Continuation.fresh_eq_iff previous request (Bank.read cached bankValid) freshOwner).mpr equal)
                  (CommonReadings.read ⟨common, valid⟩) (CommonReadings.read ⟨common, valid⟩).intersection_split) rfl
          | .rejected failure => .invalidCommon request cached fresh common freshValid failure
        else .wrongFresh request cached fresh common freshValid equal

/-- Derive the validity decision from the detailed continuation check. -/
@[expose] public def Check.decision {previous : SourceFrontier value} {code : Code previous}
    (result : Check code) : Decidable (Valid code) :=
  match result with
  | .accepted valid _ _ => .isTrue valid
  | .invalidReuse _ failure => .isFalse failure
  | .invalidBank _ _ _ _ failure => .isFalse (fun valid => failure.notValid valid.1)
  | .invalidResult _ _ _ _ _ failure => .isFalse (fun valid => failure valid.2.1)
  | .wrongFresh _ _ _ _ freshValid different => .isFalse (fun valid => different (valid.2.2 freshValid).1)
  | .invalidCommon _ _ _ _ freshValid failure =>
      .isFalse (fun valid => failure.notAligned (valid.2.2 freshValid).2)

/-- Compare two rejected proposal checks at the same original owner and code.

The supplied invalidity excludes the successful branch. Nested failures keep
their original reasons and occurrences; no proposal check is repeated. -/
public def Check.compareInvalid {previous : SourceFrontier value} {code : Code previous}
    (invalid : ¬ Valid code) (first second : Check code) : Decidable (first = second) := by
  cases first with
  | accepted valid _ _ => exact False.elim (invalid valid)
  | invalidReuse request failure =>
    cases second with
    | accepted valid _ _ => exact False.elim (invalid valid)
    | invalidReuse => exact .isTrue rfl
  | invalidBank request cached fresh common failure =>
    cases second with
    | accepted valid _ _ => exact False.elim (invalid valid)
    | invalidBank _ _ _ _ other =>
      match Bank.Failure.compare failure other with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    | _ => exact .isFalse (by intro same; cases same)
  | invalidResult request cached fresh common reason failure =>
    cases second with
    | accepted valid _ _ => exact False.elim (invalid valid)
    | invalidResult _ _ _ _ other _ =>
      match Result.Input.Check.compare reason other with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    | _ => exact .isFalse (by intro same; cases same)
  | wrongFresh request cached fresh common freshValid different =>
    cases second with
    | accepted valid _ _ => exact False.elim (invalid valid)
    | wrongFresh => exact .isTrue rfl
    | _ => exact .isFalse (by intro same; cases same)
  | invalidCommon request cached fresh common freshValid failure =>
    cases second with
    | accepted valid _ _ => exact False.elim (invalid valid)
    | invalidCommon _ _ _ _ otherValid other =>
      have validEqual : freshValid = otherValid := Subsingleton.elim _ _
      cases validEqual
      match CommonReadings.Failure.compare failure other with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    | _ => exact .isFalse (by intro same; cases same)

/-- Retrieve the continuation retained by a successful check without reconstructing its caches. -/
@[expose] public def Check.read {previous : SourceFrontier value} {code : Code previous}
    (result : Check code) (valid : Valid code) : Producer.Continuation producer previous :=
  match result with
  | .accepted _ value _ => value
  | .invalidReuse _ failure => False.elim (failure valid)
  | .invalidBank _ _ _ _ failure => False.elim (failure.notValid valid.1)
  | .invalidResult _ _ _ _ _ failure => False.elim (failure valid.2.1)
  | .wrongFresh _ _ _ _ freshValid different => False.elim (different (valid.2.2 freshValid).1)
  | .invalidCommon _ _ _ _ freshValid failure =>
      False.elim (failure.notAligned (valid.2.2 freshValid).2)

/-- The cached continuation is the original readback of the checked proposal. -/
public theorem Check.read_eq {previous : SourceFrontier value} {code : Code previous}
    (result : Check code) (valid : Valid code) :
    result.read valid = Continuation.Proposal.read ⟨code, valid⟩ := by
  cases result with
  | accepted _ _ equal => exact equal
  | invalidReuse _ failure => exact False.elim (failure valid)
  | invalidBank _ _ _ _ failure => exact False.elim (failure.notValid valid.1)
  | invalidResult _ _ _ _ _ failure => exact False.elim (failure valid.2.1)
  | wrongFresh _ _ _ _ freshValid different => exact False.elim (different (valid.2.2 freshValid).1)
  | invalidCommon _ _ _ _ freshValid failure =>
      exact False.elim (failure.notAligned (valid.2.2 freshValid).2)

/-- Decide validity using the same typed continuation and collection checks. -/
@[expose] public def recognize {previous : SourceFrontier value} (code : Code previous) : Decidable (Valid code) :=
  (check code).decision

/-- Quote an original continuation into its retained finite fields. -/
@[expose] public def quote {previous : SourceFrontier value}
    (continuation : Producer.Continuation producer previous) : Display previous :=
  match continuation with
  | .reused request accurate => ⟨.reused request, accurate⟩
  | .refined request cached fresh freshEq common _ =>
      ⟨.refined request (Bank.quote cached) (Result.Input.quote fresh).val (CommonReadings.quote common).val,
        Bank.quote_valid cached, (Result.Input.quote fresh).property, fun freshValid => by
          have equal : Result.Input.read ⟨(Result.Input.quote fresh).val, freshValid⟩ = fresh :=
            Result.Input.read_quote fresh
          rw [equal]
          exact ⟨(Continuation.fresh_eq_iff previous request cached fresh).mp freshEq,
            (CommonReadings.quote common).property⟩⟩

/-- Reading a quotation recovers the original continuation. -/
public theorem read_quote {previous : SourceFrontier value} (continuation : Producer.Continuation producer previous) :
    read (quote continuation) = continuation := by
  cases continuation with
  | reused => rfl
  | refined request cached fresh freshEq common split =>
      have congruent : ∀ (firstBank secondBank : List (SourcePoint value)) (bankEq : firstBank = secondBank)
          (first second : Continuous.Result modulus) (equal : first = second)
          (firstEq : first = producer.requestCached (Producer.effectiveBank previous firstBank) request)
          (secondEq : second = producer.requestCached (Producer.effectiveBank previous secondBank) request)
          (original : SourceFrontier.CommonReadings previous second.frontier)
          (valid : CommonReadings.Valid previous first.frontier (CommonReadings.quote original).val)
          (firstSplit : IntegrationFrontierRefines
            (CommonReadings.read ⟨(CommonReadings.quote original).val, valid⟩).intersection.cells previous.cells)
          (secondSplit : IntegrationFrontierRefines original.intersection.cells previous.cells),
          Producer.Continuation.refined (producer := producer) (previous := previous) request firstBank first firstEq
              (CommonReadings.read ⟨(CommonReadings.quote original).val, valid⟩) firstSplit =
            Producer.Continuation.refined (producer := producer) (previous := previous)
              request secondBank second secondEq original secondSplit := by
        intro firstBank secondBank bankEq first second equal firstEq secondEq original valid firstSplit secondSplit
        cases bankEq
        cases equal
        have same : CommonReadings.read ⟨(CommonReadings.quote original).val, valid⟩ = original :=
          CommonReadings.read_quote original
        have byCommon : ∀ (a b : SourceFrontier.CommonReadings previous first.frontier), a = b →
            ∀ (aSplit : IntegrationFrontierRefines a.intersection.cells previous.cells)
              (bSplit : IntegrationFrontierRefines b.intersection.cells previous.cells),
              Producer.Continuation.refined (producer := producer) (previous := previous)
                request firstBank first firstEq a aSplit =
              Producer.Continuation.refined (producer := producer) (previous := previous)
                request firstBank first secondEq b bSplit := by
          intro a b same aSplit bSplit
          cases same
          rfl
        exact byCommon _ _ same _ _
      change Producer.Continuation.refined request (Bank.read (Bank.quote cached) _) _ _ _ _ = _
      exact congruent _ cached (Bank.read_quote cached _) _ fresh (Result.Input.read_quote fresh) _ _ common _ _ split

/-- Quoting a checked proposal recovers its proposed fields. -/
public theorem quote_read {previous : SourceFrontier value} (display : Display previous) :
    quote (read display) = display := by
  cases display with
  | mk code valid =>
    cases code with
    | reused => rfl
    | refined request cached fresh common =>
      have congruent : ∀ (firstFresh secondFresh : Result.Input.Code), firstFresh = secondFresh →
          ∀ (firstCommon secondCommon : CommonReadings.Code), firstCommon = secondCommon →
            Code.refined (previous := previous) request cached firstFresh firstCommon =
              Code.refined (previous := previous) request cached secondFresh secondCommon := by
        intro firstFresh secondFresh freshEqual firstCommon secondCommon commonEqual
        cases freshEqual
        cases commonEqual
        rfl
      apply Subtype.ext
      change Code.refined request (Bank.quote (Bank.read cached valid.1))
        (Result.Input.quote (Result.Input.read ⟨fresh, valid.2.1⟩)).val
        (CommonReadings.quote (CommonReadings.read ⟨common, (valid.2.2 valid.2.1).2⟩)).val =
        Code.refined request cached fresh common
      rw [Bank.quote_read]
      exact congruent _ _ (congrArg Subtype.val (Result.Input.quote_read ⟨fresh, valid.2.1⟩)) _ _
        (congrArg Subtype.val (CommonReadings.quote_read ⟨common, (valid.2.2 valid.2.1).2⟩))

/-- Accepted proposals have the same identity exactly when their original continuations agree. -/
@[expose] public def Same {previous : SourceFrontier value} (first second : Display previous) : Prop :=
  read first = read second

/-- Decide original continuation identity for two checked proposals. -/
@[expose] public def compare {previous : SourceFrontier value} (first second : Display previous) :
    Decidable (Same first second) := Continuation.compareOwner (read first) (read second)

/-- Proposal identity is equality of the reconstructed original continuation. -/
public theorem same_iff_read_eq {previous : SourceFrontier value} (first second : Display previous) :
    Same first second ↔ read first = read second := Iff.rfl

/-- Decide literal proposal identity, including branch, bank and ordered common-reading inputs. -/
@[expose] public def compareCode {previous : SourceFrontier value}
    (first second : Code previous) : Decidable (first = second) := by
  cases first with
  | reused firstRequest =>
    cases second with
    | reused secondRequest =>
      if equal : firstRequest = secondRequest then
        cases equal
        exact .isTrue rfl
      else exact .isFalse (fun same => by cases same; exact equal rfl)
    | refined => exact .isFalse (fun same => by cases same)
  | refined firstRequest firstCached firstFresh firstCommon =>
    cases second with
    | reused => exact .isFalse (fun same => by cases same)
    | refined secondRequest secondCached secondFresh secondCommon =>
      if requestEqual : firstRequest = secondRequest then
        cases requestEqual
        if cachedEqual : firstCached = secondCached then
          cases cachedEqual
          match Result.Input.compareCode firstFresh secondFresh with
          | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
          | .isTrue freshEqual =>
            cases freshEqual
            if cuts : firstCommon.1.cuts = secondCommon.1.cuts then
              have partitions : firstCommon.1 = secondCommon.1 := Unit.Normalized.ext_cuts cuts
              cases firstCommon with
              | mk firstPartition firstInputs =>
                cases secondCommon with
                | mk secondPartition secondInputs =>
                  cases partitions
                  if inputs : firstInputs = secondInputs then
                    cases inputs
                    exact .isTrue rfl
                  else exact .isFalse (fun same => by cases same; exact inputs rfl)
            else exact .isFalse (fun same => by cases same; exact cuts rfl)
        else exact .isFalse (fun same => by cases same; exact cachedEqual rfl)
      else exact .isFalse (fun same => by cases same; exact requestEqual rfl)

/-- Present finite continuation proposals at their original saved frontier. -/
@[expose] public def presentation (previous : SourceFrontier value) : Purelib.Data.Presentation (Code previous) where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

end Continuation.Proposal

namespace History

open Purelib.Integration.SourceFrontier

/-- The original pi controller's state, including its indexed finite history. -/
public abbrev State := RefiningController.History.State producer.controller producer.controller.origin

/-- A proposed step retains the frontier at which its continuation was formed. -/
public abbrev StepCode := Σ saved : SourceFrontier value, Continuation.Proposal.Code saved

/-- A history proposal is an ordered finite list of original indexed steps. -/
public abbrev Code := List StepCode

/-- Decide equality of original source frontiers through their retained finite presentations. -/
@[expose] public def compareFrontier (first second : SourceFrontier value) : Decidable (first = second) :=
  match Frontier.compare (Frontier.quote first) (Frontier.quote second) with
  | .isTrue same => .isTrue ((Frontier.read_quote first (Frontier.quote_sourceRange first)).symm.trans
      (((Frontier.same_iff_read_eq _ _ (Frontier.quote_sourceRange first)
        (Frontier.quote_sourceRange second)).mp same).trans
          (Frontier.read_quote second (Frontier.quote_sourceRange second))))
  | .isFalse different => .isFalse (fun equal => different (by cases equal; exact ⟨rfl, rfl⟩))

set_option genInjectivity false in
/-- A history scan identifies the failing occurrence and its proved binding failure. -/
public inductive Failure where
  /-- The proposed step belongs to a different saved frontier. -/
  | wrongPrevious (position : Nat) (actual saved : SourceFrontier value) (different : actual ≠ saved)
  /-- The step's own typed presentation fails at this occurrence. -/
  | invalidStep (position : Nat) (saved : SourceFrontier value) (step : Continuation.Proposal.Code saved)
      (result : Continuation.Proposal.Check step) (invalid : ¬ Continuation.Proposal.Valid step)

/-- The original initial state, retaining the controller's actual initial result. -/
@[expose] public def initial : State := ⟨producer.frontier producer.controller.origin, .initial⟩

set_option genInjectivity false in
/-- Checking a saved frontier and a continuation retains their original binding. -/
public inductive SavedCheck (saved : Frontier.Code) (step : Continuation.Proposal.Code initial.1) where
  /-- The saved cells fail the ordered alignment check. -/
  | invalidCells (failure : Frontier.Failure saved.2 saved.1.intervals)
  /-- An aligned saved cell has an invalid source bound. -/
  | invalidRange (aligned : Frontier.Valid saved)
      (failure : Frontier.RangeFailure (Frontier.readCells saved.2 saved.1.intervals aligned))
  /-- The proposal is checked against the reconstructed original frontier. -/
  | checked (aligned : Frontier.Valid saved) (range : Frontier.SourceRange ⟨saved, aligned⟩)
      (owner : SourceFrontier value) (readback : owner = Frontier.read ⟨saved, aligned⟩ range)
      (result : Continuation.Proposal.Check (Continuation.Proposal.rebind (next := owner) step))

/-- Check saved finite data before checking the continuation against its reconstructed owner. -/
@[expose] public def checkSaved (saved : Frontier.Code) (step : Continuation.Proposal.Code initial.1) :
    SavedCheck saved step :=
  match Frontier.checkComplete saved with
  | .invalidCells failure => .invalidCells failure
  | .invalidRange aligned failure => .invalidRange aligned failure
  | .accepted aligned range owner readback =>
      .checked aligned range owner readback (Continuation.Proposal.check (Continuation.Proposal.rebind step))

set_option genInjectivity false in
/-- The result of checking cuts before a saved frontier and continuation. -/
public inductive SavedCutsCheck (cuts : Unit.Presentation.Code) (cells : List Cell.Code)
    (step : Continuation.Proposal.Code initial.1) where
  /-- The original cut checker identifies a proved invalid input. -/
  | invalidCuts (reason : Unit.Presentation.Check cuts) (invalid : ¬ Unit.Presentation.Valid cuts)
  /-- One constructed partition and the existing saved-step check are retained. -/
  | checked (valid : Unit.Presentation.Valid cuts)
      (saved : Frontier.Code) (savedEq : saved = Frontier.fromCuts ⟨cuts, valid⟩ cells)
      (result : SavedCheck saved step)

/-- Check cuts once, then check the saved step against that original partition cache. -/
@[expose] public def checkSavedCuts (cuts : Unit.Presentation.Code) (cells : List Cell.Code)
    (step : Continuation.Proposal.Code initial.1) : SavedCutsCheck cuts cells step :=
  let reason := Unit.Presentation.check cuts
  match reason with
  | .outOfRange index failed =>
      .invalidCuts reason (fun valid => failed (valid.2 (cuts.get index) (List.getElem_mem index.isLt)))
  | .badAdjacent _ _ _ _ _ _ notSorted => .invalidCuts reason (fun valid => notSorted valid.1)
  | .accepted valid =>
      let saved := Frontier.fromCuts ⟨cuts, valid⟩ cells
      .checked valid saved rfl (checkSaved saved step)

/-- Checking an original frontier's cuts retains its original partition and cells. -/
public theorem checkSavedCuts_quote (frontier : SourceFrontier value)
    (step : Continuation.Proposal.Code initial.1) :
    ∃ (valid : Unit.Presentation.Valid frontier.partition.cuts)
      (result : SavedCheck (Frontier.fromCuts ⟨frontier.partition.cuts, valid⟩
        (Frontier.quote frontier).val.2) step),
      checkSavedCuts frontier.partition.cuts (Frontier.quote frontier).val.2 step =
          .checked valid (Frontier.fromCuts ⟨frontier.partition.cuts, valid⟩
            (Frontier.quote frontier).val.2) rfl result ∧
        Frontier.fromCuts ⟨frontier.partition.cuts, valid⟩ (Frontier.quote frontier).val.2 =
          (Frontier.quote frontier).val := by
  cases checked : Unit.Presentation.check frontier.partition.cuts with
  | accepted valid =>
      refine ⟨valid, checkSaved (Frontier.fromCuts ⟨frontier.partition.cuts, valid⟩
        (Frontier.quote frontier).val.2) step, ?_, ?_⟩
      · unfold checkSavedCuts
        rw [checked]
      · apply Prod.ext
        · exact Unit.Presentation.read_quote frontier.partition
        · rfl
  | outOfRange index failed =>
      have valid := (Unit.Presentation.quote frontier.partition).property
      exact False.elim (failed (valid.2 _ (List.getElem_mem index.isLt)))
  | badAdjacent _ _ _ _ _ _ failed =>
      exact False.elim (failed (Unit.Presentation.quote frontier.partition).property.1)

/-- Extract a history step only after its saved frontier and continuation have both passed. -/
@[expose] public def SavedCheck.step {saved : Frontier.Code}
    {proposal : Continuation.Proposal.Code initial.1} : SavedCheck saved proposal → Option StepCode
  | .checked _ _ owner _ (.accepted ..) => some ⟨owner, Continuation.Proposal.rebind proposal⟩
  | _ => none

/-- Extract the original checked step after both the cuts and saved continuation succeed. -/
@[expose] public def SavedCutsCheck.step {cuts : Unit.Presentation.Code} {cells : List Cell.Code}
    {proposal : Continuation.Proposal.Code initial.1} : SavedCutsCheck cuts cells proposal → Option StepCode
  | .invalidCuts .. => none
  | .checked _ _ _ result => result.step

/-- Append the actual continuation to its exact indexed predecessor history. -/
@[expose] public def append (previous : State) (step : Producer.Continuation producer previous.1) : State :=
  ⟨step.frontier, .next previous.2 step⟩

/-- The bound process starts with the original producer result and indexed initial history. -/
public theorem boundProcess_initial : boundProcess.initial = initial := rfl

/-- A bound is the integral enclosure of the exact frontier retained by the state. -/
public theorem boundProcess_bound (state : State) :
    boundProcess.bound state = integralBound state.1.cells := rfl

/-- A request appends the actual continuation, with its bank read from the original history.

The bank is supplied as a callback: `advanceWithBank` reads it only when the
saved frontier does not already meet the request. -/
public theorem boundProcess_request (state : State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    boundProcess.request state epsilon positive = append state
      (producer.advanceWithBank (fun _ => producer.retainedReadings state.2) state.1 ⟨epsilon, positive⟩) := rfl

/-- A sufficiently narrow saved frontier appends the reused continuation without reading its bank. -/
public theorem boundProcess_request_reused (state : State) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) (accurate : (integralBound state.1.cells).width < epsilon) :
    boundProcess.request state epsilon positive = append state (.reused ⟨epsilon, positive⟩ accurate) := by
  exact (boundProcess_request state epsilon positive).trans
    (congrArg (append state)
      (producer.advanceWithBank_reused (fun _ => producer.retainedReadings state.2)
        state.1 ⟨epsilon, positive⟩ accurate))

/-- A finite history entry contains saved frontier data and an unbound continuation proposal. -/
public abbrev RawStep := Frontier.Code × Continuation.Proposal.Code initial.1

/-- A finite history input retains its entries in their proposed order. -/
public abbrev RawCode := List RawStep

set_option genInjectivity false in
/-- The first invalid finite history entry, including its original position and evidence. -/
public inductive RawFailure where
  /-- A saved frontier has an invalid ordered cell or cache. -/
  | invalidCells (position : Nat) (saved : Frontier.Code)
      (failure : Frontier.Failure saved.2 saved.1.intervals)
  /-- A saved frontier has an invalid fixed-source endpoint bound. -/
  | invalidRange (position : Nat) (saved : Frontier.Code) (aligned : Frontier.Valid saved)
      (failure : Frontier.RangeFailure (Frontier.readCells saved.2 saved.1.intervals aligned))
  /-- The saved frontier differs from the actual predecessor reached by the scan. -/
  | wrongPrevious (position : Nat) (actual saved : SourceFrontier value) (different : actual ≠ saved)
  /-- The continuation fails against its reconstructed saved frontier. -/
  | invalidStep (position : Nat) (saved : SourceFrontier value) (step : Continuation.Proposal.Code saved)
      (result : Continuation.Proposal.Check step) (invalid : ¬ Continuation.Proposal.Valid step)

/-- Compare two invalid-cell history outcomes using their retained data.

The partition comparison projects its original cuts; it does not rebuild the
interval cache. Cell lists, positions and the indexed failure reason all remain
part of the outcome identity. -/
public def RawFailure.compareInvalidCells (firstPosition secondPosition : Nat)
    (firstSaved secondSaved : Frontier.Code)
    (firstFailure : Frontier.Failure firstSaved.2 firstSaved.1.intervals)
    (secondFailure : Frontier.Failure secondSaved.2 secondSaved.1.intervals) :
    Decidable (RawFailure.invalidCells firstPosition firstSaved firstFailure =
      RawFailure.invalidCells secondPosition secondSaved secondFailure) := by
  letI : DecidableEq Unit.Normalized := fun first second =>
    if cuts : first.cuts = second.cuts then
      .isTrue (Unit.Normalized.ext_cuts cuts)
    else
      .isFalse (fun same => cuts (congrArg Unit.Normalized.cuts same))
  if positions : firstPosition = secondPosition then
    cases positions
    if saved : firstSaved = secondSaved then
      cases saved
      match Frontier.Failure.compare firstFailure secondFailure with
      | .isTrue failures => cases failures; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    else exact .isFalse (fun same => by cases same; exact saved rfl)
  else exact .isFalse (fun same => by cases same; exact positions rfl)

/-- Compare invalid-range history outcomes using their original retained data.

Positions, saved partitions and cells, endpoint reasons and occurrences determine
identity; alignment proofs do not. No source check or partition cache is repeated. -/
public def RawFailure.compareInvalidRange (firstPosition secondPosition : Nat)
    (firstSaved secondSaved : Frontier.Code)
    (firstAligned : Frontier.Valid firstSaved) (secondAligned : Frontier.Valid secondSaved)
    (firstFailure : Frontier.RangeFailure (Frontier.readCells firstSaved.2 firstSaved.1.intervals firstAligned))
    (secondFailure : Frontier.RangeFailure (Frontier.readCells secondSaved.2 secondSaved.1.intervals secondAligned)) :
    Decidable (RawFailure.invalidRange firstPosition firstSaved firstAligned firstFailure =
      RawFailure.invalidRange secondPosition secondSaved secondAligned secondFailure) := by
  letI : DecidableEq Unit.Normalized := fun first second =>
    if cuts : first.cuts = second.cuts then
      .isTrue (Unit.Normalized.ext_cuts cuts)
    else
      .isFalse (fun same => cuts (congrArg Unit.Normalized.cuts same))
  if positions : firstPosition = secondPosition then
    cases positions
    if saved : firstSaved = secondSaved then
      cases saved
      have aligned : firstAligned = secondAligned := Subsingleton.elim _ _
      cases aligned
      match Frontier.RangeFailure.compare firstFailure secondFailure with
      | .isTrue failures => cases failures; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    else exact .isFalse (fun same => by cases same; exact saved rfl)
  else exact .isFalse (fun same => by cases same; exact positions rfl)

/-- Decide equality of retained history failures without repeating their scans.

The original positions, saved owners, proposed codes and detailed nested
failures determine equality. Proof witnesses do not distinguish outcomes. -/
public def RawFailure.compare (first second : RawFailure) : Decidable (first = second) := by
  cases first with
  | invalidCells position saved failure =>
    cases second with
    | invalidCells otherPosition otherSaved otherFailure =>
      exact compareInvalidCells position otherPosition saved otherSaved failure otherFailure
    | _ => exact .isFalse (by intro same; cases same)
  | invalidRange position saved aligned failure =>
    cases second with
    | invalidRange otherPosition otherSaved otherAligned otherFailure =>
      exact compareInvalidRange position otherPosition saved otherSaved aligned otherAligned failure otherFailure
    | _ => exact .isFalse (by intro same; cases same)
  | wrongPrevious position actual saved different =>
    cases second with
    | wrongPrevious otherPosition otherActual otherSaved _ =>
      if positions : position = otherPosition then
        cases positions
        match compareFrontier actual otherActual with
        | .isFalse unequal => exact .isFalse (fun same => by cases same; exact unequal rfl)
        | .isTrue equal =>
          cases equal
          match compareFrontier saved otherSaved with
          | .isFalse unequal => exact .isFalse (fun same => by cases same; exact unequal rfl)
          | .isTrue equal => cases equal; exact .isTrue rfl
      else exact .isFalse (fun same => by cases same; exact positions rfl)
    | _ => exact .isFalse (by intro same; cases same)
  | invalidStep position saved step result invalid =>
    cases second with
    | invalidStep otherPosition otherSaved otherStep otherResult _ =>
      if positions : position = otherPosition then
        cases positions
        match compareFrontier saved otherSaved with
        | .isFalse unequal => exact .isFalse (fun same => by cases same; exact unequal rfl)
        | .isTrue equal =>
          cases equal
          match Continuation.Proposal.compareCode step otherStep with
          | .isFalse unequal => exact .isFalse (fun same => by cases same; exact unequal rfl)
          | .isTrue equal =>
            cases equal
            match Continuation.Proposal.Check.compareInvalid invalid result otherResult with
            | .isFalse unequal => exact .isFalse (fun same => by cases same; exact unequal rfl)
            | .isTrue equal => cases equal; exact .isTrue rfl
      else exact .isFalse (fun same => by cases same; exact positions rfl)
    | _ => exact .isFalse (by intro same; cases same)

/-- Continue a history scan from a previously checked saved frontier and proposal.

The supplied result is consumed directly, so its reconstructed frontier and
certificates are not recomputed when a different input checker is used. -/
@[expose] public def withSaved {Error : Type} (state : State) (position : Nat)
    (saved : Frontier.Code) (proposal : Continuation.Proposal.Code initial.1)
    (checked : SavedCheck saved proposal) (failure : RawFailure → Error)
    (next : State → Except Error State) : Except Error State :=
  match checked with
  | .invalidCells problem => .error (failure (.invalidCells position saved problem))
  | .invalidRange aligned problem => .error (failure (.invalidRange position saved aligned problem))
  | .checked _ _ owner _ result =>
    match compareFrontier state.1 owner with
    | .isFalse different => .error (failure (.wrongPrevious position state.1 owner different))
    | .isTrue binding =>
      match result.decision with
      | .isFalse invalid => .error (failure (.invalidStep position owner _ result invalid))
      | .isTrue valid =>
        let continuation : Producer.Continuation producer state.1 := binding.symm ▸ result.read valid
        next (append state continuation)

/-- Scan finite entries using their accepted continuations and the original indexed states. -/
@[expose] public def scanRawFrom (state : State) (position : Nat) : RawCode → Except RawFailure State
  | [] => .ok state
  | (saved, proposal) :: rest =>
    withSaved state position saved proposal (checkSaved saved proposal) id
      (fun next => scanRawFrom next (position + 1) rest)

/-- A history entry with unchecked cuts, cells and a typed continuation proposal. -/
public abbrev CutsStep := Unit.Presentation.Code × List Cell.Code × Continuation.Proposal.Code initial.1

/-- A finite sequence of history entries whose cuts have not yet been checked. -/
public abbrev CutsCode := List CutsStep

/-- Decide literal equality of unchecked history entries at the original source.

The decision compares the supplied ordered cuts, saved cells and continuation
proposal. It does not check their validity or reconstruct a frontier. -/
@[expose] public def compareCutsStep (first second : CutsStep) : Decidable (first = second) := by
  rcases first with ⟨firstCuts, firstCells, firstProposal⟩
  rcases second with ⟨secondCuts, secondCells, secondProposal⟩
  if cuts : firstCuts = secondCuts then
    cases cuts
    if cells : firstCells = secondCells then
      cases cells
      match Continuation.Proposal.compareCode firstProposal secondProposal with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun equal => by cases equal; exact different rfl)
    else exact .isFalse (fun equal => by cases equal; exact cells rfl)
  else exact .isFalse (fun equal => by cases equal; exact cuts rfl)

/-- Decide literal equality of finite unchecked history inputs in their original order. -/
@[expose] public def compareCutsCode (first second : CutsCode) : Decidable (first = second) := by
  letI (a b : CutsStep) : Decidable (a = b) := compareCutsStep a b
  exact inferInstanceAs (Decidable (first = second))

set_option genInjectivity false in
/-- The first failure of a history scan with unchecked cuts. -/
public inductive CutsFailure where
  /-- The cut checker rejects the original cut list at the indicated history position. -/
  | invalidCuts (position : Nat) (cuts : Unit.Presentation.Code)
      (reason : Unit.Presentation.Check cuts) (invalid : ¬ Unit.Presentation.Valid cuts)
  /-- A checked partition has an invalid saved frontier, owner or continuation. -/
  | invalidSaved (failure : RawFailure)

/-- Decide equality of two retained invalid-cut history failures.

The comparison uses the original history positions, cut lists and detailed
cut-check results. It neither repeats recognition nor rebuilds a partition;
proofs of invalidity do not distinguish outcomes. -/
public def CutsFailure.compareInvalidCuts (firstPosition secondPosition : Nat)
    {firstCuts secondCuts : Unit.Presentation.Code}
    (firstReason : Unit.Presentation.Check firstCuts) (firstInvalid : ¬ Unit.Presentation.Valid firstCuts)
    (secondReason : Unit.Presentation.Check secondCuts) (secondInvalid : ¬ Unit.Presentation.Valid secondCuts) :
    Decidable (CutsFailure.invalidCuts firstPosition firstCuts firstReason firstInvalid =
      CutsFailure.invalidCuts secondPosition secondCuts secondReason secondInvalid) := by
  if positions : firstPosition = secondPosition then
    cases positions
    if cuts : firstCuts = secondCuts then
      cases cuts
      match Unit.Presentation.Check.compare firstReason secondReason with
      | .isTrue reasons => cases reasons; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    else exact .isFalse (fun same => by cases same; exact cuts rfl)
  else exact .isFalse (fun same => by cases same; exact positions rfl)

/-- Decide equality of unchecked-cut history failures from their retained outcomes. -/
public def CutsFailure.compare (first second : CutsFailure) : Decidable (first = second) := by
  cases first with
  | invalidCuts position cuts reason invalid =>
    cases second with
    | invalidCuts otherPosition otherCuts otherReason otherInvalid =>
      exact compareInvalidCuts position otherPosition reason invalid otherReason otherInvalid
    | _ => exact .isFalse (by intro same; cases same)
  | invalidSaved failure =>
    cases second with
    | invalidSaved other =>
      match RawFailure.compare failure other with
      | .isTrue equal => cases equal; exact .isTrue rfl
      | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
    | _ => exact .isFalse (by intro same; cases same)

/-- Scan unchecked cuts and continue using the saved frontier checked from them.

Each accepted cut list constructs its partition once. The same checked
frontier and continuation are passed to the existing history transition. -/
@[expose] public def scanCutsFrom (state : State) (position : Nat) : CutsCode → Except CutsFailure State
  | [] => .ok state
  | (cuts, cells, proposal) :: rest =>
    match checkSavedCuts cuts cells proposal with
    | .invalidCuts reason invalid => .error (.invalidCuts position cuts reason invalid)
    | .checked _ saved _ result =>
      withSaved state position saved proposal result
        CutsFailure.invalidSaved (fun next => scanCutsFrom next (position + 1) rest)

/-- Check an unchecked-cut history from the original initial state. -/
@[expose] public def checkCuts (code : CutsCode) : Except CutsFailure State := scanCutsFrom initial 0 code

/-- Project the original cuts and cells from an existing saved-frontier entry. -/
@[expose] public def cutsStep (entry : RawStep) : CutsStep :=
  (entry.1.1.cuts, entry.1.2, entry.2)

/-- Check finite saved-frontier and proposal entries from the original initial state. -/
@[expose] public def checkRaw (code : RawCode) : Except RawFailure State := scanRawFrom initial 0 code

set_option genInjectivity false in
/-- The result of checking and executing a finite pi history request.

Success retains the actual predecessor and returned indexed histories, their
binding to the original request, and its refinement and width certificates.
Failures retain the history scan or the nonpositive tolerance evidence. -/
public inductive RequestCheck (code : RawCode) (epsilon : Fraction.Rational) where
  /-- The finite history scan identified an invalid saved entry. -/
  | invalidHistory (failure : RawFailure) (checked : checkRaw code = .error failure)
  /-- The history was accepted but the requested tolerance is nonpositive. -/
  | nonpositive (previous : State) (checked : checkRaw code = .ok previous)
      (reason : epsilon ≤ 0)
  /-- The original process returned the retained history and its guarantees. -/
  | accepted (previous : State) (checked : checkRaw code = .ok previous)
      (positive : 0 < epsilon) (returned : State)
      (requested : returned = boundProcess.request previous epsilon positive)
      (refines : Purelib.Data.Rat.Interval.Refines (boundProcess.bound returned) (boundProcess.bound previous))
      (accurate : (boundProcess.bound returned).width < epsilon)

/-- Check a raw history and positive tolerance before using the original pi request.

The existing finite history scan and accuracy checker determine the two input
failures. A successful result retains the actual returned state and the original
process guarantees, including its existing cache and continuation behavior. -/
@[expose] public def requestRaw (code : RawCode) (epsilon : Fraction.Rational) : RequestCheck code epsilon :=
  match checked : checkRaw code with
  | .error failure => .invalidHistory failure checked
  | .ok previous =>
    match AccuracyRequest.Presentation.check epsilon with
    | .nonpositive reason => .nonpositive previous checked reason
    | .valid positive =>
      .accepted previous checked positive (boundProcess.request previous epsilon positive) rfl
        (boundProcess.request_refines previous epsilon positive)
        (boundProcess.accurate previous epsilon positive)

/-- Project an existing indexed history step into its finite saved-frontier data. -/
@[expose] public def rawStep (step : StepCode) : RawStep :=
  ((Frontier.quote step.1).val, Continuation.Proposal.rebind step.2)

/-- Scan proposed steps in order from an original state, retaining the first proved failure. -/
@[expose] public def scanFrom (state : State) (position : Nat) : Code → Except Failure State
  | [] => .ok state
  | ⟨saved, step⟩ :: rest =>
      letI : Decidable (state.1 = saved) := compareFrontier state.1 saved
      if binding : state.1 = saved then
        let result := Continuation.Proposal.check step
        match result.decision with
        | .isFalse invalid => .error (.invalidStep position saved step result invalid)
        | .isTrue valid =>
            let continuation : Producer.Continuation producer state.1 :=
              binding.symm ▸ result.read valid
            scanFrom (append state continuation) (position + 1) rest
      else .error (.wrongPrevious position state.1 saved binding)

/-- Check a finite history proposal from the original pi initial state. -/
@[expose] public def check (code : Code) : Except Failure State := scanFrom initial 0 code

/-- Project every retained continuation and its original predecessor frontier in order. -/
@[expose] public def quoteHistory {frontier : SourceFrontier value} :
    producer.controller.History producer.controller.origin frontier → Code
  | .initial => []
  | .next (previous := saved) history step => quoteHistory history ++ [⟨saved, (Continuation.Proposal.quote step).val⟩]

/-- Project the finite indexed history of an original pi state. -/
@[expose] public def quote (state : State) : Code := quoteHistory state.2

/-- Quote an original indexed history as ordered finite frontier/proposal entries. -/
@[expose] public def quoteRaw (state : State) : RawCode := (quote state).map rawStep

/-- Project the original ordered cut, cell and proposal data from an indexed history. -/
@[expose] public def quoteCuts (state : State) : CutsCode := (quoteRaw state).map cutsStep

/-- Scanning a quoted original step retains its exact continuation and indexed predecessor. -/
public theorem scanRawFrom_quotedStep (state : State) (step : Producer.Continuation producer state.1)
    (position : Nat) (rest : RawCode) :
    scanRawFrom state position (rawStep ⟨state.1, (Continuation.Proposal.quote step).val⟩ :: rest) =
      scanRawFrom (append state step) (position + 1) rest := by
  have originalValid := (Continuation.Proposal.quote step).property
  have originalRead : ∀ valid : Continuation.Proposal.Valid (Continuation.Proposal.quote step).val,
      Continuation.Proposal.read ⟨(Continuation.Proposal.quote step).val, valid⟩ = step :=
    fun _ => Continuation.Proposal.read_quote step
  generalize codeEq : (Continuation.Proposal.quote step).val = code at originalValid originalRead ⊢
  cases code
  all_goals
   obtain ⟨aligned, range, owner, readback, checked, ownerEq⟩ := Frontier.checkComplete_quote state.1
   cases ownerEq
   rw [scanRawFrom]
   unfold withSaved
   dsimp only [rawStep, Continuation.Proposal.rebind]
   unfold checkSaved
   rw [checked]
   dsimp only [Continuation.Proposal.rebind]
   split
   · next different _ => exact False.elim (different rfl)
   · next binding _ =>
    have bindingEq : binding = rfl := Subsingleton.elim _ _
    cases bindingEq
    split
    · next invalid _ => exact False.elim (invalid originalValid)
    · next valid _ =>
      rw [Continuation.Proposal.Check.read_eq, originalRead valid]

/-- A successful raw prefix continues at the original indexed state it reached. -/
public theorem scanRawFrom_append (state : State) (position : Nat) (first second : RawCode)
    (intermediate : State) (success : scanRawFrom state position first = .ok intermediate) :
    scanRawFrom state position (first ++ second) = scanRawFrom intermediate (position + first.length) second := by
  induction first generalizing state position with
  | nil =>
      change Except.ok state = Except.ok intermediate at success
      cases Except.ok.inj success
      change scanRawFrom intermediate position second = scanRawFrom intermediate (position + 0) second
      rw [Nat.add_zero]
  | cons entry rest ih =>
      rcases entry with ⟨saved, proposal⟩
      rw [scanRawFrom] at success
      rw [List.cons_append, scanRawFrom]
      unfold withSaved at success ⊢
      cases checked : checkSaved saved proposal with
      | invalidCells failure =>
          rw [checked] at success
          cases success
      | invalidRange aligned failure =>
          rw [checked] at success
          cases success
      | checked aligned range owner readback result =>
          rw [checked] at success
          dsimp only at success ⊢
          cases binding : compareFrontier state.1 owner with
          | isFalse different =>
              rw [binding] at success
              cases success
          | isTrue equal =>
              rw [binding] at success
              dsimp only at success ⊢
              cases decision : result.decision with
              | isFalse invalid =>
                  rw [decision] at success
                  cases success
              | isTrue valid =>
                  rw [decision] at success
                  have tail := ih _ (position + 1) success
                  have positions : (position + 1) + rest.length = position + (⟨saved, proposal⟩ :: rest).length := by
                    change (position + 1) + rest.length = position + Nat.succ rest.length
                    rw [Nat.add_assoc, Nat.one_add]
                  exact tail.trans (congrArg (fun n => scanRawFrom intermediate n second) positions)

/-- Raw quotation and scanning recover every original indexed history. -/
public theorem scanRawFrom_quoteHistory {frontier : SourceFrontier value}
    (history : producer.controller.History producer.controller.origin frontier) (position : Nat) :
    scanRawFrom initial position ((quoteHistory history).map rawStep) = .ok ⟨frontier, history⟩ := by
  induction history generalizing position with
  | initial => rfl
  | next previous step ih =>
      change scanRawFrom initial position
        ((quoteHistory previous ++ ([⟨_, (Continuation.Proposal.quote step).val⟩] : Code)).map rawStep) = _
      rw [Purelib.Data.List.Map.map_append]
      rw [scanRawFrom_append initial position _ _ ⟨_, previous⟩ (ih position)]
      dsimp only [List.map_cons, List.map_nil]
      rw [scanRawFrom_quotedStep ⟨_, previous⟩ step]
      rfl

/-- Checking the finite quotation of an original state recovers that exact state. -/
public theorem checkRaw_quoteRaw (state : State) : checkRaw (quoteRaw state) = .ok state := by
  cases state with
  | mk frontier history => exact scanRawFrom_quoteHistory history 0

/-- Lift an existing saved-history result to the unchecked-cut failure type. -/
@[expose] public def liftRaw : Except RawFailure State → Except CutsFailure State
  | .ok state => .ok state
  | .error failure => .error (.invalidSaved failure)

/-- Projecting cuts before a scan preserves its original result and failures. -/
public theorem scanCutsFrom_map (code : RawCode) (state : State) (position : Nat) :
    scanCutsFrom state position (code.map cutsStep) = liftRaw (scanRawFrom state position code) := by
  induction code generalizing state position with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨⟨partition, cells⟩, proposal⟩
    have original := (Unit.Presentation.quote partition).property
    cases checked : Unit.Presentation.check partition.cuts with
    | outOfRange index failed =>
      exact False.elim (failed (original.2 _ (List.getElem_mem index.isLt)))
    | badAdjacent _ _ _ _ _ _ failed => exact False.elim (failed original.1)
    | accepted valid =>
      have same : Frontier.fromCuts ⟨partition.cuts, valid⟩ cells = (partition, cells) := by
        apply Prod.ext
        · exact Unit.Presentation.read_quote partition
        · rfl
      rw [List.map_cons, scanCutsFrom]
      dsimp only [cutsStep]
      unfold checkSavedCuts
      rw [checked]
      dsimp only
      rw [same, scanRawFrom]
      cases result : checkSaved (partition, cells) proposal with
      | invalidCells failure => rfl
      | invalidRange aligned failure => rfl
      | checked aligned range owner readback outcome =>
        unfold withSaved
        dsimp only
        cases binding : compareFrontier state.1 owner with
        | isFalse different => rfl
        | isTrue equal =>
          cases decision : outcome.decision with
          | isFalse invalid => rfl
          | isTrue valid =>
            exact ih _ _

/-- Checking the unchecked-cut quotation recovers the original indexed state. -/
public theorem checkCuts_quoteCuts (state : State) : checkCuts (quoteCuts state) = .ok state := by
  unfold checkCuts quoteCuts
  rw [scanCutsFrom_map]
  change liftRaw (checkRaw (quoteRaw state)) = .ok state
  rw [checkRaw_quoteRaw]
  rfl

/-- A successful prefix scan continues from the exact original state it reached. -/
public theorem scanFrom_append (state : State) (position : Nat) (first second : Code)
    (intermediate : State) (success : scanFrom state position first = .ok intermediate) :
    scanFrom state position (first ++ second) = scanFrom intermediate (position + first.length) second := by
  induction first generalizing state position with
  | nil =>
      change Except.ok state = Except.ok intermediate at success
      cases Except.ok.inj success
      change scanFrom intermediate position second = scanFrom intermediate (position + 0) second
      rw [Nat.add_zero]
  | cons entry rest inductionHypothesis =>
      rcases entry with ⟨saved, step⟩
      rw [scanFrom] at success
      rw [List.cons_append, scanFrom]
      split at success
      · next binding =>
        rw [dif_pos binding]
        dsimp only at success ⊢
        cases recognized : (Continuation.Proposal.check step).decision with
        | isFalse invalid =>
          rw [recognized] at success
          cases success
        | isTrue valid =>
          rw [recognized] at success
          have tail := inductionHypothesis _ (position + 1) success
          have positions : (position + 1) + rest.length = position + (⟨saved, step⟩ :: rest).length := by
            change (position + 1) + rest.length = position + Nat.succ rest.length
            rw [Nat.add_assoc, Nat.one_add]
          exact tail.trans (congrArg (fun n => scanFrom intermediate n second) positions)
      · cases success

/-- Scanning a quoted original step appends that exact continuation. -/
public theorem scanFrom_quotedStep (state : State) (step : Producer.Continuation producer state.1)
    (position : Nat) (rest : Code) :
    scanFrom state position (⟨state.1, (Continuation.Proposal.quote step).val⟩ :: rest) =
      scanFrom (append state step) (position + 1) rest := by
  unfold scanFrom
  split
  · next binding =>
    dsimp only
    split
    · next invalid _ => exact False.elim (invalid (Continuation.Proposal.quote step).property)
    · next valid _ =>
      have bindingEq : binding = rfl := Subsingleton.elim _ _
      cases bindingEq
      have same : Continuation.Proposal.read ⟨(Continuation.Proposal.quote step).val, valid⟩ = step :=
        Continuation.Proposal.read_quote step
      rw [Continuation.Proposal.Check.read_eq]
      rw [same]
      rw [scanFrom.eq_def]
  · next different => exact False.elim (different rfl)

/-- Scanning a quoted history reconstructs its original indexed state. -/
public theorem scanFrom_quoteHistory {frontier : SourceFrontier value}
    (history : producer.controller.History producer.controller.origin frontier) (position : Nat) :
    scanFrom initial position (quoteHistory history) = .ok ⟨frontier, history⟩ := by
  induction history generalizing position with
  | initial => rfl
  | next previous step inductionHypothesis =>
      change scanFrom initial position (quoteHistory previous ++ [⟨_, (Continuation.Proposal.quote step).val⟩]) = _
      rw [scanFrom_append initial position (quoteHistory previous) _ ⟨_, previous⟩ (inductionHypothesis position)]
      rw [scanFrom_quotedStep ⟨_, previous⟩ step]
      rfl

/-- Checking the quotation of an original state recovers that exact state. -/
public theorem check_quote (state : State) : check (quote state) = .ok state := by
  cases state with
  | mk frontier history => exact scanFrom_quoteHistory history 0

/-- Quotation of an appended state retains the complete preceding history and the new step. -/
public theorem quote_append (state : State) (step : Producer.Continuation producer state.1) :
    quote (append state step) = quote state ++ [⟨state.1, (Continuation.Proposal.quote step).val⟩] := rfl

/-- A successful raw scan retains exactly the proposed finite entries after its starting history. -/
public theorem quoteRaw_scanRawFrom (code : RawCode) (state result : State) (position : Nat)
    (success : scanRawFrom state position code = .ok result) : quoteRaw result = quoteRaw state ++ code := by
  induction code generalizing state position with
  | nil =>
      change Except.ok state = Except.ok result at success
      cases Except.ok.inj success
      exact (List.append_nil (quoteRaw result)).symm
  | cons entry rest ih =>
      rcases entry with ⟨saved, proposal⟩
      rw [scanRawFrom] at success
      unfold withSaved at success
      cases checked : checkSaved saved proposal with
      | invalidCells failure =>
          rw [checked] at success
          cases success
      | invalidRange aligned failure =>
          rw [checked] at success
          cases success
      | checked aligned range owner readback outcome =>
          rw [checked] at success
          dsimp only at success
          cases binding : compareFrontier state.1 owner with
          | isFalse different =>
              rw [binding] at success
              cases success
          | isTrue equal =>
              rw [binding] at success
              dsimp only at success
              cases decision : outcome.decision with
              | isFalse invalid =>
                  rw [decision] at success
                  cases success
              | isTrue valid =>
                  rw [decision] at success
                  have tail := ih _ (position + 1) success
                  cases state with
                  | mk actual history =>
                    cases equal
                    rw [Continuation.Proposal.Check.read_eq] at tail
                    unfold quoteRaw at tail ⊢
                    rw [quote_append, Purelib.Data.List.Map.map_append] at tail
                    change actual = Frontier.read ⟨saved, aligned⟩ range at readback
                    have savedEq : (Frontier.quote actual).val = saved := by
                      rw [readback, Frontier.quote_read]
                    have proposalEq : Continuation.Proposal.rebind
                        (Continuation.Proposal.rebind proposal : Continuation.Proposal.Code actual) = proposal := by
                      rw [Continuation.Proposal.rebind_rebind, Continuation.Proposal.rebind_self]
                    have quoted := congrArg Subtype.val
                      (Continuation.Proposal.quote_read ⟨Continuation.Proposal.rebind proposal, valid⟩)
                    dsimp only [List.map_cons, List.map_nil, rawStep] at tail
                    rw [quoted, savedEq, proposalEq, List.append_assoc] at tail
                    exact tail

/-- Every accepted raw history agrees with the original history checker and its exact quotation. -/
public theorem checkRaw_agrees (code : RawCode) (state : State) (success : checkRaw code = .ok state) :
    check (quote state) = .ok state ∧ quoteRaw state = code :=
  ⟨check_quote state, quoteRaw_scanRawFrom code initial state 0 success⟩

/-- A successful unchecked-cut scan retains the exact proposed entries in order. -/
public theorem quoteCuts_scanCutsFrom (code : CutsCode) (state result : State) (position : Nat)
    (success : scanCutsFrom state position code = .ok result) :
    quoteCuts result = quoteCuts state ++ code := by
  induction code generalizing state position with
  | nil =>
    change Except.ok state = Except.ok result at success
    cases Except.ok.inj success
    exact (List.append_nil (quoteCuts result)).symm
  | cons entry rest ih =>
    rcases entry with ⟨cuts, cells, proposal⟩
    rw [scanCutsFrom] at success
    cases checked : checkSavedCuts cuts cells proposal with
    | invalidCuts reason invalid =>
      rw [checked] at success
      cases success
    | checked valid saved savedEq savedResult =>
      rw [checked] at success
      dsimp only at success
      cases savedEq
      let saved := Frontier.fromCuts ⟨cuts, valid⟩ cells
      change withSaved state position saved proposal savedResult _ _ = .ok result at success
      cases savedChecked : savedResult with
      | invalidCells failure =>
        rw [savedChecked] at success
        cases success
      | invalidRange aligned failure =>
        rw [savedChecked] at success
        cases success
      | checked aligned range owner readback outcome =>
        rw [savedChecked] at success
        dsimp only [withSaved] at success
        cases binding : compareFrontier state.1 owner with
        | isFalse different => rw [binding] at success; cases success
        | isTrue equal =>
          rw [binding] at success
          dsimp only at success
          cases decision : outcome.decision with
          | isFalse invalid => rw [decision] at success; cases success
          | isTrue validStep =>
            rw [decision] at success
            let next := append state (equal.symm ▸ outcome.read validStep)
            have tail := ih next (position + 1) success
            have one : scanRawFrom state position [(saved, proposal)] = .ok next := by
              rw [scanRawFrom]
              unfold withSaved
              have original : checkSaved saved proposal = savedResult := by
                unfold checkSavedCuts at checked
                cases cutResult : Unit.Presentation.check cuts with
                | outOfRange index failed => rw [cutResult] at checked; cases checked
                | badAdjacent _ _ _ _ _ _ failed => rw [cutResult] at checked; cases checked
                | accepted proof =>
                  rw [cutResult] at checked
                  dsimp only at checked
                  cases checked
                  rfl
              rw [original, savedChecked]
              dsimp only
              rw [binding, decision]
              rfl
            have quoted := quoteRaw_scanRawFrom [(saved, proposal)] state next position one
            have projected := congrArg (List.map cutsStep) quoted
            unfold quoteCuts at tail ⊢
            rw [Purelib.Data.List.Map.map_append] at projected
            dsimp only [List.map_cons, List.map_nil, cutsStep] at projected
            have retained : saved.1.cuts = cuts := Unit.Presentation.read_cuts ⟨cuts, valid⟩
            change _ = _ ++ [(saved.1.cuts, saved.2, proposal)] at projected
            rw [retained] at projected
            rw [projected, List.append_assoc] at tail
            exact tail

/-- A successful unchecked-cut history is exactly the quotation of its returned state. -/
public theorem checkCuts_agrees (code : CutsCode) (state : State) (success : checkCuts code = .ok state) :
    quoteCuts state = code := by
  exact quoteCuts_scanCutsFrom code initial state 0 success

/-- A successful scan retains precisely the proposed ordered steps after the preceding history. -/
public theorem quote_scanFrom (code : Code) (state result : State) (position : Nat)
    (success : scanFrom state position code = .ok result) : quote result = quote state ++ code := by
  induction code generalizing state position with
  | nil =>
      change Except.ok state = Except.ok result at success
      cases Except.ok.inj success
      exact (List.append_nil (quote result)).symm
  | cons entry rest inductionHypothesis =>
      rcases entry with ⟨saved, step⟩
      unfold scanFrom at success
      split at success
      · next binding =>
        dsimp only at success
        split at success
        · cases success
        · next valid _ =>
          have scanned := inductionHypothesis _ (position + 1) success
          rw [Continuation.Proposal.Check.read_eq] at scanned
          rw [quote_append] at scanned
          cases state with
          | mk actual history =>
            cases binding
            have quoted : (Continuation.Proposal.quote (Continuation.Proposal.read ⟨step, valid⟩)).val = step :=
              congrArg Subtype.val (Continuation.Proposal.quote_read ⟨step, valid⟩)
            rw [quoted, List.append_assoc] at scanned
            exact scanned
      · cases success

/-- A proposed history is valid when its finite scan reaches an original state. -/
@[expose] public def Valid (code : Code) : Prop := ∃ state, check code = .ok state

/-- Decide history validity by the same finite scan that returns located failures. -/
@[expose] public def recognize (code : Code) : Decidable (Valid code) :=
  match result : check code with
  | .ok state => .isTrue ⟨state, result⟩
  | .error _ => .isFalse (fun ⟨_, success⟩ => by rw [result] at success; cases success)

/-- A history proposal with its finite successful-scan evidence. -/
public abbrev Display := {code : Code // Valid code}

/-- Read the exact original state returned by the successful scan. -/
@[expose] public def read (display : Display) : State :=
  match result : check display.val with
  | .ok state => state
  | .error _ => False.elim (by
      obtain ⟨_, success⟩ := display.property
      rw [result] at success
      cases success)

/-- Quote an original state with its successful-scan certificate. -/
@[expose] public def display (state : State) : Display := ⟨quote state, state, check_quote state⟩

/-- A successful scan identifies the state returned by readback. -/
public theorem read_of_success (input : Display) (state : State) (success : check input.val = .ok state) :
    read input = state := by
  unfold read
  split
  · next found result => exact Except.ok.inj (result.symm.trans success)
  · next failure result => rw [success] at result; cases result

/-- Reading the quotation recovers the original indexed history state. -/
public theorem read_display (state : State) : read (display state) = state :=
  read_of_success (display state) state (check_quote state)

/-- Every successfully scanned proposal is the quotation of its resulting original state. -/
public theorem quote_of_success (code : Code) (state : State) (success : check code = .ok state) :
    quote state = code := by
  have equal := quote_scanFrom code initial state 0 success
  exact equal

/-- Quoting a read display recovers its original ordered proposals. -/
public theorem display_read (input : Display) : display (read input) = input := by
  apply Subtype.ext
  cases result : check input.val with
  | error failure =>
    obtain ⟨_, success⟩ := input.property
    rw [result] at success
    cases success
  | ok state =>
    have readEqual : read input = state := read_of_success input state result
    rw [readEqual]
    exact quote_of_success input.val state result

/-- Decide equality of one indexed step, preserving its original saved frontier. -/
@[expose] public def compareStep (first second : StepCode) : Decidable (first = second) := by
  cases first with
  | mk firstSaved firstStep =>
    cases second with
    | mk secondSaved secondStep =>
      match compareFrontier firstSaved secondSaved with
      | .isFalse different => exact .isFalse (fun same => different (congrArg Sigma.fst same))
      | .isTrue savedEqual =>
        cases savedEqual
        match Continuation.Proposal.compareCode firstStep secondStep with
        | .isFalse different => exact .isFalse (fun same => by cases same; exact different rfl)
        | .isTrue equal => cases equal; exact .isTrue rfl

/-- Two valid displays agree exactly when their original history states agree. -/
@[expose] public def Same (first second : Display) : Prop := first.val = second.val

/-- Decide finite ordered history-code equality with original indexed-step comparisons. -/
@[expose] public def compare (first second : Display) : Decidable (Same first second) := by
  letI (a b : StepCode) : Decidable (a = b) := compareStep a b
  exact inferInstanceAs (Decidable (first.val = second.val))

/-- History-code equality agrees with equality of the original indexed states. -/
public theorem same_iff_read_eq (first second : Display) : Same first second ↔ read first = read second := by
  constructor
  · intro equal
    have same : first = second := Subtype.ext equal
    cases same
    rfl
  · intro equal
    have quoted := congrArg display equal
    rw [display_read, display_read] at quoted
    exact congrArg Subtype.val quoted

/-- The finite presentation of actual pi continuation histories. -/
@[expose] public def history : Purelib.Data.Presentation Code where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-!
`check` scans the ordered proposals from the original controller origin. Each
step retains its saved frontier and the continuation fields; `Failure` records
the first mismatched predecessor or invalid continuation, with a proof of the
specific failed condition. `check_quote`, `read_display`, `display_read` and
`same_iff_read_eq` connect the finite scan and comparison to the original
indexed history. The proposals accept certified preparation/frontier fields and
derive the original split proof from each checked common collection. Recognition
of independently supplied proofs and the underlying proof/runtime boundary are
separate obligations.
-/

end History

end Purelib.Approximation.Rational.Pi.Source.Presentation
