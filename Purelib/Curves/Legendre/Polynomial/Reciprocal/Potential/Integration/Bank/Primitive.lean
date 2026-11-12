module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Bank
public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Source.Primitive.Remainder
public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Source.Primitive.Bounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Nat.Order

/-! # One regular sample before all original reciprocal-bank requests

The first pass retains only the original local residual bounds and paid
Selections. Their actual maximum determines one shared polynomial sample
and one physical coefficient. The second pass builds the original physical
budgets and requests on those same caches before any reciprocal sample.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover.Bank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives (PolynomialSample)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.PhysicalPrimitive
  (RemainderBounds regularNumerator)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial Box)
open Purelib.Approximation.Rational.Geometric.Search (Selection)

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}
    {sourceDifferential : Differential 1} {count : Nat}
    {error : Coordinate} {errorPositive : 0 < error} {floor : Nat}

namespace Primitive

namespace Selections

/-- Original residual bounds and one whole paid Selection on the same planned coordinate, followed by a tail. -/
@[expose] def Entry {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    (data : ParentData cap sourceDifferential count parent) {originalTail : Type 3}
    (planned : Plan.Entry data error errorPositive floor originalTail)
    (target : Coordinate) (positive : 0 < target) (pFloor : Nat) (remaining : Type 3) : Type 3 :=
  (bounds : { value : RemainderBounds data.comparison planned.2.1 //
    value = RemainderBounds.build data.comparison planned.2.1 }) ×
  (_selection : { value : Selection bounds.val.scale pFloor target //
    value = Selection.build bounds.val.scale bounds.val.scale_nonnegative pFloor target positive }) × remaining

/-- Package abstract original head bounds and Selection with their exact factory equations. -/
private def ofParts {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    (data : ParentData cap sourceDifferential count parent) {originalTail remaining : Type 3}
    (planned : Plan.Entry data error errorPositive floor originalTail)
    (target : Coordinate) (positive : 0 < target) (pFloor : Nat)
    (bounds : RemainderBounds data.comparison planned.2.1)
    (boundsEq : bounds = RemainderBounds.build data.comparison planned.2.1)
    (selection : Selection bounds.scale pFloor target)
    (selectionEq : selection = Selection.build bounds.scale bounds.scale_nonnegative pFloor target positive)
    (rest : remaining) : Entry data planned target positive pFloor remaining :=
  ⟨⟨bounds, boundsEq⟩, ⟨selection, selectionEq⟩, rest⟩

end Selections

/-- The ordered local residual caches and paid Selections, with no polynomial sample constructed per parent. -/
@[expose] def Selections (target : Coordinate) (positive : 0 < target) (pFloor : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → Plan error errorPositive floor bank → Type 3
  | [], .nil, _ => PUnit
  | _ :: _, .cons data rest, planned =>
      Selections.Entry data planned target positive pFloor
        (Selections target positive pFloor rest planned.2.2.2)

namespace Selections

variable {target : Coordinate} {positive : 0 < target} {pFloor : Nat}

/-- Build the retained residual bounds and paid Selection before consuming the same companion tail. -/
private def buildStep {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (target : Coordinate) (positive : 0 < target) (pFloor : Nat)
    (finishTail : Unit → Selections target positive pFloor rest planned.2.2.2) :
    Selections target positive pFloor (.cons data rest) planned :=
  let bounds := RemainderBounds.build data.comparison planned.2.1
  let selection := Selection.build bounds.scale bounds.scale_nonnegative pFloor target positive
  let remaining := finishTail ()
  ofParts (parameter := parameter) (frame := frame) (cap := cap)
    data planned target positive pFloor bounds rfl selection rfl remaining

/-- Select once per original parent without constructing any regular polynomial or reciprocal sample. -/
def build (target : Coordinate) (positive : 0 < target) (pFloor : Nat) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (planned : Plan error errorPositive floor bank) →
        Selections target positive pFloor bank planned
  | [], .nil, _ => ⟨⟩
  | _ :: _, .cons data rest, planned =>
      buildStep (parameter := parameter) (frame := frame) (cap := cap)
        data rest planned target positive pFloor (fun _ => build target positive pFloor rest planned.2.2.2)

/-- Read the maximum of the same retained Selection stages, starting at the original regular floor. -/
def maximum : {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
    (bank : Bank cap sourceDifferential count parents) → (planned : Plan error errorPositive floor bank) →
      Selections target positive pFloor bank planned → Nat
  | [], .nil, _, _ => pFloor
  | _ :: _, .cons _ rest, planned, cached =>
      Nat.max cached.2.1.val.stage (maximum rest planned.2.2.2 cached.2.2)

/-- The nonempty maximum reads that actual head Selection and the same remaining selections. -/
private theorem packaged_maximum_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (cached : Selections target positive pFloor (.cons data rest) planned) :
    maximum (.cons data rest) planned cached =
      Nat.max cached.2.1.val.stage (maximum rest planned.2.2.2 cached.2.2) := by rfl

/-- The nonempty maximum reads that actual head Selection and the same remaining selections. -/
theorem maximum_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (cached : Selections target positive pFloor (.cons data rest) planned) :
    maximum (.cons data rest) planned cached =
      Nat.max cached.2.1.val.stage (maximum rest planned.2.2.2 cached.2.2) :=
  packaged_maximum_cons data rest planned cached

/-- The first retained paid Selection is no later than the actual common regular stage. -/
theorem head_le {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (cached : Selections target positive pFloor (.cons data rest) planned) :
    cached.2.1.val.stage ≤ maximum (.cons data rest) planned cached :=
  Eq.mp (congrArg (fun value : Nat => cached.2.1.val.stage ≤ value)
    (maximum_cons data rest planned cached).symm) (Data.Nat.Order.le_max_left _ _)

/-- The remaining original selections keep their paid stages below the same outer maximum. -/
theorem tail_le {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (cached : Selections target positive pFloor (.cons data rest) planned) :
    maximum rest planned.2.2.2 cached.2.2 ≤ maximum (.cons data rest) planned cached :=
  Eq.mp (congrArg (fun value : Nat => maximum rest planned.2.2.2 cached.2.2 ≤ value)
    (maximum_cons data rest planned cached).symm) (Data.Nat.Order.le_max_right _ _)

end Selections

namespace Requests

/-- Original budgets and requests share one sample and certified coefficient, followed by a tail. -/
@[expose] def Entry {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    (data : ParentData cap sourceDifferential count parent) {originalTail : Type 3}
    (planned : Plan.Entry data error errorPositive floor originalTail)
    {index : Nat} {box : Box}
    (sample : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = sample.physicalCoefficient })
    (target : Coordinate) (positive : 0 < target) (remaining : Type 3) : Type 3 :=
  (bounds : { value : PhysicalPrimitive.Bounds data.comparison sample //
    value = PhysicalPrimitive.Bounds.ofCoefficient data.comparison sample coefficient }) ×
  (paid : { value : PhysicalPrimitive.Bounds.Requests bounds.val planned.1 planned.2.1 floor target error //
    value = bounds.val.requests planned.1 planned.2.1 floor target positive error errorPositive }) ×
  (_required : { value : Nat // value = Nat.max paid.val.1.stage paid.val.2.selection.stage }) × remaining

/-- Package the original budgets and requests on the shared coefficient without rebuilding it. -/
private def ofParts {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    (data : ParentData cap sourceDifferential count parent) {originalTail remaining : Type 3}
    (planned : Plan.Entry data error errorPositive floor originalTail) {index : Nat} {box : Box}
    (sample : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = sample.physicalCoefficient })
    (target : Coordinate) (positive : 0 < target)
    (bounds : PhysicalPrimitive.Bounds data.comparison sample)
    (boundsEq : bounds = PhysicalPrimitive.Bounds.ofCoefficient data.comparison sample coefficient)
    (paid : PhysicalPrimitive.Bounds.Requests bounds planned.1 planned.2.1 floor target error)
    (paidEq : paid = bounds.requests planned.1 planned.2.1 floor target positive error errorPositive)
    (required : Nat) (requiredEq : required = Nat.max paid.1.stage paid.2.selection.stage)
    (rest : remaining) : Entry data planned sample coefficient target positive remaining :=
  ⟨⟨bounds, boundsEq⟩, ⟨paid, paidEq⟩, ⟨required, requiredEq⟩, rest⟩

end Requests

/-- The original per-parent physical requests share one literal regular sample and physical coefficient. -/
@[expose] def Requests {index : Nat} {box : Box}
    (sample : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = sample.physicalCoefficient })
    (target : Coordinate) (positive : 0 < target) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → Plan error errorPositive floor bank → Type 3
  | [], .nil, _ => PUnit
  | _ :: _, .cons data rest, planned =>
      Requests.Entry data planned sample coefficient target positive
        (Requests sample coefficient target positive rest planned.2.2.2)

namespace Requests

variable {index : Nat} {box : Box}
    {sample : PolynomialSample cap (regularNumerator (parameter := parameter)) index box}
    {coefficient : { value : Polynomial // value = sample.physicalCoefficient }}
    {target : Coordinate} {positive : 0 < target}

/-- Build only the comparison-specific budgets and actual q requests before consuming the same tail. -/
private def buildStep {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (sample : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = sample.physicalCoefficient })
    (target : Coordinate) (positive : 0 < target)
    (finishTail : Unit → Requests sample coefficient target positive rest planned.2.2.2) :
    Requests sample coefficient target positive (.cons data rest) planned :=
  let bounds := PhysicalPrimitive.Bounds.ofCoefficient data.comparison sample coefficient
  let paid := bounds.requests planned.1 planned.2.1 floor target positive error errorPositive
  let required := Nat.max paid.1.stage paid.2.selection.stage
  let remaining := finishTail ()
  ofParts (parameter := parameter) (frame := frame) (cap := cap)
    data planned sample coefficient target positive bounds rfl paid rfl required rfl remaining

/-- Construct one actual request pair per head using the same shared sample and coefficient throughout. -/
def build {index : Nat} {box : Box}
    (sample : PolynomialSample cap (regularNumerator (parameter := parameter)) index box)
    (coefficient : { value : Polynomial // value = sample.physicalCoefficient })
    (target : Coordinate) (positive : 0 < target) :
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
      (bank : Bank cap sourceDifferential count parents) → (planned : Plan error errorPositive floor bank) →
        Requests sample coefficient target positive bank planned
  | [], .nil, _ => ⟨⟩
  | _ :: _, .cons data rest, planned =>
      buildStep (parameter := parameter) (frame := frame) (cap := cap)
        data rest planned sample coefficient target positive
        (fun _ => build sample coefficient target positive rest planned.2.2.2)

/-- Read the original head maximum before consuming an abstract retained tail.

The complete planning and request heads keep their original dependent
indices. Only the tail's type is abstract, so the recursive scan does not
expand another parent's physical budget family to read one scalar.
-/
private def maximumStep {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    (data : ParentData cap sourceDifferential count parent) {originalTail remaining : Type 3}
    (planned : Plan.Entry data error errorPositive floor originalTail)
    (cached : Entry data planned sample coefficient target positive remaining)
    (finishTail : remaining → Nat) : Nat :=
  Nat.max cached.2.2.1.val (finishTail cached.2.2.2)

/-- Read the maximum of the actual cached q request stages, retaining the original q floor for the empty bank. -/
def maximum : {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)} →
    (bank : Bank cap sourceDifferential count parents) → (planned : Plan error errorPositive floor bank) →
      Requests sample coefficient target positive bank planned → Nat
  | [], .nil, _, _ => floor
  | _ :: _, .cons data rest, planned, cached =>
      maximumStep (parameter := parameter) (frame := frame) (cap := cap)
        data planned cached (fun tail => maximum rest planned.2.2.2 tail)

/-- The nonempty q maximum reads its retained head maximum and original tail. -/
private theorem packaged_maximum_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (cached : Requests sample coefficient target positive (.cons data rest) planned) :
    maximum (.cons data rest) planned cached =
      Nat.max cached.2.2.1.val (maximum rest planned.2.2.2 cached.2.2.2) := by rfl

/-- The nonempty q maximum reads its retained head maximum and original tail. -/
theorem maximum_cons {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (cached : Requests sample coefficient target positive (.cons data rest) planned) :
    maximum (.cons data rest) planned cached =
      Nat.max cached.2.2.1.val (maximum rest planned.2.2.2 cached.2.2.2) :=
  packaged_maximum_cons data rest planned cached

/-- The remaining original q requests stay below the same outer maximum. -/
theorem tail_le {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (cached : Requests sample coefficient target positive (.cons data rest) planned) :
    maximum rest planned.2.2.2 cached.2.2.2 ≤ maximum (.cons data rest) planned cached :=
  Eq.mp (congrArg (fun value : Nat => maximum rest planned.2.2.2 cached.2.2.2 ≤ value)
    (maximum_cons data rest planned cached).symm) (Data.Nat.Order.le_max_right _ _)

/-- An actual original potential request above the retained q maximum pays this same head's physical requests. -/
theorem head_paid {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (cached : Requests sample coefficient target positive (.cons data rest) planned)
    {first : data.data.first.coordinates.Potential} {last : data.data.last.coordinates.Potential} {common : Nat}
    (actual : Request planned.1 data.data first last planned.2.1 error errorPositive common)
    (later : maximum (.cons data rest) planned cached ≤ common) :
    Nat.max cached.2.1.val.1.stage cached.2.1.val.2.selection.stage ≤ actual.2.2.2.2.val := by
  have head : cached.2.2.1.val ≤ maximum (.cons data rest) planned cached :=
    Eq.mp (congrArg (fun value : Nat => cached.2.2.1.val ≤ value)
      (maximum_cons data rest planned cached).symm) (Data.Nat.Order.le_max_left _ _)
  have bounded := head.trans (later.trans (PotentialComparison.Request.floor_le actual))
  exact Eq.mp (congrArg (fun value : Nat => value ≤ actual.2.2.2.2.val) cached.2.2.1.property) bounded

end Requests

end Primitive

/-- A two-pass companion retains all local Selections, one shared P sample/coefficient and the resulting q requests. -/
@[expose] def Primitive (target : Coordinate) (quarterPositive : 0 < target / 4) (pFloor : Nat) (box : Box)
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (planned : Plan error errorPositive floor bank) : Type 3 :=
  (selections : Primitive.Selections (target / 4) quarterPositive pFloor bank planned) ×
  (pStage : { value : Nat // value = Primitive.Selections.maximum bank planned selections }) ×
  (sample : { value : PolynomialSample cap (regularNumerator (parameter := parameter)) pStage.val box //
    value = PolynomialSample.build cap (regularNumerator (parameter := parameter)) pStage.val box }) ×
  (coefficient : { value : Polynomial // value = sample.val.physicalCoefficient }) ×
  Primitive.Requests sample.val coefficient (target / 4) quarterPositive bank planned

namespace Primitive

variable {target : Coordinate} {quarterPositive : 0 < target / 4} {pFloor : Nat} {box : Box}

/-- Package the abstract complete two-pass caches on their same original bank and plan. -/
private def ofParts {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (planned : Plan error errorPositive floor bank)
    (target : Coordinate) (quarterPositive : 0 < target / 4) (pFloor : Nat) (box : Box)
    (selections : Selections (target / 4) quarterPositive pFloor bank planned)
    (pStage : Nat) (pStageEq : pStage = Selections.maximum bank planned selections)
    (sample : PolynomialSample cap (regularNumerator (parameter := parameter)) pStage box)
    (sampleEq : sample = PolynomialSample.build cap (regularNumerator (parameter := parameter)) pStage box)
    (coefficient : { value : Polynomial // value = sample.physicalCoefficient })
    (requests : Requests sample coefficient (target / 4) quarterPositive bank planned) :
    Primitive target quarterPositive pFloor box bank planned :=
  ⟨selections, ⟨pStage, pStageEq⟩, ⟨sample, sampleEq⟩, coefficient, requests⟩

/-- Select all P floors first, build one shared sample/coefficient, then retain every original physical q request. -/
def build {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (bank : Bank cap sourceDifferential count parents) (planned : Plan error errorPositive floor bank)
    (target : Coordinate) (quarterPositive : 0 < target / 4) (pFloor : Nat) (box : Box) :
    Primitive target quarterPositive pFloor box bank planned :=
  let selections := Selections.build (target / 4) quarterPositive pFloor bank planned
  let pStage := Selections.maximum bank planned selections
  let sample := PolynomialSample.build cap (regularNumerator (parameter := parameter)) pStage box
  let coefficient := (⟨sample.physicalCoefficient, rfl⟩ : { value : Polynomial // value = sample.physicalCoefficient })
  let requests := Requests.build sample coefficient (target / 4) quarterPositive bank planned
  ofParts (parameter := parameter) (frame := frame) (cap := cap)
    bank planned target quarterPositive pFloor box selections pStage rfl sample rfl coefficient requests

/-- Read the one shared regular sample at its original common P stage. -/
def sample {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {bank : Bank cap sourceDifferential count parents} {planned : Plan error errorPositive floor bank}
    (cached : Primitive target quarterPositive pFloor box bank planned) :
    PolynomialSample cap (regularNumerator (parameter := parameter)) cached.2.1.val box := cached.2.2.1.val

/-- Read the same whole certified physical coefficient shared by all head budgets. -/
def coefficient {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {bank : Bank cap sourceDifferential count parents} {planned : Plan error errorPositive floor bank}
    (cached : Primitive target quarterPositive pFloor box bank planned) :
    { value : Polynomial // value = cached.sample.physicalCoefficient } := cached.2.2.2.1

/-- The shared sample is the original complete polynomial factory at that same retained P stage. -/
private theorem packaged_sample_eq {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {bank : Bank cap sourceDifferential count parents} {planned : Plan error errorPositive floor bank}
    (cached : Primitive target quarterPositive pFloor box bank planned) :
    cached.sample = PolynomialSample.build cap (regularNumerator (parameter := parameter)) cached.2.1.val box :=
  cached.2.2.1.property

/-- The shared sample is the original complete polynomial factory at that same retained P stage. -/
theorem sample_eq {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {bank : Bank cap sourceDifferential count parents} {planned : Plan error errorPositive floor bank}
    (cached : Primitive target quarterPositive pFloor box bank planned) :
    cached.sample = PolynomialSample.build cap (regularNumerator (parameter := parameter)) cached.2.1.val box :=
  packaged_sample_eq cached

/-- The physical coefficient reader retains the same actual polynomial cache. -/
private theorem packaged_coefficient_value {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {bank : Bank cap sourceDifferential count parents} {planned : Plan error errorPositive floor bank}
    (cached : Primitive target quarterPositive pFloor box bank planned) :
    cached.coefficient.val = cached.2.2.2.1.val := by rfl

/-- The physical coefficient reader retains the same actual polynomial cache. -/
theorem coefficient_value {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {bank : Bank cap sourceDifferential count parents} {planned : Plan error errorPositive floor bank}
    (cached : Primitive target quarterPositive pFloor box bank planned) :
    cached.coefficient.val = cached.2.2.2.1.val := packaged_coefficient_value cached

/-- The head's original Selection is paid at the unchanged common P index. -/
theorem head_pStage {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (cached : Primitive target quarterPositive pFloor box (.cons data rest) planned) :
    cached.1.2.1.val.stage ≤ cached.2.1.val :=
  Eq.mp (congrArg (fun value : Nat => cached.1.2.1.val.stage ≤ value) cached.2.1.property.symm)
    (Selections.head_le data rest planned cached.1)

/-- Retain the actual maximum of the original q plan and the same shared-sample physical request bank. -/
def commonFloor {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {bank : Bank cap sourceDifferential count parents} {planned : Plan error errorPositive floor bank}
    (cached : Primitive target quarterPositive pFloor box bank planned) :
    { value : Nat // value = Nat.max (Plan.commonFloor bank planned)
      (Requests.maximum bank planned cached.2.2.2.2) } :=
  let original := Plan.commonFloor bank planned
  let physical := Requests.maximum bank planned cached.2.2.2.2
  let common := Nat.max original physical
  ⟨common, rfl⟩

section

variable {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    {bank : Bank cap sourceDifferential count parents} {planned : Plan error errorPositive floor bank}
    (cached : Primitive target quarterPositive pFloor box bank planned)

/-- The retained common q floor pays the original plan's actual floor. -/
theorem original_le
    (common : { value : Nat // value = Nat.max (Plan.commonFloor bank planned)
      (Requests.maximum bank planned cached.2.2.2.2) }) : Plan.commonFloor bank planned ≤ common.val :=
  Eq.mp (congrArg (fun value : Nat => Plan.commonFloor bank planned ≤ value) common.property.symm)
    (Data.Nat.Order.le_max_left _ _)

/-- The retained common q floor pays every new physical request maximum represented by the actual scan. -/
theorem requests_le
    (common : { value : Nat // value = Nat.max (Plan.commonFloor bank planned)
      (Requests.maximum bank planned cached.2.2.2.2) }) :
    Requests.maximum bank planned cached.2.2.2.2 ≤ common.val :=
  Eq.mp (congrArg (fun value : Nat => Requests.maximum bank planned cached.2.2.2.2 ≤ value) common.property.symm)
    (Data.Nat.Order.le_max_right _ _)

end

/-- An original request at the retained common q floor pays the same actual first-head physical requests. -/
theorem head_qStage {parent : Parent (Fibre.frameCurve frame) sourceDifferential}
    {parents : List (Parent (Fibre.frameCurve frame) sourceDifferential)}
    (data : ParentData cap sourceDifferential count parent) (rest : Bank cap sourceDifferential count parents)
    (planned : Plan error errorPositive floor (.cons data rest))
    (cached : Primitive target quarterPositive pFloor box (.cons data rest) planned)
    (common : { value : Nat // value = Nat.max (Plan.commonFloor (.cons data rest) planned)
      (Requests.maximum (.cons data rest) planned cached.2.2.2.2) })
    {first : data.data.first.coordinates.Potential} {last : data.data.last.coordinates.Potential}
    (actual : Request planned.1 data.data first last planned.2.1 error errorPositive common.val) :
    Nat.max cached.2.2.2.2.2.1.val.1.stage cached.2.2.2.2.2.1.val.2.selection.stage ≤ actual.2.2.2.2.val :=
  Requests.head_paid data rest planned cached.2.2.2.2 actual (requests_le cached common)

end Primitive

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential.Integration.Plan

end
