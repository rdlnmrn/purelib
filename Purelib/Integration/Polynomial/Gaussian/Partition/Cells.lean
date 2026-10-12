module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Partition.Child
public import Purelib.Integration.Polynomial.Gaussian.Partition.Request
public import Purelib.Integration.Polynomial.Gaussian.Partition.Segment
import Purelib.Integration.Polynomial.Gaussian.Partition.Source
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Segment.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction

/-!
# Source-indexed Gaussian polynomial partitions

The ordered source segments retain their cut requests, child restrictions and
cached integral samples. Compilation and comparison preserve the nominal
source owners, dependent indices and exact ordered model readbacks.
-/

public section
namespace Purelib.Integration.Polynomial.Gaussian.Partition

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian

open Purelib.Integration.Polynomial.Gaussian.Segment.Basic (PolynomialSegment)
set_option genInjectivity false in
/-- An ordered family of compiled polynomial segments indexed by the exact original source path.

Each retained head compilation belongs to its original source segment, and the dependent tail preserves the remaining
source list. -/
inductive Cells.CompiledCells : Source.PolynomialPath → Type
  /-- The empty compilation indexed by the exact empty source path. -/ | nil :
    Purelib.Integration.Polynomial.Gaussian.Partition.Cells.CompiledCells []
  /-- Retain the original head segment compilation and exact source-indexed tail compilation. -/ | cons {source :
    PolynomialSegment} {rest : Source.PolynomialPath}
      (head : Segment.CompiledSegment source) (tail :
        Purelib.Integration.Polynomial.Gaussian.Partition.Cells.CompiledCells rest) :
        Purelib.Integration.Polynomial.Gaussian.Partition.Cells.CompiledCells (source :: rest)

constructive_injectivity Cells.CompiledCells

/-- Compile the retained cut request for each exact original source segment.

The construction retains its supplied source and parameters. Cached data is computed once from those inputs and its
defining equalities retain that construction. -/
@[expose] def Cells.CompiledCells.canonical : {source : Source.PolynomialPath} → Request.CutRequest source →
  Cells.CompiledCells source
  | [], .nil => .nil
  | source :: _, .cons cuts tail => .cons (Segment.CompiledSegment.canonical source cuts)
    (Purelib.Integration.Polynomial.Gaussian.Partition.Cells.CompiledCells.canonical tail)

/-- Concatenate the retained compiled segment models in original source order.

The construction concatenates the cached head model with the model of the unchanged source-indexed tail. -/
@[expose] def Cells.CompiledCells.model : {source : Source.PolynomialPath} → Cells.CompiledCells source →
  Path.Basic.PathModel
  | [], .nil => ⟨[]⟩
  | _ :: _, .cons head tail => head.model.concat tail.model

/-- Sum the retained compiled segment samples in original source order.

The construction adds the cached head sample to the sample of the unchanged source-indexed tail. -/
@[expose] def Cells.CompiledCells.sample : {source : Source.PolynomialPath} → Cells.CompiledCells source →
  Basic.Canonical
  | [], .nil => 0
  | _ :: _, .cons head tail => head.sample + tail.sample

/-- The retained compiled sample equals the exact concatenated model's integral sample.

The sample and model remain caches of the same retained compilation. Their defining equalities transport the exact
scalar readback. -/
theorem Cells.CompiledCells.sample_model : ∀ {source : Source.PolynomialPath} (compiled : Cells.CompiledCells source),
    compiled.sample = compiled.model.integralSample
  | [], .nil => rfl
  | _ :: _, .cons head tail => by
      change head.sample + tail.sample = (head.model.concat tail.model).integralSample
      rw [Path.Basic.PathModel.integralSample_concat,
        head.sample_model, tail.sample_model]

/-- The retained compiled sample equals the original source path's exact sample.

The retained compilation follows the supplied source order. Its exact samples sum to the integral sample of that same
source. -/
theorem Cells.CompiledCells.sample_source : ∀ {source : Source.PolynomialPath} (compiled : Cells.CompiledCells source),
    compiled.sample = Source.sourceSample source
  | [], .nil => rfl
  | _ :: _, .cons head tail => by
      change head.sample + tail.sample = _
      rw [head.sample_source, tail.sample_source]
      rfl

/-- Prepending original compiled child models preserves the remaining model's total allowance.

Every retained child contributes zero weighted allowance, so prepending its exact model leaves the remaining total
unchanged. -/
private theorem Cells.CompiledCells.fold_allowance {source : PolynomialSegment} :
    ∀ (children : List (Child source)) (rest : List Cell.Basic.CellModel),
      (⟨(children.map Child.model) ++ rest⟩ : Path.Basic.PathModel).totalWeightedAllowance =
        (⟨rest⟩ : Path.Basic.PathModel).totalWeightedAllowance
  | [], _ => rfl
  | child :: children, rest => by
      change child.model.weightedAllowance +
        (⟨(children.map Child.model) ++ rest⟩ : Path.Basic.PathModel).totalWeightedAllowance = _
      rw [child.weightedAllowance_zero, Fraction.Field.zero_add,
        Purelib.Integration.Polynomial.Gaussian.Partition.Cells.CompiledCells.fold_allowance]

/-- The exact compiled model has zero total weighted allowance.

The retained concatenated model consists of exact child cells. Their ordered weighted allowances sum to zero. -/
theorem Cells.CompiledCells.totalAllowance_zero : ∀ {source : Source.PolynomialPath} (compiled : Cells.CompiledCells
  source),
    compiled.model.totalWeightedAllowance = 0
  | [], .nil => rfl
  | _ :: _, .cons head tail => by
      change (head.model.concat tail.model).totalWeightedAllowance = 0
      rw [head.model_eq]
      change (⟨(head.children.map Child.model) ++ tail.model.cells⟩ : Path.Basic.PathModel).totalWeightedAllowance
        = 0
      rw [Cells.CompiledCells.fold_allowance]
      exact tail.totalAllowance_zero

/-- The exact compiled model has zero aggregate allowance.

The retained model is assembled from exact child models. Its aggregate allowance uses their zero total allowance. -/
theorem Cells.CompiledCells.allowance_zero {source : Source.PolynomialPath} (compiled : Cells.CompiledCells source) :
    compiled.model.aggregateAllowance = 0 := by
  unfold Path.Basic.PathModel.aggregateAllowance
  rw [compiled.totalAllowance_zero, Fraction.Field.mul_zero_direct]

end Purelib.Integration.Polynomial.Gaussian.Partition
end
