module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.GetD
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Partition.Cells
public import Purelib.Integration.Polynomial.Gaussian.Partition.Common
public import Purelib.Integration.Polynomial.Gaussian.Partition.Ownership
import Purelib.Integration.Polynomial.Gaussian.Partition.Request
import Purelib.Integration.Polynomial.Gaussian.Partition.Source
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Segment.Basic

/-!
# Source-indexed Gaussian polynomial partitions

The ordered source segments retain their cut requests, child restrictions and
cached integral samples. Compilation and comparison preserve the nominal
source owners, dependent indices and exact ordered model readbacks.
-/

public section
namespace Purelib.Integration.Polynomial.Gaussian.Partition

open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- A compiled original polynomial path with cached model and sample readbacks.

The retained source-indexed cell compilation remains the owner of the cached concatenated model and exact sample. -/
structure Compiled.CompiledPartition (source : Source.PolynomialPath) where
  /-- The retained compilation indexed by the original source path. -/ cells : Cells.CompiledCells source
  /-- The cached concatenated path model. -/ model : Path.Basic.PathModel
  /-- The cached model equals the exact retained cell compilation's model. -/ model_eq : model = cells.model
  /-- The cached Gaussian integral sample. -/ sample : Basic.Canonical
  /-- The cached sample equals the exact retained cell compilation's sample. -/ sample_eq : sample = cells.sample

constructive_injectivity Compiled.CompiledPartition

/-- Compile the original source path's retained cut request and cache its exact model and sample.

The source-indexed cells are computed once. Both cached readbacks consume that same cell compilation and retain their
defining equalities. -/
@[expose] def Compiled.compilePartition (source : Source.PolynomialPath) (request : Request.CutRequest source) :
  Compiled.CompiledPartition source :=
  let cells := Cells.CompiledCells.canonical request
  { cells := cells
    model := cells.model
    model_eq := rfl
    sample := cells.sample
    sample_eq := rfl }

/-- The cached compiled sample equals its cached model's integral sample.

The sample and model remain caches of the same retained compilation. Their defining equalities transport the exact
scalar readback. -/
theorem Compiled.CompiledPartition.sample_model {source : Source.PolynomialPath} (compiled : Compiled.CompiledPartition
  source) :
    compiled.sample = compiled.model.integralSample := by
  rw [compiled.sample_eq, compiled.model_eq, compiled.cells.sample_model]

/-- The cached compiled sample equals the exact original source sample.

The retained compilation follows the supplied source order. Its exact samples sum to the integral sample of that same
source. -/
theorem Compiled.CompiledPartition.sample_source {source : Source.PolynomialPath} (compiled : Compiled.CompiledPartition
  source) :
    compiled.sample = Source.sourceSample source := by
  rw [compiled.sample_eq, compiled.cells.sample_source]

/-- The cached compiled model has zero aggregate allowance.

The retained model is assembled from exact child models. Its aggregate allowance uses their zero total allowance. -/
theorem Compiled.CompiledPartition.allowance_zero {source : Source.PolynomialPath} (compiled :
  Compiled.CompiledPartition source) :
    compiled.model.aggregateAllowance = 0 := by
  rw [compiled.model_eq, compiled.cells.allowance_zero]

/-- Read the exact original-owned compiled children starting at source index zero.

Each entry retains its nominal source and dependent child. The ordered readback advances the source index once per
segment. -/
@[expose] def Compiled.CompiledPartition.ownedChildren {source : Source.PolynomialPath} (compiled :
  Compiled.CompiledPartition source) : List Ownership.OwnedChild :=
  compiled.cells.ownedChildren 0

/-- Each retained child reads back the exact original source segment at its retained source index.

The child remains indexed by its nominal source owner. The retained natural source index reads that same segment through
optional finite-list lookup. -/
theorem Compiled.CompiledPartition.owner_lookup {source : Source.PolynomialPath} (compiled : Compiled.CompiledPartition
  source)
    {entry : Ownership.OwnedChild} (member : entry ∈ compiled.ownedChildren) :
    Purelib.Data.List.getElem? source entry.sourceIndex = some entry.source := by
  obtain ⟨index, identity, lookup⟩ := compiled.cells.ownedChildren_source 0 member
  rw [identity, Nat.zero_add]
  exact lookup

/-- Construct common refinements between the two retained compilations of the same original source.

Both input owners and their retained partitions remain in the comparison. The construction keeps the ordered
common-refinement witnesses. -/
@[expose] def Compiled.CompiledPartition.common {source : Source.PolynomialPath} (left right :
  Compiled.CompiledPartition source) :
    Common.CommonCells left.cells right.cells := left.cells.common right.cells

/-- Two cut requests for the exact same original polynomial path give equal integral samples.

Both retained compiled models read back to the original source sample, without identifying or replacing their separate
partitions. -/
theorem Compiled.polynomial_partition_independent (source : Source.PolynomialPath) (left right : Request.CutRequest
  source) :
    (Compiled.compilePartition source left).model.integralSample =
      (Compiled.compilePartition source right).model.integralSample := by
  rw [← Compiled.CompiledPartition.sample_model, ← Compiled.CompiledPartition.sample_model,
    Compiled.CompiledPartition.sample_source, Compiled.CompiledPartition.sample_source]

end Purelib.Integration.Polynomial.Gaussian.Partition
end
