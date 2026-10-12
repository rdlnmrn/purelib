module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Integration.Partition.Interval
import Purelib.Integration.Partition.Unit.Basic
public import Purelib.Integration.Partition.Unit.Common
public import Purelib.Integration.Polynomial.Gaussian.Partition.Child
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Segment.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Rat.Fraction.Arithmetic

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
open Purelib.Data.List
open Purelib.Integration.Partition
open Purelib.Integration.Polynomial.Gaussian

open Purelib.Integration.Polynomial.Gaussian.Segment.Basic (PolynomialSegment)
set_option genInjectivity false in
/-- A retained unit partition with cached exact polynomial children, ordered path model and summed sample.

Every cache remains linked to the original polynomial segment and retained partition by a defining equality; children
keep their exact restriction owners. -/
structure Segment.CompiledSegment (source : PolynomialSegment) where
  /-- The exact retained unit-interval partition. -/ partition : Partition.Unit.Normalized
  /-- The cached ordered child restrictions of the original polynomial segment. -/ children : List (Child source)
  /-- The children are exactly the canonical restrictions over the retained partition intervals. -/ children_eq :
    children = partition.intervals.map (Child.canonical source)
  /-- The cached ordered polynomial path model. -/ model : Path.Basic.PathModel
  /-- The model consists of the exact retained child models. -/ model_eq : model = Child.childModels children
  /-- The cached sum of the original retained child samples. -/ sample : Basic.Canonical
  /-- The sample equals the ordered sum of those exact retained children. -/ sample_eq : sample = Child.childSum
    children

constructive_injectivity Segment.CompiledSegment

/-- Compile the original polynomial segment over the supplied partition, computing and retaining its children once.

The original partition supplies the ordered interval list. Its child restrictions are cached once, and the model and
sample read back that exact cache. -/
@[expose] def Segment.CompiledSegment.ofPartition (source : PolynomialSegment) (partition : Partition.Unit.Normalized) :
  Segment.CompiledSegment source :=
  let children := partition.intervals.map (Child.canonical source)
  { partition := partition
    children := children
    children_eq := rfl
    model := Child.childModels children
    model_eq := rfl
    sample := Child.childSum children
    sample_eq := rfl }

/-- Normalize the requested rational cuts into a unit partition and compile the original segment over it.

The construction retains its supplied source and parameters. Cached data is computed once from those inputs and its
defining equalities retain that construction. -/
@[expose] def Segment.CompiledSegment.canonical (source : PolynomialSegment) (cuts : List Fraction.Rational) :
  Segment.CompiledSegment source :=
  Segment.CompiledSegment.ofPartition source (Partition.Unit.Normalized.ofRequest cuts)

/-- Every child retained in the compiled segment has a valid original parameter interval.

Membership in the cached child list identifies an interval in the same retained valid unit partition. -/
theorem Segment.CompiledSegment.children_valid {source : PolynomialSegment} (compiled : Segment.CompiledSegment source)
    (child : Child source) (member : child ∈ compiled.children) : child.interval.Valid := by
  rw [compiled.children_eq] at member
  obtain ⟨interval, inPartition, rfl⟩ := Map.mem_map.mp member
  exact compiled.partition.valid interval inPartition

/-- Reading the retained children's intervals recovers the exact original partition interval list.

Each canonical child retains its supplied interval. Reading those fields preserves the order and length of the cached
partition list. -/
theorem Segment.CompiledSegment.children_intervals {source : PolynomialSegment} (compiled : Segment.CompiledSegment
  source) :
    compiled.children.map Child.interval = compiled.partition.intervals := by
  rw [compiled.children_eq]
  have erase : ∀ intervals : List Partition.Interval,
      (intervals.map (Child.canonical source)).map Child.interval = intervals := by
    intro intervals
    induction intervals with
    | nil => rfl
    | cons head tail inductionHypothesis =>
        change head :: (tail.map (Child.canonical source)).map Child.interval = head :: tail
        rw [inductionHypothesis]
  exact erase compiled.partition.intervals

/-- The compiled sample equals the exact retained path model's integral sample.

The sample and model remain caches of the same retained compilation. Their defining equalities transport the exact
scalar readback. -/
theorem Segment.CompiledSegment.sample_model {source : PolynomialSegment} (compiled : Segment.CompiledSegment source) :
    compiled.sample = compiled.model.integralSample := by
  rw [compiled.sample_eq, compiled.model_eq, Child.childSum_eq_model]

/-- The compiled sample equals the original unsplit polynomial segment's integral sample.

The retained compilation follows the supplied source order. Its exact samples sum to the integral sample of that same
source. -/
theorem Segment.CompiledSegment.sample_source {source : PolynomialSegment} (compiled : Segment.CompiledSegment source) :
    compiled.sample = source.integralSample := by
  rw [compiled.sample_eq, compiled.children_eq, Child.childSum_chain source compiled.partition.chain]
  rfl

/-- The compiled exact polynomial path has zero aggregate allowance.

The retained model is assembled from exact child models. Its aggregate allowance uses their zero total allowance. -/
theorem Segment.CompiledSegment.allowance_zero {source : PolynomialSegment} (compiled : Segment.CompiledSegment source)
  :
    compiled.model.aggregateAllowance = 0 := by
  rw [compiled.model_eq, Child.childModels_allowance]

/-- Construct the common refinement of the two exact retained partitions of one original segment.

Both input owners and their retained partitions remain in the comparison. The construction keeps the ordered
common-refinement witnesses. -/
@[expose] def Segment.CompiledSegment.common {source : PolynomialSegment} (left right : Segment.CompiledSegment source)
  :
    Unit.Common.CommonRefinement left.partition right.partition :=
  Unit.Common.commonRefinement left.partition right.partition

/-- Two compiled partitions of the same original polynomial segment have identical cached samples.

Both cached samples read back to the integral sample of the same nominal source segment. -/
theorem Segment.CompiledSegment.partition_independent {source : PolynomialSegment} (left right : Segment.CompiledSegment
  source) :
    left.sample = right.sample := left.sample_source.trans right.sample_source.symm

end Purelib.Integration.Polynomial.Gaussian.Partition
end
