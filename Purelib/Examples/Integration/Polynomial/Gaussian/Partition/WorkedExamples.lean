module
import Purelib.Integration.Polynomial.Gaussian.Partition.Source
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Partition.Unit.Common
import Purelib.Integration.Partition.Unit.Normalize
import Purelib.Integration.Polynomial.Gaussian.Partition.Compiled
import Purelib.Integration.Polynomial.Gaussian.Partition.Ownership
import Purelib.Integration.Polynomial.Gaussian.Partition.Request
import Purelib.Integration.Polynomial.Gaussian.Partition.Segment
import Purelib.Polynomial.Ascending.Gaussian.Basic
public import Purelib.Integration.Polynomial.Gaussian.Segment.Basic
public import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Integration.Partition.Unit.Basic
public import Purelib.Examples.Integration.Polynomial.Gaussian.Transport.WorkedExamples
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.CCL.Program
import Purelib.Integration.Partition.Interval
import Purelib.Integration.Partition.Ownership
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic

@[expose] public section

/-!
# Generated polynomial partition regressions

All data are small; arithmetic examples use kernel decision at ordinary Lean
limits.  The symbolic results use the generic transport and partition proofs,
not a normalization of large concrete coefficient banks.
-/

namespace Purelib.Examples.Integration.Polynomial.Gaussian.Partition.WorkedExamples

open Purelib.Approximation.Gaussian
open Purelib.CCL.Progressive
open Purelib.Data
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Partition
open Purelib.Integration.Polynomial.Gaussian.Partition
open Purelib.Integration.Polynomial.Gaussian.Partition.Compiled (CompiledPartition)
open Purelib.Integration.Polynomial.Gaussian.Partition.Ownership (OwnedChild)
open Purelib.Integration.Polynomial.Gaussian.Partition.Request (CutRequest CutError)
open Purelib.Integration.Polynomial.Gaussian.Partition.Segment (CompiledSegment)
open Purelib.Integration.Polynomial.Gaussian.Partition.Source (PolynomialPath)
open Purelib.Integration.Polynomial.Gaussian.Segment.Basic (PolynomialSegment)
open Purelib.Polynomial.Ascending.Gaussian (CoefficientPolynomial)
open Purelib.Examples.Integration.Polynomial.Gaussian

/-- The displayed duplicate and out-of-range cuts normalize to the two interior third points. -/
theorem cuts_normalized :
    Unit.Normalize.normalize [2 / 3, -1, 1 / 3, 2 / 3, 1, 0, 2] = [1 / 3, 2 / 3] := by decide

/-- The third-point request partitions the unit interval into its three consecutive thirds. -/
theorem thirds_cover :
    (Unit.Normalized.ofRequest [2 / 3, 1 / 3]).intervals =
      [⟨0, 1 / 3⟩, ⟨1 / 3, 2 / 3⟩, ⟨2 / 3, 1⟩] := by decide

/-- The common refinement of the thirds partition and the halves partition. -/
def thirdsHalves :
  Unit.Common.CommonRefinement (Unit.Normalized.ofRequest [1 / 3, 2 / 3])
    (Unit.Normalized.ofRequest [1 / 2]) :=
  Unit.Common.commonRefinement _ _

/-- The common refinement has the four displayed consecutive intervals. -/
theorem common_intervals :
  thirdsHalves.partition.intervals =
    [⟨0, 1 / 3⟩, ⟨1 / 3, 1 / 2⟩, ⟨1 / 2, 2 / 3⟩, ⟨2 / 3, 1⟩] := by decide

/-- The four common intervals retain their original left and right parent indices. -/
theorem common_parent_indices :
    thirdsHalves.entries.map (fun entry =>
      (entry.leftOwner.index, entry.rightOwner.index)) =
      [(0, 0), (1, 0), (1, 1), (2, 1)] := by decide

/-- The quadratic Gaussian segment from `1 + i` to `-1 + 2i`. -/
def curvedSegment : PolynomialSegment :=
  ⟨⟨1, 1⟩, ⟨-1, 2⟩, Transport.WorkedExamples.quadratic⟩

/-- The curved segment has exact integral sample `-11/2 - i`. -/
theorem curvedSegment_integral :
  curvedSegment.integralSample = ⟨-11 / 2, -1⟩ := by decide

/-- Every finite cut partition of the curved segment preserves its exact integral sample. -/
theorem curved_partition_sample (cuts : List Rational) :
    (CompiledSegment.canonical curvedSegment cuts).sample = ⟨-11 / 2, -1⟩ := by
  rw [CompiledSegment.sample_source, curvedSegment_integral]

/-- The polynomial path containing two occurrences of the same curved segment. -/
def repeatedPath : PolynomialPath := [curvedSegment, curvedSegment]

/-- The request bisecting the first occurrence and retaining the second occurrence whole. -/
def repeatedRequest : CutRequest repeatedPath := .cons [1 / 2] (.cons [] .nil)

/-- The compiled partition of the repeated path with its original typed cut request. -/
def repeatedCompiled : CompiledPartition repeatedPath :=
  Compiled.compilePartition repeatedPath repeatedRequest

/-- The compiled children retain source occurrence indices zero, zero and one. -/
theorem repeated_ownership :
    repeatedCompiled.ownedChildren.map OwnedChild.sourceIndex = [0, 0, 1] := by decide

/-- The repeated path's compiled integral sample is `-11 - 2i`. -/
theorem repeated_integral :
  repeatedCompiled.sample = ⟨-11, -2⟩ := by
  rw [CompiledPartition.sample_source]
  decide

/-- A serialized request missing its second source row is rejected at that original source cell. -/
theorem missing_row_rejected :
    CutRequest.decode 0
      repeatedPath [⟨0, [1 / 2]⟩] =
      .error (.afterCell 0 curvedSegment
        [curvedSegment] ⟨0, [1 / 2]⟩ [] rfl
        (.missingCell 1 curvedSegment [])) := rfl

/-- A duplicate source index is rejected when the second occurrence requires index one. -/
theorem duplicate_owner_rejected :
    CutRequest.decode 0
      repeatedPath [⟨0, []⟩, ⟨0, []⟩] =
      .error (.afterCell 0 curvedSegment
        [curvedSegment] ⟨0, []⟩ [⟨0, []⟩] rfl
        (.wrongCell 1 curvedSegment [] ⟨0, []⟩ [] (by decide)))
          := rfl

/-- A nonempty serialized request for an empty source path is rejected as an extra row. -/
theorem extra_row_rejected :
    CutRequest.decode 0 [] [⟨0, []⟩] = .error (.extraCell 0 ⟨0, []⟩ []) := rfl

/-- The displayed incomplete row list is not the serialization of any complete typed request for the repeated path. -/
theorem missing_row_not_a_complete_request (request : CutRequest repeatedPath) :
    [⟨0, [1 / 2]⟩] ≠ CutRequest.serialize 0 request :=
  (CutError.afterCell 0
    curvedSegment
    [curvedSegment] ⟨0, [1 / 2]⟩ [] rfl
    (.missingCell 1 curvedSegment [])).rejects_serialization
      request

/-- A row before the required initial source offset is rejected with the exact wrong-cell witness. -/
theorem out_of_order_offset_rejected :
    CutRequest.decode 7
      [curvedSegment] [⟨6, []⟩] =
      .error (.wrongCell 7 curvedSegment [] ⟨6, []⟩ [] (by
        decide)) := rfl

/-- The original typed repeated-path request survives serialization and decoding unchanged. -/
theorem serialized_request_roundtrip :
    CutRequest.decode 0
      repeatedPath
      (CutRequest.serialize 0
      repeatedRequest) = .ok
      repeatedRequest :=
  CutRequest.decode_serialize 0
    repeatedRequest

/-- The empty compiled path has zero sample. -/
theorem empty_path_sample :
  (Compiled.compilePartition [] .nil).sample = 0 := rfl

/-- A segment with equal endpoints has zero sample under every finite cut request. -/
theorem degenerate_segment_sample
  (point : Gaussian.Basic.Canonical)
    (polynomial : CoefficientPolynomial) (cuts : List Rational) :
    (CompiledSegment.canonical ⟨point, point, polynomial⟩ cuts).sample = 0 := by
  rw [CompiledSegment.sample_source]
  change (point - point) * _ = 0
  rw [Gaussian.Basic.sub_self, Gaussian.Basic.zero_mul]

/-- Reversing the curved segment negates its partition sample. -/
theorem reversed_partition_sample (cuts : List Rational) :
    (CompiledSegment.canonical curvedSegment.reversed cuts).sample = -curvedSegment.integralSample := by
  rw [CompiledSegment.sample_source,
    PolynomialSegment.reversed_integralSample]

/-- The policy alternating the retained fixed request with a uniform cut schedule. -/
def alternatingPolicy : IntegrationPrograms.PartitionPolicy repeatedPath :=
  .alternating (.fixed repeatedRequest) (.uniform 2 1)

/-- The fixed and alternating policies produce equivalent named integration outputs for the same original path. -/
def different_policy_equivalence :
  Equivalence.NamedEquivalent
    (IntegrationPrograms.polynomialProgram repeatedPath (.fixed repeatedRequest)).output.name
    (IntegrationPrograms.polynomialProgram repeatedPath alternatingPolicy).output.name :=
  IntegrationPrograms.polynomial_outputs_equivalent repeatedPath _ _

end Purelib.Examples.Integration.Polynomial.Gaussian.Partition.WorkedExamples

end
