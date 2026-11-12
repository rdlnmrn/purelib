module
import Purelib.Examples.Integration.Polynomial.Gaussian.Partition.WorkedExamples
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
import Purelib.Integration.Polynomial.Gaussian.Segment.Basic
import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Integration.Partition.Unit.Basic
import Purelib.Examples.Integration.Polynomial.Gaussian.Transport.WorkedExamples
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.CCL.Program
import Purelib.Integration.Partition.Interval
import Purelib.Integration.Partition.Ownership
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic

/-! Regression checks for the retained integration polynomial gaussian partition contracts. -/

namespace TestPurelib.Integration.Polynomial.Gaussian.Partition

open Purelib.Examples.Integration.Polynomial.Gaussian.Partition.WorkedExamples

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

/-- The four common intervals retain their original left and right parent indices. -/
theorem common_parent_indices :
    thirdsHalves.entries.map (fun entry =>
      (entry.leftOwner.index, entry.rightOwner.index)) =
      [(0, 0), (1, 0), (1, 1), (2, 1)] := by decide

/-- The compiled children retain source occurrence indices zero, zero and one. -/
theorem repeated_ownership :
    repeatedCompiled.ownedChildren.map OwnedChild.sourceIndex = [0, 0, 1] := by decide

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

end TestPurelib.Integration.Polynomial.Gaussian.Partition
