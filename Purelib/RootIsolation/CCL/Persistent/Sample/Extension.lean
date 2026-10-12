module
import Purelib.Data.CCL.Encoding.Parser.Inverse
import Purelib.Data.CCL.Encoding.Parser.Next
import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Geometry.CCL.Parser.Formula.Advance
import Purelib.Geometry.CCL.Parser.Formula.Input
import Purelib.Geometry.CCL.Parser.Formula.State
import Purelib.Geometry.Projective.Hermitian.Formula.Pullback
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
public import Purelib.RootIsolation.CCL.Persistent.Sample.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Hermitian.Formula.Basic
import Purelib.Geometry.Projective.Homography.Basic

public section

open Purelib

open Purelib.Geometry.Rational

open Purelib.RootIsolation

/-!
# Strict-sign steps for the persistent CCL controller

This module implements the part of the one-bit controller where every atom
of the selected child formula is separated from its Hermitian boundary on the
current box.  The same displayed input remains a compatible sample after the
bit is appended, and formula stability proves this uniformly for every later
supplied winding-one refinement.

Boundary equality is intentionally not guessed here.  `stableNext?` returns
`none` when an atom margin is unresolved; the curve-count/equality-owner layer
must handle precisely those cases.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Sample.Extension.CompatibleSample

section CompatibleSample

/-- The input-coordinate formula at a compatible sample is the same decision
as the affine formula at its explicitly computed inverse tail. -/
theorem inputAdvanceFormula_iff_nextTail
    {word : Data.List.BinaryPrefix.Basic.SourcePersistentStrictWordAlias} {box : Box}
    (sample : CCL.Persistent.Sample.Basic.CompatibleSample word box)
    (bit : Bool) :
    (Geometry.CCL.Parser.Formula.inputAdvanceFormula
        (Data.CCL.Encoding.Parser.State.parse word) bit).Holds sample.point ↔
      (Geometry.CCL.Parser.Formula.advanceFormula
        (Data.CCL.Encoding.Parser.State.parse word) bit).Holds sample.nextDecision.tail := by
  let next := sample.nextDecision
  exact
    (Geometry.CCL.Parser.Formula.inputAdvanceFormula_canStep_iff
      (Data.CCL.Encoding.Parser.State.parse word) sample.point next.tail (Data.CCL.Encoding.Parser.State.parse_det_ne
        word)
      next.represents bit).trans
    ((Data.CCL.Encoding.Parser.Next.canStep_iff_canAdvanceAt
      (Data.CCL.Encoding.Parser.State.parse word) sample.point next.tail (Data.CCL.Encoding.Parser.State.parse_det_ne
        word)
      next.represents bit).trans
    (Geometry.CCL.Parser.Formula.advanceFormula_iff
      (Data.CCL.Encoding.Parser.State.parse word) bit next.tail).symm)

/-- A full local child decision supplies the history-free input-coordinate
obligation used by the persistent controller. -/
theorem
  inputIncrementalAdvanceFormula_holds_of_advance
    {word : Data.List.BinaryPrefix.Basic.SourcePersistentStrictWordAlias} {box : Box}
    (sample : CCL.Persistent.Sample.Basic.CompatibleSample word box)
    (bit : Bool)
    (advance : (Geometry.CCL.Parser.Formula.advanceFormula
      (Data.CCL.Encoding.Parser.State.parse word) bit).Holds sample.nextDecision.tail) :
    (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula
      (Data.CCL.Encoding.Parser.State.parse word) bit).Holds sample.point := by
  let next := sample.nextDecision
  apply (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula_canStep_iff
    (Data.CCL.Encoding.Parser.State.parse word) sample.point next.tail
    (Data.CCL.Encoding.Parser.State.parse_det_ne word) next.represents bit).mpr
  apply (Data.CCL.Encoding.Parser.Next.canStep_iff_canAdvanceAt
    (Data.CCL.Encoding.Parser.State.parse word) sample.point next.tail
    (Data.CCL.Encoding.Parser.State.parse_det_ne word) next.represents bit).mpr
  exact (Geometry.CCL.Parser.Formula.advanceFormula_iff
    (Data.CCL.Encoding.Parser.State.parse word) bit next.tail).mp advance

/-- Preserve the displayed rational input while appending a semantically
admissible bit.  Only the propositional representation witness changes. -/
@[expose] def extend
    {word : Data.List.BinaryPrefix.Basic.SourcePersistentStrictWordAlias} {box : Box}
    (sample : CCL.Persistent.Sample.Basic.CompatibleSample word box)
    (bit : Bool)
    (holds : (Geometry.CCL.Parser.Formula.inputAdvanceFormula
      (Data.CCL.Encoding.Parser.State.parse word) bit).Holds sample.point) :
    CCL.Persistent.Sample.Basic.CompatibleSample (word ++ [bit]) box := by
  let next := sample.nextDecision
  have possible : Data.CCL.Encoding.Parser.Semantics.Prefix.CanStep (Data.CCL.Encoding.Parser.State.parse word)
    sample.point bit :=
    (Geometry.CCL.Parser.Formula.inputAdvanceFormula_canStep_iff
      (Data.CCL.Encoding.Parser.State.parse word) sample.point next.tail (Data.CCL.Encoding.Parser.State.parse_det_ne
        word)
      next.represents bit).1 holds
  exact
    { point := sample.point
      inside := sample.inside
      nonzero := sample.nonzero
      represented := by
        rcases possible with ⟨tail, represented⟩
        exact ⟨tail, by
          simpa only [Data.CCL.Encoding.Parser.State.parse_append_singleton, -eq_self, -iff_self] using represented⟩ }

/-- Append a bit from only its history-free formula.  Current representability
supplies all retained constraints before the incremental predicate is folded
back into the complete child formula. -/
@[expose] def extendIncremental
    {word : Data.List.BinaryPrefix.Basic.SourcePersistentStrictWordAlias} {box : Box}
    (sample : CCL.Persistent.Sample.Basic.CompatibleSample word box)
    (bit : Bool)
    (holds : (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula
      (Data.CCL.Encoding.Parser.State.parse word) bit).Holds sample.point) :
    CCL.Persistent.Sample.Basic.CompatibleSample (word ++ [bit]) box := by
  let next := sample.nextDecision
  have possible : Data.CCL.Encoding.Parser.Semantics.Prefix.CanStep (Data.CCL.Encoding.Parser.State.parse word)
    sample.point bit :=
    (Geometry.CCL.Parser.Formula.inputIncrementalAdvanceFormula_canStep_iff
      (Data.CCL.Encoding.Parser.State.parse word) sample.point next.tail
      (Data.CCL.Encoding.Parser.State.parse_det_ne word) next.represents bit).mp holds
  exact
    { point := sample.point
      inside := sample.inside
      nonzero := sample.nonzero
      represented := by
        rcases possible with ⟨tail, represented⟩
        exact ⟨tail, by
          simpa only [Data.CCL.Encoding.Parser.State.parse_append_singleton, -eq_self, -iff_self] using represented⟩ }

end CompatibleSample

end Purelib.RootIsolation.CCL.Persistent.Sample.Extension.CompatibleSample

end
