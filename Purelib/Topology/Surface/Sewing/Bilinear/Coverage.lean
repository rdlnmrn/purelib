module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.Bilinear.Errors
import Purelib.Topology.Surface.Sewing.Bilinear.Requests
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Topology.Surface.Sewing.Bilinear.Refinement
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.List

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.Bilinear

open Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

public section

/-! Exact source-sum readback through the complete cut polygon. -/

namespace Purelib.Topology.Surface.Sewing.Bilinear.Coverage

open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate FaceTrace)
open Purelib.Topology.Surface.Sewing.Bilinear.Errors (traceAt)
open Purelib.Topology.Surface.Sewing.Bilinear.Requests (AreaRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (ContactBank)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRefinement (ContactRates)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear

open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint triangleWedgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

/-- The bounded finite sum over a retained list equals its mapped Gaussian list sum. -/
private theorem indexed_sum {Item : Type} (entries : List Item) (count : Nat)
    (lengthEq : entries.length = count) (value : Item → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun index : Fin count => value (entries[index.val]'(by rw [lengthEq]; exact index.isLt))) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map value) := by
  cases lengthEq
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      exact congrArg (value head + ·) ih

/-- Reordering the original list preserves the Gaussian sum of a fixed reading. -/
private theorem sum_permutation {Item : Type} (value : Item → Gaussian.Basic.Canonical) {first last : List Item}
    (order : List.Perm first last) : Data.Gaussian.Norm.Sum.Basic.gaussianSum (first.map value) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (last.map value) := by
  induction order with
  | nil => rfl
  | cons head order ih => exact congrArg (value head + ·) ih
  | swap first last tail => change value _ + (value _ + _) = value _ + (value _ + _); ring1
  | trans first last ihFirst ihLast => exact ihFirst.trans ihLast

/-- Summing the list of finite function values agrees with the original finite-index sum. -/
private theorem sum_ofFn {count : Nat} (value : Fin count → Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn value) = FiniteSum.Fin.sumFin value := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [OfFn.Basic.ofFn_succ, FiniteSum.Fin.sumFin_succ]
      exact congrArg (value 0 + ·) (ih (fun index => value index.succ))

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {forest : SewingForest faces}

/-- Exact polygon coverage reads each original face once in the retained source sum. -/
theorem source_sum (polygon : SewingForest.SinglePolygon forest) {localValues : Fin faceCount →
  PrimitiveSewing.PrimitiveValues 3}
    (surface : SewnPrimitiveSamples.CachedSample polygon.patch localValues) (value : Fin faceCount →
      Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun position => value (Errors.traceAt surface position).source) = FiniteSum.Fin.sumFin value
      := by
  have readback := indexed_sum surface.faces.entries polygon.patch.cut.triangles.length
    (FaceBank.entries_length surface.faces) (fun trace => value trace.source)
  change FiniteSum.Fin.sumFin (fun position => value (Errors.traceAt surface position).source) = _ at readback
  have mapped : surface.faces.entries.map (fun trace => value trace.source) =
      (surface.faces.entries.map FaceTrace.source).map value := (Purelib.Data.List.Map.map_map value FaceTrace.source
        surface.faces.entries).symm
  rw [mapped, surface.faces.sources_eq] at readback
  apply readback.trans
  apply (sum_permutation value polygon.coverage).trans
  rw [OfFn.Basic.map_ofFn]
  exact sum_ofFn value

/-- The shared bilinear refinement bounds error against the complete original face-area sum.

Cached source coverage transfers the indexed cut-triangle estimate without rebuilding either sewn sample. -/
theorem AreaRequest.Refinement.accurate_sources (polygon : SewingForest.SinglePolygon forest)
    {magnitude target : SewnPrimitiveFaces.Coordinate} {request : Requests.AreaRequest polygon.patch magnitude target}
    {contacts : SewnPrimitiveContacts.ContactBank polygon.patch.assembly}
    {leftFamily rightFamily : Nat → Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    {leftRates : SewnPrimitiveRefinement.ContactRates contacts leftFamily} {rightRates :
      SewnPrimitiveRefinement.ContactRates contacts rightFamily} {floor : Nat}
    (refinement : Refinement request leftRates rightRates floor) {stage : Nat}
    (later : refinement.index ≤ stage) {leftLocal rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    {left : SewnPrimitiveSamples.CachedSample polygon.patch leftLocal} {right : SewnPrimitiveSamples.CachedSample
      polygon.patch rightLocal}
    (sample : Samples left right)
    (leftReadback : ∀ source, leftLocal source = leftFamily stage source)
    (rightReadback : ∀ source, rightLocal source = rightFamily stage source)
    (bounded : ∀ source (index : Fin 3),
      (PrimitivePoint.Bounded (⟨leftLocal source index - leftLocal source 0,
        rightLocal source index - rightLocal source 0⟩ : Purelib.Topology.Polygon.Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (sample.boundaryArea - FiniteSum.Fin.sumFin (fun source => Stokes.triangleWedgeArea
      ⟨leftLocal source 0, rightLocal source 0⟩
      ⟨leftLocal source 1, rightLocal source 1⟩
      ⟨leftLocal source 2, rightLocal source 2⟩)) < target := by
  have estimate := refinement.accurate later sample leftReadback rightReadback
    (fun position => bounded (Errors.traceAt left position).source)
  have equal := source_sum polygon left (fun source => Stokes.triangleWedgeArea
    ⟨leftLocal source 0, rightLocal source 0⟩
    ⟨leftLocal source 1, rightLocal source 1⟩
    ⟨leftLocal source 2, rightLocal source 2⟩)
  rw [equal] at estimate
  exact estimate

end Purelib.Topology.Surface.Sewing.Bilinear.Coverage
