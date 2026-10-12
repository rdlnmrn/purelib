module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Integration.Path.IncrementArea
public import Purelib.Topology.Mesh.RetracingWords
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes

/-! Retained canonical word observations beneath single, paired and conjugate
magnitude producers. The observation preserves its actual value owner, ordered
edges, one acquired increment list and its executable summary. Payment and
readback consume the retained fields. This object does not claim that an
arbitrary word is a paired walk, physical boundary or resplit inclusion. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public section

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Topology.Mesh

open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes (OrientedEdge triangleEdgeOccurrences)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation orderedRoute_value)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Topology.Mesh.RetracingWords (wordArea sum_map_eq_wordValue)
open Purelib.Integration.Path.IncrementArea (Summary)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_zero normSq_neg)
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct)

variable {genus : Nat} {curve : HyperellipticCurve genus} {owner : OwnedPuncturedMesh
  curve}

/-- An ordered list of oriented edges on the original retained mesh vertex set. -/
@[reducible, expose] def Word (owner : OwnedPuncturedMesh curve) := List (OrientedEdge owner.vertices.count)
/-- The canonical increment list read from the actual original values and ordered edge word. -/
@[reducible, expose] def Entries (values : Values owner) (word : Word owner) := word.map
  (CanonicalEdgeValues.edgeValuation owner.mesh values)
/-- Exact equality between the supplied and retained original magnitude certificates. -/
@[reducible, expose] def MagnitudeIdentity {values : Values owner} (supplied retained : EdgeMagnitude values) : Prop :=
  retained = supplied
/-- Exact equality with the canonical increments of the original retained word. -/
@[reducible, expose] def EntryIdentity (values : Values owner) (word : Word owner) (entries : List
  Data.Gaussian.Basic.Canonical) : Prop := entries = Entries values word
/-- Exact equality between the supplied original word and its retained edge list. -/
@[reducible, expose] def WordIdentity (word retained : Word owner) : Prop := retained = word
/-- The complete squared-count magnitude bound for the original finite edge word. -/
@[reducible, expose] def BoundSpecification (count : Nat) (magnitude : Fraction.Rational) : Fraction.Rational := (count
  : Fraction.Rational)^2 * (4 * magnitude)

/-- Canonical valuation is either the retained supported route increment or zero. The stronger original 4*bound remains
valid for every retained edge. -/
theorem edge_bounded {values : Values owner} (magnitude : EdgeMagnitude values)
    (edge : OrientedEdge owner.vertices.count) :
    Data.Gaussian.Norm.Basic.normSq
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh values edge) ≤ 4 *
      magnitude.bound := by
  have nonnegative : 0 ≤ 4 * magnitude.bound := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    magnitude.nonnegative
  have forward (edge : OrientedEdge owner.vertices.count) :
      Data.Gaussian.Norm.Basic.normSq (if supported : edge ∈ triangleEdgeOccurrences
        owner.mesh.triangulation.faces ∨
          edge.reverse ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces then
        (EdgeRoute.build owner.mesh edge supported).sourceEdge.increment values else 0) ≤
        4 * magnitude.bound := by
    split
    · exact magnitude.source_bounded _
    · exact Data.Gaussian.Norm.Basic.normSq_zero.trans_le nonnegative
  unfold CanonicalEdgeValues.edgeValuation
  split
  · exact forward edge
  · split
    · rw [Data.Gaussian.Norm.Basic.normSq_neg]
      exact forward edge.reverse
    · exact Data.Gaussian.Norm.Basic.normSq_zero.trans_le nonnegative

set_option genInjectivity false in
/-- The cached canonical increments and executable summary of an original ordered mesh word.

The exact original value owner, edge list and supplied magnitude certificate remain retained with the paid total bound.
-/
structure Observation (values : Values owner) (word : Word owner) (supplied : EdgeMagnitude values) where
  /-- The original magnitude certificate retained by the observation. -/ magnitude : EdgeMagnitude values
  /-- The retained magnitude certificate is exactly the supplied original certificate. -/ magnitude_eq :
    MagnitudeIdentity supplied magnitude
  /-- The actual retained original edge word in occurrence order. -/ edges : Word owner
  /-- The retained edges are exactly the supplied original word. -/ edges_eq : WordIdentity word edges
  /-- The acquired canonical increment list of the original retained word. -/ increments : List
    Data.Gaussian.Basic.Canonical
  /-- The increment cache equals the canonical readings of the exact original edge word. -/ increments_eq :
    EntryIdentity values word increments
  /-- The executable summary cached from the actual retained increment list. -/ summary : IncrementArea.Summary
    increments
  /-- The cached complete squared-count total bound. -/ bound : Fraction.Rational
  /-- The cached bound is the original word-length expression with the retained magnitude. -/ bound_eq : bound =
    BoundSpecification word.length magnitude.bound
  /-- The squared norm of the actual cached increment total is at most the retained bound. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq summary.total ≤ bound

constructive_injectivity Observation

/-- Acquire the ordered entries and their summary once, then retain their original stronger source-derived magnitude
certificate.

The original edge word supplies the canonical increment list and its cached summary. The retained magnitude and exact
word length certify the same complete squared-count bound. -/
@[expose] def realize {values : Values owner} (magnitude : EdgeMagnitude values) (word : Word owner) : Observation
  values word magnitude :=
  let increments := Entries values word
  let summary := IncrementArea.Summary.build increments
  let bound := BoundSpecification word.length magnitude.bound
  have bounded : Data.Gaussian.Norm.Basic.normSq summary.total ≤ bound := by
    rw [summary.total_eq]
    change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum increments) ≤
      (word.length : Fraction.Rational)^2 * (4 * magnitude.bound)
    apply IncrementArea.sum_bound_of_length
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitude.nonnegative) ?_ ?_
    · intro value member
      obtain ⟨edge, _, equal⟩ := Map.mem_map.mp member
      rw [← equal]
      exact edge_bounded magnitude edge
    · exact (Map.length_map _ _).le
  ⟨magnitude, rfl, word, rfl, increments, rfl, summary, bound, rfl, bounded⟩

namespace Observation

variable {values : Values owner} {word : Word owner} {magnitude : EdgeMagnitude values}

/-- The total from the already retained original increment summary. -/
@[expose] def total (observation : Observation values word magnitude) : Gaussian := observation.summary.total
/-- The area from the already retained original increment summary. -/
@[expose] def area (observation : Observation values word magnitude) : Gaussian := observation.summary.area

/-- The cached total equals the canonical valuation sum on the exact original edge word. -/
theorem total_readback (observation : Observation values word magnitude) :
    observation.total = SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh values) word := by
  rw [total, observation.summary.total_eq, observation.increments_eq, Entries, RetracingWords.sum_map_eq_wordValue]

/-- The cached area equals the canonical polygon area on the exact original edge word. -/
theorem area_readback (observation : Observation values word magnitude) :
    observation.area = RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation owner.mesh values) word := by
  rw [area, observation.summary.area_eq, observation.increments_eq]
  rfl

/-- The retained bound reads the original word length and originally supplied magnitude certificate. -/
theorem bound_readback (observation : Observation values word magnitude) :
    observation.bound = BoundSpecification word.length magnitude.bound := by
  rw [observation.bound_eq, observation.magnitude_eq]

/-- A paid retained bound controls the squared norm of the actual cached word total. -/
theorem pay (observation : Observation values word magnitude) {target : Fraction.Rational}
    (paid : observation.bound ≤ target) : Data.Gaussian.Norm.Basic.normSq observation.total ≤ target :=
      observation.bounded.trans paid

end Observation
end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations
