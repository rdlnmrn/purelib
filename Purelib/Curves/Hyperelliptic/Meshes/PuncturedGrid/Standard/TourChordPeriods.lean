module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
public import Purelib.Topology.Surface.Chord.Spanning
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib.Topology.Surface

open Purelib.Data.Rat

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

open Purelib

public section

/-!
# Actual standard-tour chains and their shared chord-period programs

Both A/B rows use the exact retained chord bank underlying the prepared
component programs. The resulting original-tour identities preserve the
corrected physical row and signed face chain. Component approximation
errors are charged with the actual cached integer weights.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Chord.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates (OnChords onChords)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Meshes.FramedPuncturedGrid curve (Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {index : Fin genus} {pair :
    TourFaces.StandardTours.Pair lifted index}
  {coordinates : TourCoordinates.BoundaryCoordinates pair} {integral :
    Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {source : Differentials.Basic.Differential genus} {differential : Fin genus}

set_option genInjectivity false in
/-- The two original tour chains expressed through one retained chord-period bank.

Keep each chain's physical correction and original integer weights with its component approximation. -/
structure ChordPeriods (span : TourSpanning.Spanning coordinates integral)
  (prepared : Cut.CyclePrograms.CutChordPrograms lifted source)
    (components : Cut.ChainPeriods.ComponentSamples prepared.programs differential)
      where
  /-- The actual A-chain geometry on the retained original chord routes. -/ aGeometry :
    OnChords span.a prepared.routes
  /-- The actual B-chain geometry on the retained original chord routes. -/ bGeometry :
    OnChords span.b prepared.routes
  /-- The A-period combination using the original shared components and actual integer coefficients. -/ a :
    Cut.ChainPeriods.ChainPeriod components span.a.coefficients
  /-- The B-period combination using the original shared components and actual integer coefficients. -/ b :
    Cut.ChainPeriods.ChainPeriod components span.b.coefficients

constructive_injectivity ChordPeriods

/-- Reuse the one prepared component bank and synchronized streams. Only
the two integer combinations and their physical corrections are new data. -/
@[expose] def chordPeriods (span : TourSpanning.Spanning coordinates
  integral) (prepared : Cut.CyclePrograms.CutChordPrograms lifted source)
    (components : Cut.ChainPeriods.ComponentSamples prepared.programs differential) :
      ChordPeriods span prepared components :=
  ⟨onChords span.a prepared.routes,
    Chord.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates.onChords span.b prepared.routes,
    Cut.ChainPeriods.ChainPeriod.build components span.a.coefficients,
      Cut.ChainPeriods.ChainPeriod.build components span.b.coefficients⟩

namespace ChordPeriods

variable {span : TourSpanning.Spanning coordinates integral} {prepared :
  Cut.CyclePrograms.CutChordPrograms lifted source}
  {components : Cut.ChainPeriods.ComponentSamples prepared.programs differential}

/-- The retained A-period chain equals its original chord-geometry chain. -/
theorem a_chain (periods : ChordPeriods span prepared
  components) : periods.a.chain = periods.aGeometry.chain := rfl
/-- The retained B-period chain equals its original chord-geometry chain. -/
theorem b_chain (periods : ChordPeriods span prepared
  components) : periods.b.chain = periods.bGeometry.chain := rfl

/-- The original A-tour value is its chord-chain value plus the retained physical and signed-face corrections. -/
theorem a_value (periods : ChordPeriods span prepared
  components) (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    Sewing.SewingRetraction.wordValue value pair.aFaces.geometry.indexed =
      Chord.Spanning.CutCycleChain.edgeValue periods.a.chain value +
      Boundary.BoundaryCoordinates.WordCoordinates.combine periods.aGeometry.physical
        (fun column => value (Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) +
      Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value
        coordinates.routes.a.correction := by
  rw [coordinates.a_value value anti, periods.aGeometry.value_eq value anti]
  rfl

/-- The original B-tour value is its chord-chain value plus the retained physical and signed-face corrections. -/
theorem b_value (periods : ChordPeriods span prepared
  components) (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    Sewing.SewingRetraction.wordValue value pair.bFaces.geometry.indexed =
      Chord.Spanning.CutCycleChain.edgeValue periods.b.chain value +
      Boundary.BoundaryCoordinates.WordCoordinates.combine periods.bGeometry.physical
        (fun column => value (Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) +
      Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value
        coordinates.routes.b.correction := by
  rw [coordinates.b_value value anti, periods.bGeometry.value_eq value anti]
  rfl

/-- The cached A sample is the finite integer-weighted combination of the original component program readings. -/
theorem a_sample (periods : ChordPeriods span prepared
  components) (stage : Nat) :
    periods.a.approximation.sample stage = FiniteSum.Fin.sumFin (fun index =>
      (span.a.coefficients index : Gaussian.Basic.Canonical) *
        (((prepared.programs.programs index).program differential).integral.model stage).integralSample) :=
  periods.a.sample_eq_programs stage

/-- The cached B sample is the finite integer-weighted combination of the original component program readings. -/
theorem b_sample (periods : ChordPeriods span prepared
  components) (stage : Nat) :
    periods.b.approximation.sample stage = FiniteSum.Fin.sumFin (fun index =>
      (span.b.coefficients index : Gaussian.Basic.Canonical) *
        (((prepared.programs.programs index).program differential).integral.model stage).integralSample) :=
  periods.b.sample_eq_programs stage

/-- Transport a component estimate through the actual A-chain identity.
The physical and face terms are subtracted explicitly, not declared zero. -/
theorem a_comparison_bound (periods : ChordPeriods span
  prepared components)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge)
    (stage : Nat) (bounds : Fin lifted.cutBoundaryWord.alphabet.count → Periods.WeightedPeriods.Coordinate)
    (bounded : ∀ index, Gaussian.Norm.Basic.normSq (Sewing.SewingRetraction.wordValue value
      (prepared.programs.programs index).cycle.path.surfaceEdges -
      (((prepared.programs.programs index).program differential).integral.model stage).integralSample) ≤ bounds index) :
    Gaussian.Norm.Basic.normSq ((Sewing.SewingRetraction.wordValue value
      pair.aFaces.geometry.indexed -
      Boundary.BoundaryCoordinates.WordCoordinates.combine periods.aGeometry.physical
        (fun column => value (Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) -
      Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value
        coordinates.routes.a.correction) - periods.a.approximation.sample stage) ≤
      periods.a.coefficients.charge bounds := by
  have comparison := periods.a.comparison_bound
    (fun index => Sewing.SewingRetraction.wordValue value (prepared.routes.cycles
      index).path.surfaceEdges) stage bounds (fun index => by
      rw [← prepared.programs.cycles_eq]
      exact bounded index)
  rw [periods.a.coefficients.combine_eq] at comparison
  change Gaussian.Norm.Basic.normSq (Chord.Spanning.CutCycleChain.edgeValue periods.a.chain
    value - periods.a.approximation.sample stage) ≤ _ at comparison
  rw [periods.a_value value anti]
  have cancellation (chain physical faces : Gaussian.Basic.Canonical) : chain + physical + faces - physical - faces =
    chain := by ring1
  rw [cancellation]
  exact comparison

/-- The original B-tour comparison is bounded by its retained weighted component errors after subtracting the actual
physical and face corrections. -/
theorem b_comparison_bound (periods : ChordPeriods span
  prepared components)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge)
    (stage : Nat) (bounds : Fin lifted.cutBoundaryWord.alphabet.count → Periods.WeightedPeriods.Coordinate)
    (bounded : ∀ index, Gaussian.Norm.Basic.normSq (Sewing.SewingRetraction.wordValue value
      (prepared.programs.programs index).cycle.path.surfaceEdges -
      (((prepared.programs.programs index).program differential).integral.model stage).integralSample) ≤ bounds index) :
    Gaussian.Norm.Basic.normSq ((Sewing.SewingRetraction.wordValue value
      pair.bFaces.geometry.indexed -
      Boundary.BoundaryCoordinates.WordCoordinates.combine periods.bGeometry.physical
        (fun column => value (Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) -
      Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value
        coordinates.routes.b.correction) - periods.b.approximation.sample stage) ≤
      periods.b.coefficients.charge bounds := by
  have comparison := periods.b.comparison_bound
    (fun index => Sewing.SewingRetraction.wordValue value (prepared.routes.cycles
      index).path.surfaceEdges) stage bounds (fun index => by
      rw [← prepared.programs.cycles_eq]
      exact bounded index)
  rw [periods.b.coefficients.combine_eq] at comparison
  change Gaussian.Norm.Basic.normSq (Chord.Spanning.CutCycleChain.edgeValue periods.b.chain
    value - periods.b.approximation.sample stage) ≤ _ at comparison
  rw [periods.b_value value anti]
  have cancellation (chain physical faces : Gaussian.Basic.Canonical) : chain + physical + faces - physical - faces =
    chain := by ring1
  rw [cancellation]
  exact comparison

end ChordPeriods
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods
