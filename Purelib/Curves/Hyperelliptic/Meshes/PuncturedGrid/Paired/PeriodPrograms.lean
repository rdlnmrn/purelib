module
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-!
# Prepared period families for the ordered, corrected branch walks

The whole finite A/B family shares one lifted grid, one ordered branch bank,
and one materialized preparation per row. The cached face assignments read
the very parents used by those period programs. The complete area identity
therefore applies to this family's actual geometric words, including its
physical hole, exterior and regular-face contributions.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}

set_option genInjectivity false in
/-- Materialize both the operational preparation and its shared-mesh face
assignment. The dependent index retains the exact ordered A pair and B shear. -/
structure PeriodRow (paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered) (index : Fin
  genus) where
  /-- The original A-pair and corrected B-walk preparation for this exact ordered row. -/ prepared : (paired.row
    index).row.Prepared (Periods.PeriodMatrix.standardDifferential index)
  /-- The retained face assignments of the exact original prepared period parents. -/ faces : prepared.Faces

constructive_injectivity PeriodRow

namespace PeriodRow

/-- Materialize the original ordered row's period preparation and the exact face assignments of its retained parents. -/
@[expose] def build (paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered) (index : Fin
  genus) : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.PeriodRow paired index :=
  let prepared := (paired.row index).row.prepare (Periods.PeriodMatrix.standardDifferential index)
  ⟨prepared, prepared.faces⟩

end PeriodRow

set_option genInjectivity false in
/-- A cached finite family, with no preparation hidden in a differential
lookup. Every row uses its own standard differential as the source chart;
all other differential entries recast the same stored parents. -/
structure Prepared (paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered) where
  /-- The original dependent cache of prepared period rows and their face assignments. -/ rows :
    Data.Vector.DependentVector (fun index : Fin genus =>
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.PeriodRow paired index)

constructive_injectivity Prepared

/-- Prepare every original ordered A/B row once and retain the complete dependent finite family. -/
@[expose] def prepare (paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered) :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired :=
  ⟨Data.Vector.DependentVector.ofFn (Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.PeriodRow.build paired)⟩

namespace Prepared

variable {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} (prepared :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)

/-- Read the exact retained original prepared row at its finite index. -/
@[expose] def row (index : Fin genus) : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.PeriodRow paired index
  := prepared.rows.get index

/-- Read the original prepared A period of the retained row. -/
@[expose] def aWalk (index : Fin genus) := (prepared.row index).prepared.a.period

/-- Read the original corrected B period of the retained row. -/
@[expose] def bWalk (index : Fin genus) := (prepared.row index).prepared.b

/-- Read the paired finite refinement family from the exact original cached A and B periods. -/
@[expose] def cycles : Path.Gaussian.Lifted.Family.PairedCycleRefinements 2 genus where
  aCycle := fun index => (prepared.aWalk index).cycle
  bCycle := fun index => (prepared.bWalk index).cycle

/-- The numerical interface consumes the same retained rows as the area
formula below. This construction asserts no equality to the old raw tours. -/
@[expose] def periodData : Periods.PeriodMatrix.PeriodData curve where
  cycles := prepared.cycles
  aProgram := fun differential index => (prepared.aWalk index).program differential
  bProgram := fun differential index => (prepared.bWalk index).program differential

/-- The original A program model equals the standard differential model of its exact retained refinement state. -/
theorem aProgram_model (differential index : Fin genus) (stage : Nat) :
    ((prepared.periodData.aProgram differential index).integral.model stage) =
      ((prepared.aWalk index).state stage).state.model (Periods.PeriodMatrix.standardDifferential differential) := rfl

/-- The original B program model equals the standard differential model of its exact retained refinement state. -/
theorem bProgram_model (differential index : Fin genus) (stage : Nat) :
    ((prepared.periodData.bProgram differential index).integral.model stage) =
      ((prepared.bWalk index).state stage).state.model (Periods.PeriodMatrix.standardDifferential differential) := rfl

/-- A and B remain based at the actual common vertex at every pair of
independently selected refinement stages. -/
theorem states_base_eq (index : Fin genus) (aStage bStage : Nat) :
    ((prepared.aWalk index).state aStage).state.start = ((prepared.bWalk index).state bStage).state.start :=
  ((prepared.aWalk index).state_base aStage).trans ((prepared.bWalk index).state_base bStage).symm

/-- The retained prepared A period has the exact original ordered A closed walk. -/
theorem a_walk_eq (index : Fin genus) :
    (prepared.aWalk index).closed.walk = (paired.row index).row.a.closed.walk :=
  (prepared.row index).prepared.a.walk_eq

/-- The retained prepared B period has the exact original corrected B closed walk. -/
theorem b_walk_eq (index : Fin genus) :
    (prepared.bWalk index).closed.walk = (paired.row index).row.corrected.walk :=
  (prepared.row index).prepared.b_walk_eq

/-- Read the original indexed A word from the retained prepared face assignment. -/
@[expose] def aWord (index : Fin genus) : List (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count) :=
  (prepared.row index).faces.a.geometry.geometry.indexed

/-- Read the original indexed corrected B word from its retained face assignment. -/
@[expose] def bWord (index : Fin genus) : List (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count) :=
  (prepared.row index).faces.b.geometry.indexed

/-- The retained A face word equals the original ordered row's indexed A walk. -/
theorem aWord_eq (index : Fin genus) : prepared.aWord index = (paired.row index).row.a.closed.indexed :=
  (prepared.row index).faces.a.indexed_eq

/-- The retained B face word equals the original row's complete corrected indexed walk. -/
theorem bWord_eq (index : Fin genus) : prepared.bWord index = (paired.row index).row.corrected.indexed :=
  (prepared.row index).faces.b_indexed

/-- Sum the actual boundary-ribbon areas of the retained A and corrected B word values over all original rows. -/
@[expose] def pairing (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
  Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun index : Fin genus => Path.BoundaryRibbon.area
    (Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.aWord index))
    (Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.bWord index)))

/-- The cached family's pairing equals the exact original ordered corrected-row area. -/
theorem pairing_eq (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    prepared.pairing value = paired.rows.correctedArea value := by
  rw [paired.correctedArea_sum]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [prepared.aWord_eq, prepared.bWord_eq]

/-- No boundary term is silently dropped when passing from the ordered
branch reduction to the complete cached period family. -/
theorem area_formula (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    lifted.edges.chainArea lifted.vertices value base.bank.exterior sheet + prepared.pairing value =
      paired.rows.internalArea value + paired.ending.internalArea value +
        Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value paired.rows.word)
          (-Topology.Surface.Sewing.SewingRetraction.wordValue value (paired.reference.hole.liftedBoundary
          lifted.vertices lifted.edges)) +
        paired.ending.exteriorArea value (Topology.Surface.Sewing.SewingRetraction.wordValue value paired.rows.word) +
          Topology.Mesh.RetracingWords.AreaTerm.total value ordered.prepared.compiled.areaTerms := by
  rw [prepared.pairing_eq]
  exact paired.area_formula value anti

/-- Prepare differential comparisons using the exact retained A parents and supplied original domain bank. -/
@[expose] def aComparisons (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (index : Fin genus) :=
  (prepared.row index).faces.a.comparisons domains differential

/-- Prepare differential comparisons using the exact corrected B parents and supplied original domain bank. -/
@[expose] def bComparisons (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (index : Fin genus) :=
  (prepared.row index).faces.bComparisons domains differential

/-- These are the exact initial recast parents of the displayed A program. -/
theorem aComparisons_parents (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (index : Fin genus) :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.parents differential 0
      ((prepared.row index).faces.a.geometry.assign (prepared.row index).faces.a.segments.pieces)
      (prepared.aComparisons domains differential index) =
      (prepared.aWalk index).initial.state.parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge
        differential) :=
  (prepared.row index).faces.a.comparisons_parents domains differential

/-- These are the exact initial recast parents of the corrected B program,
including its complete preceding A prefix. -/
theorem bComparisons_parents (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (index : Fin genus) :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.parents differential 0
      ((prepared.row index).faces.b.assign (prepared.row index).faces.bSegments.pieces)
      (prepared.bComparisons domains differential index) =
      (prepared.bWalk index).initial.state.parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge
        differential) :=
  (prepared.row index).faces.b_parents domains differential

end Prepared
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms

end
