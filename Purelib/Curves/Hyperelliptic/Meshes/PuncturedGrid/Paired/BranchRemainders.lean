module
import Purelib.Data.List.Append
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Integration

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

public section

/-!
# Physical hole areas and explicit stem defects in the corrected residual

Every one-branch excursion is split at its actual transported sheets. Its
hole area is retained in full. Cancellation of the two stems requires both
their area defect and their total-increment defect to be controlled; neither
is inferred from coordinate closure or from a vanishing period.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}

/-- The two original stem-and-hole cross areas combine into the explicit return-minus-stem remainder. -/
private theorem Paired.BranchRemainders.cross_remainder (stem hole returning : Gaussian.Basic.Canonical) :
    Path.BoundaryRibbon.area stem hole + Path.BoundaryRibbon.area (stem + hole) returning = Path.BoundaryRibbon.area
      (stem + hole) (returning - stem) := by
  apply Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, Path.BoundaryRibbon.area, Data.Gaussian.Basic.conj,
    Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re,
    Gaussian.Basic.mul_im] <;> ring1

/-- Read the original outward stem on its actual incoming sheet. -/
@[expose] def
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.stemWord
  (bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (index :
  Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (sheet : Fin 2) :=
  lifted.edges.indexedEdges lifted.vertices (bank.rows.get index).stem sheet

/-- Read the original hole boundary on the sheet reached by its retained stem. -/
@[expose] def
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.holeWord
  (bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (index :
  Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (sheet : Fin 2) :=
  lifted.edges.indexedEdges lifted.vertices (bank.rows.get index).boundary
    (SquareRoot.Grid.EdgeBank.RootEdgeBank.target lifted.edges (bank.rows.get index).stem sheet)

/-- Read the original reversed stem on the sheet reached after its actual hole boundary. -/
@[expose] def
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.returnWord
  (bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (index :
  Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (sheet : Fin 2) :=
  lifted.edges.indexedEdges lifted.vertices (bank.rows.get index).stem.reverse
    (SquareRoot.Grid.EdgeBank.RootEdgeBank.target lifted.edges (bank.rows.get index).boundary
      (SquareRoot.Grid.EdgeBank.RootEdgeBank.target lifted.edges (bank.rows.get index).stem sheet))

/-- The original lifted branch loop is exactly its retained stem, hole and return word concatenation. -/
theorem
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.loop_words
  (bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (index :
  Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    (bank.liftedLoop index sheet).indexed = bank.stemWord index sheet ++ (bank.holeWord index sheet ++ bank.returnWord
      index sheet) := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.liftedLoop_indexed,
    (bank.rows.get index).reference_eq,
    lifted.edges.indexedEdges_append, lifted.edges.indexedEdges_append]
  rfl

/-- Read the full area of the original transported hole boundary. -/
@[expose] def
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.holeArea
  (bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (value :
  Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (sheet : Fin 2) : Gaussian :=
      Topology.Mesh.RetracingWords.wordArea value (bank.holeWord index sheet)

/-- Retain the original outward-and-return stem areas together with their exact endpoint-defect cross term. -/
@[expose] def
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.stemError
  (bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (value :
  Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (sheet : Fin 2) : Gaussian :=
  Topology.Mesh.RetracingWords.wordArea value (bank.stemWord index sheet) + Topology.Mesh.RetracingWords.wordArea value
    (bank.returnWord index sheet) +
    Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.stemWord index sheet) +
      Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.holeWord index sheet))
      (Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.returnWord index sheet) -
        Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.stemWord index sheet))

/-- Both independent stem defects are paid. The full transported
stem-plus-hole magnitude multiplies the endpoint defect. -/
theorem
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.stemError_bound
  (bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (value :
  Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    Data.Gaussian.Norm.Basic.normSq (bank.stemError value index sheet) ≤ 2 *
      (Data.Gaussian.Norm.Basic.normSq (Topology.Mesh.RetracingWords.wordArea value (bank.stemWord index sheet) +
        Topology.Mesh.RetracingWords.wordArea value (bank.returnWord index sheet)) +
        4 * Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.stemWord
          index sheet) + Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.holeWord index sheet)) *
          Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.returnWord
            index sheet) - Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.stemWord index sheet))) :=
  open Purelib.Data.Rat in (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (le_refl _) (Path.BoundaryRibbon.area_bound _ _)) (by decide))

/-- No sheet-negation assumption is needed for this exact decomposition;
any failure of stem cancellation remains an explicit error term. -/
theorem
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.loop_area
  (bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (value :
  Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) (sheet : Fin 2) :
    Topology.Mesh.RetracingWords.wordArea value (bank.liftedLoop index sheet).indexed = bank.holeArea value index sheet
      + bank.stemError value index sheet := by
  rw [bank.loop_words, ← Purelib.Data.List.Append.append_assoc, Topology.Mesh.RetracingWords.wordArea_append,
    Topology.Mesh.RetracingWords.wordArea_append, Topology.Surface.Sewing.SewingRetraction.wordValue_append]
  unfold Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.holeArea
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.stemError
  rw [show Topology.Mesh.RetracingWords.wordArea value (bank.stemWord index sheet) +
    Topology.Mesh.RetracingWords.wordArea value (bank.holeWord index sheet) +
      Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.stemWord index sheet))
        (Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.holeWord index sheet)) +
      Topology.Mesh.RetracingWords.wordArea value (bank.returnWord index sheet) +
      Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.stemWord index sheet) +
        Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.holeWord index sheet))
        (Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.returnWord index sheet)) =
      Topology.Mesh.RetracingWords.wordArea value (bank.holeWord index sheet) +
        (Topology.Mesh.RetracingWords.wordArea value (bank.stemWord index sheet) + Topology.Mesh.RetracingWords.wordArea
          value (bank.returnWord index sheet)) +
        (Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.stemWord index sheet))
          (Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.holeWord index sheet)) +
          Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.stemWord index sheet)
            + Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.holeWord index sheet))
            (Topology.Surface.Sewing.SewingRetraction.wordValue value (bank.returnWord index sheet))) by ring1,
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders.cross_remainder]
  ring1

namespace Paired.BranchArea.PairedRows

variable {bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {reference : Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {sheet : Fin 2}

/-- Sum the full original hole areas of the retained paired rows on their actual incoming sheets. -/
@[expose] def holeAreas (value :
  Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    {labels : List (Hyperelliptic.Branches.BranchIsolation.Data.Index branches ×
      Hyperelliptic.Branches.BranchIsolation.Data.Index branches)} → {prior :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet} →
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior →
        Gaussian.Basic.Canonical
  | _, _, .nil _ => 0
  | _, _, .cons (labels := labels) _ tail =>
      bank.holeArea value labels.1 sheet + bank.holeArea value labels.2
        (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet) + holeAreas value tail

/-- Sum the explicit original stem defects of the retained paired rows. -/
@[expose] def stemErrors (value :
  Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    {labels : List (Hyperelliptic.Branches.BranchIsolation.Data.Index branches ×
      Hyperelliptic.Branches.BranchIsolation.Data.Index branches)} → {prior :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet} →
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior →
        Gaussian.Basic.Canonical
  | _, _, .nil _ => 0
  | _, _, .cons (labels := labels) _ tail =>
      bank.stemError value labels.1 sheet + bank.stemError value labels.2
        (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet) + stemErrors value tail

/-- The internal area of the original paired rows is the full retained hole-area sum plus the actual stem-error sum. -/
theorem internalArea_split (value
  : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    ∀ {labels : List (Hyperelliptic.Branches.BranchIsolation.Data.Index branches ×
      Hyperelliptic.Branches.BranchIsolation.Data.Index branches)} {prior :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet}
      (rows : Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior),
        rows.internalArea value = rows.holeAreas value + rows.stemErrors value
  | _, _, .nil _ => (_root_.add_zero _).symm
  | _, _, .cons row tail => by
      change Topology.Mesh.RetracingWords.wordArea value row.a.outward.indexed + Topology.Mesh.RetracingWords.wordArea
        value row.a.returning.indexed + tail.internalArea value = _
      rw [row.a.outward_eq, row.a.returning_indexed, bank.loop_area, bank.loop_area, internalArea_split value tail]
      change _ = (_ + _ + _) + (_ + _ + _)
      ring1

end Paired.BranchArea.PairedRows

namespace OrderedBranchPairs.EndingTours

variable {bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet
  : Fin 2}

/-- Sum the full original hole areas of the retained terminal tours on their actual incoming sheets. -/
@[expose] def holeAreas (value :
  Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    {ending : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding
      (Hyperelliptic.Branches.BranchIsolation.Data.Index branches)} →
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending → Gaussian.Basic.Canonical
  | _, .odd index _ => bank.holeArea value index sheet
  | _, .even index last _ _ => bank.holeArea value index sheet + bank.holeArea value last
    (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)

/-- Sum the explicit original stem defects of the retained terminal tours. -/
@[expose] def stemErrors (value
  : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    {ending : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding
      (Hyperelliptic.Branches.BranchIsolation.Data.Index branches)} →
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending → Gaussian.Basic.Canonical
  | _, .odd index _ => bank.stemError value index sheet
  | _, .even index last _ _ => bank.stemError value index sheet + bank.stemError value last
    (Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank in
/-- The internal area of the original terminal tours is the full retained hole-area sum plus the actual stem-error sum.
-/
theorem internalArea_split
  (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    {ending : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding
      (Hyperelliptic.Branches.BranchIsolation.Data.Index branches)} (tours :
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.EndingTours bank sheet ending) :
    tours.internalArea value = tours.holeAreas value + tours.stemErrors value := by
  cases tours with
  | odd index reference =>
      change Topology.Mesh.RetracingWords.wordArea value reference.outward.indexed = _
      rw [reference.outward_eq, bank.loop_area]
      rfl
  | even index last reference terminal =>
      change Topology.Mesh.RetracingWords.wordArea value terminal.outward.indexed +
        Topology.Mesh.RetracingWords.wordArea value terminal.returning.indexed = _
      rw [terminal.outward_eq, terminal.returning_indexed, bank.loop_area, bank.loop_area]
      change _ = (_ + _) + (_ + _)
      ring1

end OrderedBranchPairs.EndingTours

namespace Paired.PeriodPrograms.Prepared

variable {bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet
  : Fin 2} {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered
  bank sheet} {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}

/-- The actual residual exposes the single-lap holes and all stem defects
before any shrinking-hole or opposite-sheet analytic estimate is applied. -/
theorem surfaceResidual_split
  (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (value :
  Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared value =
      (paired.rows.holeAreas value + paired.ending.holeAreas value) +
      (paired.rows.stemErrors value + paired.ending.stemErrors value) +
      Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value paired.rows.word)
        (-Topology.Surface.Sewing.SewingRetraction.wordValue value (paired.reference.hole.liftedBoundary lifted.vertices
        lifted.edges)) +
      paired.ending.exteriorArea value (Topology.Surface.Sewing.SewingRetraction.wordValue value paired.rows.word) +
      Topology.Mesh.RetracingWords.AreaTerm.total value ordered.prepared.compiled.areaTerms -
      lifted.edges.chainArea lifted.vertices value base.bank.exterior sheet := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual, paired.rows.internalArea_split,
    paired.ending.internalArea_split]
  ring1

end Paired.PeriodPrograms.Prepared
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
