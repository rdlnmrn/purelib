module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Integration.Energy.Polygon
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Topology.Polygon.Stokes
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.OrderedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Paired.Increments
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Tactic.Ring
public import Purelib.Topology.Surface.Sewing.SewnFaceAreaComparison

public section

/-! Exact homogeneous period readback on the retained corrected resplit walks. -/
namespace Purelib.Riemann.Periods.NewtonCombinedPeriodArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonGrid)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank (baseMember)
open Purelib.Topology.Mesh.RetracingWords (wordArea AreaTerm)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.LinearAlgebra.Gaussian.Energy (periodCombination unnormalizedEnergyForm GaussianMatrix)
open Purelib.Integration.Energy.Polygon (energyBoundaryArea energyPrimitivePoint
  periodPairingEnergy_eq_boundaryArea_im_div_four)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea (resplitPeriodArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea (resplitInternalArea resplitReadings)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    (prepared : Prepared paired)
  {fine : Polynomial.Geometry.Grid.ClearGrid curve.polynomial
    (Purelib.Curves.Hyperelliptic.Branches.Cuts.Ambient curve)}
  (included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion base.bank.grid fine)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames fine} (edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank fine)

open Purelib.Algebra in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Combine retained basis edge readings with a coefficient vector.

The finite sum uses the original oriented edge for every basis reading before evaluating any word. -/
@[expose] def combinedEdgeValue (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (values : Fin genus → OrientedEdge vertices.count → Gaussian.Basic.Canonical) (edge : OrientedEdge vertices.count) :
      Gaussian :=
  FiniteSum.Fin.sumFin fun basis => coefficients basis * values basis edge

open Purelib.Algebra in
open Purelib.Topology in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Word evaluation commutes with the finite coefficient combination of edge readings. -/
private theorem combined_word (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (values : Fin genus → OrientedEdge vertices.count → Gaussian.Basic.Canonical) (word : List (OrientedEdge
      vertices.count)) :
    Surface.Sewing.SewingRetraction.wordValue (combinedEdgeValue vertices coefficients values) word =
      FiniteSum.Fin.sumFin (fun basis => coefficients basis * Surface.Sewing.SewingRetraction.wordValue (values basis)
        word) := by
  induction word with
  | nil =>
      exact (FiniteSum.Fin.sumFin_congr (fun basis =>
        show coefficients basis * Surface.Sewing.SewingRetraction.wordValue (values basis) [] = 0 from mul_zero
          _)).trans
          FiniteSum.Fin.sumFin_zero |>.symm
  | cons edge rest ih =>
      change combinedEdgeValue vertices coefficients values edge +
        Surface.Sewing.SewingRetraction.wordValue (combinedEdgeValue vertices coefficients values) rest = _
      rw [ih, combinedEdgeValue, ← FiniteSum.Fin.sumFin_add]
      apply FiniteSum.Fin.sumFin_congr
      intro basis
      change coefficients basis * values basis edge + coefficients basis * Surface.Sewing.SewingRetraction.wordValue
        (values basis) rest =
        coefficients basis * (values basis edge + Surface.Sewing.SewingRetraction.wordValue (values basis) rest)
      ring1

open Purelib.Topology in
open Purelib.Data in
open Purelib.RootIsolation in
open Purelib.LinearAlgebra in
/-- The matrix of actual corrected A and B walks after splitting the grid.

Each entry evaluates the original ordered bank's retained walk, including the A prefix in each B walk. -/
@[expose] def resplitPeriodMatrix (newSheet : Fin 2)
    (values : Fin genus → OrientedEdge vertices.count → Gaussian.Basic.Canonical) (bSide : Bool) :
      Gaussian.Energy.GaussianMatrix genus :=
  Matrix.matrixOfFn fun basis cycle =>
    if bSide then Surface.Sewing.SewingRetraction.wordValue (values basis) (edges.indexedEdges vertices
      (included.resplit (prepared.bWalk cycle).closed.walk (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid
        lifted.vertices _)) newSheet)
    else Surface.Sewing.SewingRetraction.wordValue (values basis) (edges.indexedEdges vertices
      (included.resplit (prepared.aWalk cycle).closed.walk (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid
        lifted.vertices _)) newSheet)

open Purelib.Algebra in
open Purelib.Topology in
open Purelib.Data in
open Purelib.RootIsolation in
open Purelib.LinearAlgebra in
/-- Read a matrix period combination as the combined edge value on its actual corrected walk. -/
theorem resplit_combination_readback (newSheet : Fin 2)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (values : Fin genus → OrientedEdge vertices.count → Gaussian.Basic.Canonical) (bSide : Bool) (cycle : Fin genus) :
    Gaussian.Energy.periodCombination coefficients
      (resplitPeriodMatrix prepared included edges vertices newSheet values bSide) cycle =
      if bSide then Surface.Sewing.SewingRetraction.wordValue (combinedEdgeValue vertices coefficients values)
        (edges.indexedEdges vertices
        (included.resplit (prepared.bWalk cycle).closed.walk
          (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid lifted.vertices _)) newSheet)
      else Surface.Sewing.SewingRetraction.wordValue (combinedEdgeValue vertices coefficients values)
        (edges.indexedEdges vertices
        (included.resplit (prepared.aWalk cycle).closed.walk
          (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid lifted.vertices _)) newSheet) := by
  let aWord := edges.indexedEdges vertices
    (included.resplit (prepared.aWalk cycle).closed.walk (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid
      lifted.vertices _)) newSheet
  let bWord := edges.indexedEdges vertices
    (included.resplit (prepared.bWalk cycle).closed.walk (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid
      lifted.vertices _)) newSheet
  have scalar (basis : Fin genus) :
      resplitPeriodMatrix prepared included edges vertices newSheet values bSide basis cycle =
        Surface.Sewing.SewingRetraction.wordValue (values basis) (if bSide then bWord else aWord) := by
    unfold resplitPeriodMatrix
    rw [Matrix.matrixOfFn_apply]
    cases bSide <;> rfl
  unfold Gaussian.Energy.periodCombination
  rw [Matrix.Multiplication.vectorMatrix_apply]
  calc
    _ = FiniteSum.Fin.sumFin (fun basis => coefficients basis * Surface.Sewing.SewingRetraction.wordValue (values basis)
      (if bSide then bWord else aWord)) :=
      FiniteSum.Fin.sumFin_congr fun basis => congrArg (coefficients basis * ·) (scalar basis)
    _ = Surface.Sewing.SewingRetraction.wordValue (combinedEdgeValue vertices coefficients values) (if bSide then bWord
      else aWord) :=
      (combined_word vertices coefficients values _).symm
    _ = _ := by cases bSide <;> rfl

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- The energy boundary area equals twice the resplit period area of the combined readings.

The identity uses the same corrected A and B words for every coefficient vector. -/
theorem combined_energy_resplit (newSheet : Fin 2)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (values : Fin genus → OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    Energy.Polygon.energyBoundaryArea
      (Gaussian.Energy.periodCombination coefficients (resplitPeriodMatrix prepared included edges vertices newSheet
        values false))
      (Gaussian.Energy.periodCombination coefficients (resplitPeriodMatrix prepared included edges vertices newSheet
        values true)) =
      2 * Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared included edges vertices newSheet
        (combinedEdgeValue vertices coefficients values) := by
  unfold Energy.Polygon.energyBoundaryArea Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea
  rw [← FiniteSum.Fin.sumFin_mul_left]
  apply FiniteSum.Fin.sumFin_congr
  intro cycle
  rw [resplit_combination_readback prepared, resplit_combination_readback prepared]
  rw [Polygon.Stokes.commutatorBoundaryArea_eq]
  simp only [-eq_self, -iff_self, Energy.Polygon.energyPrimitivePoint, Path.BoundaryRibbon.area]
  rfl

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Read the unnormalized energy form as one quarter of the imaginary doubled period area. -/
theorem combined_raw_energy (newSheet : Fin 2)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (values : Fin genus → OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    Gaussian.Energy.unnormalizedEnergyForm coefficients
      (resplitPeriodMatrix prepared included edges vertices newSheet values false)
      (resplitPeriodMatrix prepared included edges vertices newSheet values true) =
      (2 * Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared included edges vertices newSheet
        (combinedEdgeValue vertices coefficients values)).im / 4 := by
  unfold Gaussian.Energy.unnormalizedEnergyForm
  rw [Energy.Polygon.periodPairingEnergy_eq_boundaryArea_im_div_four, combined_energy_resplit prepared]

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.LinearAlgebra in
/-- Decompose the coefficient combination's full ordered boundary area.

The equality retains the actual exterior, regular-region, paired and ending words, their cross area, and both reference
and joining connector contributions. -/
theorem combined_ordered_area
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex fine point →
      Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    (newSheet : Fin 2)
    (compiled : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included edges vertices (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember
      base.bank)
      ordered.prepared.partition newSheet)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (values : Fin genus → OrientedEdge vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ basis edge, values basis edge.reverse = -values basis edge) :
    let value := combinedEdgeValue vertices coefficients values
    let ending := edges.indexedEdges vertices
      (included.resplit (bank.loopProduct paired.split.ending.labels)
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet
    2 * edges.chainArea vertices value (included.resplit base.bank.exterior
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
      Energy.Polygon.energyBoundaryArea
        (Gaussian.Energy.periodCombination coefficients (resplitPeriodMatrix prepared included edges vertices newSheet
          values false))
        (Gaussian.Energy.periodCombination coefficients (resplitPeriodMatrix prepared included edges vertices newSheet
          values true)) =
      2 * (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitInternalArea included edges vertices bank
        newSheet value paired.split.pairs + Mesh.RetracingWords.wordArea value ending +
        Path.BoundaryRibbon.area (Path.Paired.Increments.total
          (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitReadings included edges vertices bank newSheet
          value paired.split.pairs))
          (Surface.Sewing.SewingRetraction.wordValue value ending + Surface.Sewing.SewingRetraction.wordValue value
            (edges.indexedEdges vertices
            (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk
              (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
            (Hyperelliptic.Branches.BranchCutLifts.otherSheet newSheet))) +
        (Geometry.Grid.CellBoundary.sumValues (fun occurrence => Mesh.RetracingWords.wordArea value occurrence.word)
          compiled.regulars +
          Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms)) := by
  intro value ending
  have reverse (edge : OrientedEdge vertices.count) : value edge.reverse = -value edge := by
    change FiniteSum.Fin.sumFin (fun basis => coefficients basis * values basis edge.reverse) =
      -FiniteSum.Fin.sumFin (fun basis => coefficients basis * values basis edge)
    rw [← FiniteSum.Fin.sumFin_neg]
    apply FiniteSum.Fin.sumFin_congr
    intro basis
    rw [anti basis edge]
    ring1
  have identity :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.OrderedBoundary.Ordered.Paired.Prepared.resplit_exterior_area_formula
    included edges vertices reference prepared newSheet compiled value reverse
  rw [combined_energy_resplit prepared]
  have doubled := congrArg (fun term : Gaussian.Basic.Canonical => 2 * term) identity
  exact (show 2 * edges.chainArea vertices value (included.resplit base.bank.exterior
    (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
      2 * Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared included edges vertices newSheet
        value =
      2 * (edges.chainArea vertices value (included.resplit base.bank.exterior
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet +
        Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared included edges vertices newSheet
          value) by ring1).trans doubled

end Purelib.Riemann.Periods.NewtonCombinedPeriodArea
