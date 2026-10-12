module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Topology.Surface.Boundary.PolarizedWordArea

@[expose] public section

/-! The extracted conjugate period term reads the actual corrected A/B
words and agrees with the original Hermitian area on the diagonal. -/
namespace Purelib.Riemann.Periods.NewtonConjugatePeriodReadback

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonGrid)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Topology.Mesh.RetracingWords (wordArea AreaTerm)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
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
open Purelib.Topology in
open Purelib.Data in
open Purelib.RootIsolation in
/-- Compute the conjugate/value A–B period pairing on the actual resplit lifted words.

Conjugate only the first valuation and retain the chosen new sheet, coordinate inclusion, edge bank and vertex bank for
both ordered words. -/
def conjugateResplitPeriodArea (newSheet : Fin 2)
    (first second : OrientedEdge vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin fun cycle : Fin genus =>
    Data.Gaussian.Basic.conj (Surface.Sewing.SewingRetraction.wordValue first (edges.indexedEdges vertices
      (included.resplit (prepared.aWalk cycle).closed.walk (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid
        lifted.vertices _)) newSheet)) *
      Surface.Sewing.SewingRetraction.wordValue second (edges.indexedEdges vertices
        (included.resplit (prepared.bWalk cycle).closed.walk
          (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid lifted.vertices _)) newSheet) -
    Data.Gaussian.Basic.conj (Surface.Sewing.SewingRetraction.wordValue first (edges.indexedEdges vertices
      (included.resplit (prepared.bWalk cycle).closed.walk (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid
        lifted.vertices _)) newSheet)) *
      Surface.Sewing.SewingRetraction.wordValue second (edges.indexedEdges vertices
        (included.resplit (prepared.aWalk cycle).closed.walk
          (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid lifted.vertices _)) newSheet)

open Purelib.Topology in
open Purelib.Data in
/-- Conjugating each edge value commutes with the finite ordered word sum. -/
private theorem word_conj {count : Nat} (value : OrientedEdge count → Gaussian.Basic.Canonical) (word : List
  (OrientedEdge count)) :
    Surface.Sewing.SewingRetraction.wordValue (fun edge => Data.Gaussian.Basic.conj (value edge)) word =
      Data.Gaussian.Basic.conj (Surface.Sewing.SewingRetraction.wordValue value word) := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      change Data.Gaussian.Basic.conj (value edge) + Surface.Sewing.SewingRetraction.wordValue _ rest =
        Data.Gaussian.Basic.conj (value edge + Surface.Sewing.SewingRetraction.wordValue value rest)
      rw [ih, Gaussian.Basic.conj_add]

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
open Purelib.RootIsolation in
/-- Bilinear polarization extracts exactly the conjugate/value pairing on the retained corrected words.

The same prepared A/B walks, resplitting and lifted banks occur in the original area and extracted pairing. -/
theorem extract_conjugate_resplit (newSheet : Fin 2)
    (first second : OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared included edges vertices newSheet
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
        Data.Gaussian.Basic.conj (first edge)) second coefficient)) =
      conjugateResplitPeriodArea prepared included edges vertices newSheet first second := by
  unfold Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea conjugateResplitPeriodArea
  rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_sum]
  apply FiniteSum.Fin.sumFin_congr
  intro cycle
  let aWord := edges.indexedEdges vertices
    (included.resplit (prepared.aWalk cycle).closed.walk (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid
      lifted.vertices _)) newSheet
  let bWord := edges.indexedEdges vertices
    (included.resplit (prepared.bWalk cycle).closed.walk (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid
      lifted.vertices _)) newSheet
  calc
    _ = Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Path.BoundaryRibbon.area
        (Data.Gaussian.Basic.conj (Data.Gaussian.Basic.conj (Surface.Sewing.SewingRetraction.wordValue first
          aWord)) +
          coefficient * Surface.Sewing.SewingRetraction.wordValue second aWord)
        (Data.Gaussian.Basic.conj (Data.Gaussian.Basic.conj (Surface.Sewing.SewingRetraction.wordValue first
          bWord)) +
          coefficient * Surface.Sewing.SewingRetraction.wordValue second bWord)) :=
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun coefficient =>
        by
        rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix,
          Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix, word_conj,
          word_conj])
    _ = _ := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_area _ _ _ _

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Data in
/-- On equal valuations, the conjugate resplit period pairing equals the original Hermitian period area. -/
theorem conjugateResplitPeriodArea_diagonal (newSheet : Fin 2)
    (value : OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    conjugateResplitPeriodArea prepared included edges vertices newSheet value value =
      Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared included edges vertices newSheet value
        := by
  unfold conjugateResplitPeriodArea Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea
  apply FiniteSum.Fin.sumFin_congr
  intro cycle
  rfl

end Purelib.Riemann.Periods.NewtonConjugatePeriodReadback
