module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Riemann.Periods.NewtonCombinedPeriodArea
public import Purelib.Riemann.Periods.NewtonConjugatePeriodReadback
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Tactic.Ring

@[expose] public section

/-! Contract the conjugate basis-pair periods into the actual homogeneous
raw period form on the same corrected ordered A/B words. -/
namespace Purelib.Riemann.RootContinuation.NewtonHomogeneousConjugateReadback

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
open Purelib.Topology.Mesh.RetracingWords (wordArea AreaTerm)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Riemann.Periods.NewtonCombinedPeriodArea (combinedEdgeValue resplitPeriodMatrix combined_raw_energy)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea (resplitPeriodArea)
open Purelib.Riemann.Periods.NewtonConjugatePeriodReadback (conjugateResplitPeriodArea)
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
open Purelib.LinearAlgebra in
/-- The word value of a finite coefficient combination equals the corresponding combination of original word values. -/
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

section
open Purelib.Algebra
open Purelib.Data
/-- Gaussian conjugation commutes with the finite indexed sum. -/
private theorem conjugate_sum {count : Nat} (values : Fin count → Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.conj (FiniteSum.Fin.sumFin values) =
      FiniteSum.Fin.sumFin (fun index => Data.Gaussian.Basic.conj (values index)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ,
      Gaussian.Basic.conj_add, ih]

/-- Conjugating a finite coefficient combination conjugates both its coefficients and values. -/
private theorem conjugate_combination (coefficients values : Fin genus → Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.conj (FiniteSum.Fin.sumFin (fun basis => coefficients basis * values basis)) =
      FiniteSum.Fin.sumFin (fun basis => Data.Gaussian.Basic.conj (coefficients basis) *
        Data.Gaussian.Basic.conj (values basis)) := by
  rw [conjugate_sum]
  exact FiniteSum.Fin.sumFin_congr fun basis => Gaussian.Basic.conj_mul _ _

end

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
open Purelib.RootIsolation in
open Purelib.LinearAlgebra in
/-- Contract all conjugate basis-pair areas into the actual combined period area.

The equality keeps the original corrected ordered A/B words, refined edge owners and selected sheet, including every
off-diagonal basis pair. -/
theorem combined_conjugate_period_area (newSheet : Fin 2)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (values : Fin genus → OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea prepared included edges vertices newSheet
      (combinedEdgeValue vertices coefficients values) =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second =>
        Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
          conjugateResplitPeriodArea prepared included edges vertices newSheet (values first) (values second))) := by
  unfold Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitPeriodArea conjugateResplitPeriodArea
  rw [← Periods.BilinearCombination.sumFin_combination]
  apply FiniteSum.Fin.sumFin_congr
  intro cycle
  rw [combined_word, combined_word]
  let aWord := edges.indexedEdges vertices
    (included.resplit (prepared.aWalk cycle).closed.walk (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid
      lifted.vertices _)) newSheet
  let bWord := edges.indexedEdges vertices
    (included.resplit (prepared.bWalk cycle).closed.walk (SquareRoot.Grid.LiftedVertices.VertexBank.coordinate_onGrid
      lifted.vertices _)) newSheet
  have expanded := Periods.BilinearCombination.edgeArea_combination
    (fun basis => Data.Gaussian.Basic.conj (coefficients basis)) coefficients
    (fun basis => Data.Gaussian.Basic.conj (Surface.Sewing.SewingRetraction.wordValue (values basis) aWord))
    (fun basis => Data.Gaussian.Basic.conj (Surface.Sewing.SewingRetraction.wordValue (values basis) bWord))
    (fun basis => Surface.Sewing.SewingRetraction.wordValue (values basis) aWord) (fun basis =>
      Surface.Sewing.SewingRetraction.wordValue (values basis) bWord)
  rw [← conjugate_combination, ← conjugate_combination] at expanded
  exact expanded

open Purelib.Algebra in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Identify the complete weighted conjugate area with the raw homogeneous period energy.

The original corrected A/B period matrices retain the factor of two and imaginary-part division by four. -/
theorem combined_conjugate_raw_energy (newSheet : Fin 2)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (values : Fin genus → OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    Gaussian.Energy.unnormalizedEnergyForm coefficients
      (resplitPeriodMatrix prepared included edges vertices newSheet values false)
      (resplitPeriodMatrix prepared included edges vertices newSheet values true) =
      (2 * FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second =>
        Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
          conjugateResplitPeriodArea prepared included edges vertices newSheet (values first) (values second)))).im / 4
            := by
  rw [combined_raw_energy prepared, combined_conjugate_period_area prepared]

end Purelib.Riemann.RootContinuation.NewtonHomogeneousConjugateReadback
