module
public import Purelib.LinearAlgebra.Alternating.NormalForm.Intersection
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Bilinear.Integral
import Purelib.LinearAlgebra.Bilinear.Matrix.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods
public import Purelib.Topology.Surface.Sewing.CutIntersection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenus
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.Surgery
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormPeriods

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra.Bilinear

open Purelib.Riemann

open Purelib.Riemann.Meshes

open Purelib.Topology.Surface.Cut.IntegralPairing

open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord

open Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.PairedWord

open Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord

@[expose] public section

/-!
# Actual symplectic intersections of the computed handle period chains

The existing normal-form period bank already specifies its actual closed
chains, including the minus-second/first orientation of each handle. Here
their full intersection table is proved from cut-chord crossings. No table
check, branch-label convention, analytic estimate, or numerical period
request is needed. Identifying the number of these handles with the curve
genus and comparing them with the prescribed standard tours remain separate.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.ChordCycleBank

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Sewing (ChordCycleBank)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing (SpanningCoordinates)
open Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.ChordCoordinate (crossing)
open Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates (intersection
  intersection_eq_crossings)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.LinearAlgebra.Bilinear.Integral (pairing)
open Purelib.LinearAlgebra.Bilinear.Matrix.Basic (bilinear)

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List
  (OrientedEdge source)}
  {word : Purelib.Topology.Surface.Cut.BoundaryWord.CutBoundaryWord labels edges}

/-- Signed crossings of the retained chord paths, extended to the actual integer-weighted chains. No new root or path
preparation is performed. -/
def intersection (bank : Topology.Surface.Sewing.ChordCycleBank word)
    (first last : Data.Vector Int word.alphabet.count) : Int :=
  FiniteSum.Fin.sumFin fun row => FiniteSum.Fin.sumFin fun column =>
    first row * ChordCoordinate.crossing (bank.coordinates row) (bank.coordinates column) * last column

/-- The signed crossing sum of the retained chord chains equals their exact integral pairing. -/
theorem intersection_eq_pairing (bank : Topology.Surface.Sewing.ChordCycleBank word) (integral :
  Purelib.Topology.Surface.Cut.IntegralPairing.CutBoundaryWord
  word)
    (first last : Data.Vector Int word.alphabet.count) :
    intersection bank first last
      = Purelib.LinearAlgebra.Bilinear.Integral.pairing integral.paired first last := by
  unfold intersection Integral.pairing
    Matrix.Basic.bilinear
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply FiniteSum.Fin.sumFin_congr
  intro column
  rw [ChordCycleBank.crossing_eq_paired bank integral]
  simp only [Int.cast_id]
  ring1

/-- The retained chord-chain crossing sum equals the intersection of the supplied spanning-coordinate witnesses. -/
theorem intersection_eq_spans (bank : Topology.Surface.Sewing.ChordCycleBank word) {integral :
  Purelib.Topology.Surface.Cut.IntegralPairing.CutBoundaryWord
  word}
    {firstRow lastRow : Data.Vector Int word.alphabet.count}
    (first : IntegralPairing.SpanningCoordinates integral firstRow)
    (last : IntegralPairing.SpanningCoordinates integral lastRow) :
    intersection bank first.coefficients
      last.coefficients = SpanningCoordinates.intersection first last :=
  (SpanningCoordinates.intersection_eq_crossings first last bank).symm

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.ChordCycleBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.CutChordPrograms

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutChordPrograms)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods (ComponentSamples)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (NormalFormPeriods)
open Purelib.Topology.Surface.Word.NormalForm (WordNormalForm)
open Purelib.Riemann.Meshes.LiftedPuncturedGrid (cutWord_handle_count)
open Purelib.LinearAlgebra.Alternating.Handle.Basic (PivotIndices)
open _root_.Purelib.LinearAlgebra.Alternating (NormalForm)
open Purelib.Data.Vector.Basic (vectorOfFn)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {source :
    Differential genus}
  {prepared : CutChordPrograms lifted source}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {differential : Fin genus} {components :
    ComponentSamples prepared.programs differential}
  {raw : List (PivotIndices lifted.cutBoundaryWord.alphabet.count)}
    {normal : LinearAlgebra.Alternating.NormalForm integral.paired raw}

/-- The actual first handle period retains the normal form's signed first-weight vector. -/
theorem first_weights (periods : NormalFormPeriods components normal) (pair :
  Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count) :
    (periods.first pair).weights = normal.firstWeights pair := by
  change Data.Vector.Basic.vectorOfFn (fun index => -(periods.rows pair.2).weights index) = _
  rw [periods.weights_eq]
  rfl

/-- The actual second handle period retains the normal form's second-weight vector. -/
theorem last_weights (periods : NormalFormPeriods components normal) (pair :
  Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count) :
    (periods.last pair).weights = normal.lastWeights pair := periods.weights_eq pair.1

/-- Every entry of the retained row bank is the corresponding actual signed handle entry, not merely an equality between
formal labels. -/
theorem row_intersection (periods : NormalFormPeriods components normal)
    (first last : Fin lifted.cutBoundaryWord.alphabet.count) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.ChordCycleBank.intersection prepared.routes
      (periods.rows first).weights (periods.rows last).weights =
      Handle.Basic.handleEntry raw first last := by
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.ChordCycleBank.intersection_eq_pairing
    prepared.routes integral, periods.weights_eq, periods.weights_eq]
  exact normal.cycleRows_entry first last

/-- Any two retained first handle chains have zero intersection. -/
theorem first_first_intersection (periods : NormalFormPeriods components normal)
    (first last : Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)
    (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.ChordCycleBank.intersection prepared.routes
      (periods.first first).weights (periods.first last).weights = 0 := by
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.ChordCycleBank.intersection_eq_pairing
    prepared.routes integral,
    first_weights periods,
    first_weights periods]
  exact normal.first_first first last firstMember lastMember

/-- Any two retained second handle chains have zero intersection. -/
theorem last_last_intersection (periods : NormalFormPeriods components normal)
    (first last : Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)
    (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.ChordCycleBank.intersection prepared.routes
      (periods.last first).weights (periods.last last).weights = 0 := by
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.ChordCycleBank.intersection_eq_pairing
    prepared.routes integral,
    last_weights periods,
    last_weights periods]
  exact normal.last_last first last firstMember lastMember

/-- The retained first and second handle chains have intersection one for the same pivot and zero otherwise. -/
theorem first_last_intersection (periods : NormalFormPeriods components normal)
    (first last : Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)
    (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.ChordCycleBank.intersection prepared.routes
      (periods.first first).weights (periods.last last).weights =
      if first = last then 1 else 0 := by
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.ChordCycleBank.intersection_eq_pairing
    prepared.routes integral,
    first_weights periods,
    last_weights periods]
  exact normal.first_last first last firstMember lastMember

/-- The actual chord normal-form period chains form a genus-sized symplectic handle family.

The retained pivot list has the curve genus, and its first/first, second/second and mixed intersection tables are the
exact signed crossings of the original chord chains. -/
structure SymplecticHandles
    {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
    {lifted : Meshes.LiftedPuncturedGrid base} {source : Differentials.Basic.Differential genus}
    (prepared : CyclePrograms.CutChordPrograms lifted source)
    {integral : Purelib.Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
    {differential : Fin genus} (components : ChainPeriods.ComponentSamples prepared.programs differential)
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
    (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw) (periods : NormalFormPeriods
      components normal) where
  /-- The actual retained pivot count equals the original curve genus. -/ handles_eq : raw.length = genus
  /-- Every retained first/first handle intersection is zero. -/ first_first : ∀ first last : Handle.Basic.PivotIndices
    lifted.cutBoundaryWord.alphabet.count,
    first ∈ raw → last ∈ raw →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.ChordCycleBank.intersection prepared.routes
      (periods.first first).weights (periods.first last).weights = 0
  /-- Every retained second/second handle intersection is zero. -/ last_last : ∀ first last : Handle.Basic.PivotIndices
    lifted.cutBoundaryWord.alphabet.count,
    first ∈ raw → last ∈ raw →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.ChordCycleBank.intersection prepared.routes
      (periods.last first).weights (periods.last last).weights = 0
  /-- The retained mixed handle intersection is one on equal pivots and zero otherwise. -/ first_last : ∀ first last :
    Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count,
    first ∈ raw → last ∈ raw →
    Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.ChordCycleBank.intersection prepared.routes
      (periods.first first).weights (periods.last last).weights =
      if first = last then 1 else 0

/-- Certify the retained chord-period handle family using the original cut-word genus theorem and exact normal-form
intersection identities. -/
theorem SymplecticHandles.build
    {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
    {lifted : Meshes.LiftedPuncturedGrid base} {source : Differentials.Basic.Differential genus}
    (prepared : CyclePrograms.CutChordPrograms lifted source)
    {differential : Fin genus} (components : ChainPeriods.ComponentSamples prepared.programs differential)
    (word : NormalForm.WordNormalForm
      (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      (IntegralPairing.wordSignature lifted.cutIntegralPairing))
    (periods : NormalFormPeriods components word.normal) :
    SymplecticHandles prepared
      components word.normal periods where
  handles_eq := LiftedPuncturedGrid.cutWord_handle_count lifted word
  first_first := fun first last firstMember lastMember =>
    first_first_intersection periods
      first last firstMember lastMember
  last_last := fun first last firstMember lastMember =>
    last_last_intersection periods
      first last firstMember lastMember
  first_last := fun first last firstMember lastMember =>
    first_last_intersection periods
      first last firstMember lastMember

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalFormIntersection.CutChordPrograms
