module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Pairing
import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleColumns
import Purelib.LinearAlgebra.Matrix.Inverse.IntegralSymplecticRows
import Purelib.LinearAlgebra.Alternating.Handle.IndexedSum
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank

open Purelib.LinearAlgebra.Alternating.Handle

open Purelib.LinearAlgebra.Matrix.Inverse

@[expose] public section

/-! The standard intersection table of the actual corrected ordered A/B programs. -/
section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank (HandleRows)
open Purelib.LinearAlgebra (Matrix)
open Purelib.LinearAlgebra.Matrix (matrixOfFn matrixOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.LinearAlgebra.Alternating.Handle.Pairing (handlePairing)
open Purelib.LinearAlgebra.Alternating (handlePairing_indexed_count)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}
  (cut : CutBank prepared)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank

/-- The retained genus-many handle rows satisfy the standard alternating A/A, B/B and A/B pairing table. -/
theorem handle_row_table (rows
  : CutBank.HandleRows cut) :
    (∀ first last : Fin genus, Pairing.handlePairing cut.normal.pivots (rows.get first).a (rows.get last).a = 0) ∧
    (∀ first last : Fin genus, Pairing.handlePairing cut.normal.pivots (rows.get first).b (rows.get last).b = 0) ∧
    (∀ first last : Fin genus, Pairing.handlePairing cut.normal.pivots (rows.get first).a (rows.get last).b =
      if first = last then 1 else 0) := by
  let p : LinearAlgebra.Matrix Int genus :=
    LinearAlgebra.Matrix.matrixOfFn fun row column => Data.Vector.get (rows.get row).a (cut.pivotAt
    column).1
  let q : LinearAlgebra.Matrix Int genus :=
    LinearAlgebra.Matrix.matrixOfFn fun row column => Data.Vector.get (rows.get row).a (cut.pivotAt
    column).2
  let r : LinearAlgebra.Matrix Int genus :=
    LinearAlgebra.Matrix.matrixOfFn fun row column => Data.Vector.get (rows.get row).b (cut.pivotAt
    column).1
  let s : LinearAlgebra.Matrix Int genus :=
    LinearAlgebra.Matrix.matrixOfFn fun row column => Data.Vector.get (rows.get row).b (cut.pivotAt
    column).2
  have pp (row column : Fin genus) : FiniteSum.Fin.sumFin (fun index => p index row * r index column - r index row * p
    index column) = 0 := by
    simp only [p, r, LinearAlgebra.Matrix.matrixOfFn_apply]
    exact cut.first_column_wedges rows row column
  have qq (row column : Fin genus) : FiniteSum.Fin.sumFin (fun index => q index row * s index column - s index row * q
    index column) = 0 := by
    simp only [q, s, LinearAlgebra.Matrix.matrixOfFn_apply]
    exact cut.last_column_wedges rows row column
  have pq (row column : Fin genus) : FiniteSum.Fin.sumFin (fun index => p index row * s index column - r index row * q
    index column) =
      if row = column then 1 else 0 := by
    simp only [p, q, r, s, LinearAlgebra.Matrix.matrixOfFn_apply]
    exact cut.mixed_column_wedges rows row column
  obtain ⟨aa, bb, ab⟩ := IntegralSymplecticRows.row_identities p q r s pp qq pq
  refine ⟨?_, ?_, ?_⟩
  · intro first last
    have equal := aa first last
    simp only [p, q, LinearAlgebra.Matrix.matrixOfFn_apply] at equal
    exact (handlePairing_indexed_count cut.normal.pivots cut.handles_eq (rows.get first).a (rows.get last).a).trans
      equal
  · intro first last
    have equal := bb first last
    simp only [r, s, LinearAlgebra.Matrix.matrixOfFn_apply] at equal
    exact (handlePairing_indexed_count cut.normal.pivots cut.handles_eq (rows.get first).b (rows.get last).b).trans
      equal
  · intro first last
    have equal := ab first last
    simp only [p, q, r, s, LinearAlgebra.Matrix.matrixOfFn_apply] at equal
    exact (handlePairing_indexed_count cut.normal.pivots cut.handles_eq (rows.get first).a (rows.get last).b).trans
      equal

/-- The actual corrected original A-programs have zero mutual intersection. -/
theorem aa_standard (first
  last : Fin genus) : cut.intersections.aa first last = 0 :=
  (HandleRow.aa_intersection
    ((CutBank.handleRows cut).get first)
    ((CutBank.handleRows cut).get last)).trans
    ((cut.handle_row_table (CutBank.handleRows cut)).1 first last)

/-- The actual corrected original B-programs have zero mutual intersection. -/
theorem bb_standard (first
  last : Fin genus) : cut.intersections.bb first last = 0 :=
  (HandleRow.bb_intersection
    ((CutBank.handleRows cut).get first)
    ((CutBank.handleRows cut).get last)).trans
    ((cut.handle_row_table (CutBank.handleRows cut)).2.1 first last)

/-- The actual corrected original A/B programs have the Kronecker intersection table on the retained genus indices. -/
theorem ab_standard (first
  last : Fin genus) : cut.intersections.ab first last = if first = last then 1 else 0 :=
  (HandleRow.ab_intersection
    ((CutBank.handleRows cut).get first)
    ((CutBank.handleRows cut).get last)).trans
    ((cut.handle_row_table (CutBank.handleRows cut)).2.2 first last)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank

end
