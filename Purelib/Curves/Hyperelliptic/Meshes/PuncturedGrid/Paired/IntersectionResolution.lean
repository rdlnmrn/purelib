module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Pairing
import Purelib.LinearAlgebra.Bilinear.Integral
import Purelib.LinearAlgebra.Bilinear.Matrix.Basic
import Purelib.LinearAlgebra.Vector.Weighted

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.LinearAlgebra.Bilinear.Matrix.Wedge
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.CutIntersection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WedgeMatrix
public import Purelib.Topology.Surface.Cut.PairedRowReadback
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates
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
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Alternating.Handle

open Purelib.LinearAlgebra.Bilinear

open Purelib.LinearAlgebra.Bilinear.Matrix

open Purelib.LinearAlgebra.Vector

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing

@[expose] public section

/-! Exact reconstruction of the cut intersection pairing by the actual ordered A/B rows. -/
section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.RetracingWords (AreaTerm)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank ClosedCoordinates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank (HandleRows)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero)
open Purelib.LinearAlgebra.Bilinear.Matrix.Basic (bilinear)
open Purelib.LinearAlgebra.Vector.Weighted (weighted)
open Purelib.LinearAlgebra.Alternating.Handle.Pairing (handlePairing)

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

section
variable (cut : CutBank prepared)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank

/-- Subtraction of the physical rows extends the proved paired-entry identity to every slot. -/
theorem paired_row_wedges
  (first last : Fin lifted.cutBoundaryWord.alphabet.count) :
    FiniteSum.Fin.sumFin (fun index : Fin genus =>
      PairedRowReadback.pairedReadback (cut.rows.get index).a.span first * PairedRowReadback.pairedReadback
        (cut.rows.get index).b.span last -
      PairedRowReadback.pairedReadback (cut.rows.get index).b.span first * PairedRowReadback.pairedReadback
        (cut.rows.get index).a.span last) =
    cut.integral.paired first last := by
  cases firstSide : lifted.cutBoundaryWord.alphabet.oneSided first
  · cases lastSide : lifted.cutBoundaryWord.alphabet.oneSided last
    · apply Eq.trans _ (WedgeMatrix.wedgeEntry_eq_paired cut first last firstSide lastSide)
      exact FiniteSum.Fin.sumFin_congr (fun index => by
        rw [PairedRowReadback.pairedReadback_paired (cut.rows.get index).a.span first firstSide,
          PairedRowReadback.pairedReadback_paired (cut.rows.get index).b.span last lastSide,
          PairedRowReadback.pairedReadback_paired (cut.rows.get index).b.span first firstSide,
          PairedRowReadback.pairedReadback_paired (cut.rows.get index).a.span last lastSide])
    · rw [cut.integral.paired_eq, lastSide, Bool.or_true]
      change FiniteSum.Fin.sumFin _ = (0 : Int)
      apply Eq.trans (FiniteSum.Fin.sumFin_congr (fun index => ?_)) FiniteSum.Fin.sumFin_zero
      rw [PairedRowReadback.pairedReadback_physical (cut.rows.get index).b.span last lastSide,
        PairedRowReadback.pairedReadback_physical (cut.rows.get index).a.span last lastSide, mul_zero, mul_zero,
          sub_self]
  · rw [cut.integral.paired_eq, firstSide, Bool.true_or]
    change FiniteSum.Fin.sumFin _ = (0 : Int)
    apply Eq.trans (FiniteSum.Fin.sumFin_congr (fun index => ?_)) FiniteSum.Fin.sumFin_zero
    rw [PairedRowReadback.pairedReadback_physical (cut.rows.get index).a.span first firstSide,
      PairedRowReadback.pairedReadback_physical (cut.rows.get index).b.span first firstSide, zero_mul, zero_mul,
        sub_self]

/-- The full cut-pairing bilinear value is reconstructed by the alternating weighted products of the actual ordered A/B
rows. -/
theorem
  bilinear_reconstruction
    (left right : Data.Vector Int lifted.cutBoundaryWord.alphabet.count) :
    Bilinear.Matrix.Basic.bilinear (fun row column => cut.integral.paired row column) left right =
      FiniteSum.Fin.sumFin (fun index : Fin genus =>
        Weighted.weighted (PairedRowReadback.pairedReadback (cut.rows.get index).a.span) left * Weighted.weighted
          (PairedRowReadback.pairedReadback (cut.rows.get index).b.span) right -
        Weighted.weighted (PairedRowReadback.pairedReadback (cut.rows.get index).b.span) left * Weighted.weighted
          (PairedRowReadback.pairedReadback (cut.rows.get index).a.span) right) := by
  apply (Bilinear.Matrix.Basic.bilinear_congr (fun row column => (cut.paired_row_wedges row column).symm) left
    right).trans
  rw [Wedge.bilinear_sum]
  exact FiniteSum.Fin.sumFin_congr (fun index => Wedge.bilinear_wedge _ _ left right)

/-- The original integral pairing is reconstructed from its pairings with the retained ordered A/B spanning coordinates.
-/
theorem pairing_reconstruction
    (left right : Data.Vector Int lifted.cutBoundaryWord.alphabet.count) :
    Integral.pairing cut.integral.paired left right = FiniteSum.Fin.sumFin (fun index : Fin genus =>
      Integral.pairing cut.integral.paired (cut.rows.get index).a.span.coefficients left *
        Integral.pairing cut.integral.paired (cut.rows.get index).b.span.coefficients right -
      Integral.pairing cut.integral.paired (cut.rows.get index).b.span.coefficients left *
        Integral.pairing cut.integral.paired (cut.rows.get index).a.span.coefficients right) := by
  have castReadback : Integral.pairing cut.integral.paired left right =
      Bilinear.Matrix.Basic.bilinear (fun row column => cut.integral.paired row column) left right :=
    Bilinear.Matrix.Basic.bilinear_congr (fun _ _ => Int.cast_id) left right
  apply castReadback.trans
    ((bilinear_reconstruction cut left
    right).trans ?_)
  exact FiniteSum.Fin.sumFin_congr (fun index => by
    rw [PairedRowReadback.weighted_pairedReadback (cut.rows.get index).a.span left,
      PairedRowReadback.weighted_pairedReadback (cut.rows.get index).b.span right,
      PairedRowReadback.weighted_pairedReadback (cut.rows.get index).b.span left,
      PairedRowReadback.weighted_pairedReadback (cut.rows.get index).a.span right])

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.IntersectionResolution.CutBank

/-- The intersection of two actual closed cut-coordinate spans is their original integral matrix pairing. -/
private theorem intersection_pairing
    {firstWord lastWord : List (Stokes.OrientedEdge lifted.vertices.count)}
    (first : PeriodCoordinates.ClosedCoordinates firstWord cut.integral) (last : PeriodCoordinates.ClosedCoordinates
      lastWord cut.integral) :
    SpanningCoordinates.intersection first.span last.span = Integral.pairing cut.integral.paired first.span.coefficients
      last.span.coefficients := by
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply FiniteSum.Fin.sumFin_congr
  intro column
  dsimp only [Integral.pairing, Bilinear.Matrix.Basic.bilinear]
  rw [Int.cast_id]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.IntersectionResolution.CutBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank

/-- The original closed-coordinate intersection is reconstructed by the retained ordered A/B row intersections. -/
theorem
  intersection_reconstruction
    {firstWord lastWord : List (Stokes.OrientedEdge lifted.vertices.count)}
    (first : PeriodCoordinates.ClosedCoordinates firstWord cut.integral) (last : PeriodCoordinates.ClosedCoordinates
      lastWord cut.integral) :
    SpanningCoordinates.intersection first.span last.span = FiniteSum.Fin.sumFin (fun index : Fin genus =>
      SpanningCoordinates.intersection (cut.rows.get index).a.span first.span * SpanningCoordinates.intersection
        (cut.rows.get index).b.span last.span -
      SpanningCoordinates.intersection (cut.rows.get index).b.span first.span * SpanningCoordinates.intersection
        (cut.rows.get index).a.span last.span) := by
  apply (IntersectionResolution.CutBank.intersection_pairing cut first
    last).trans
  apply (pairing_reconstruction cut
    first.span.coefficients last.span.coefficients).trans
  exact FiniteSum.Fin.sumFin_congr (fun index => by
    rw [Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.IntersectionResolution.CutBank.intersection_pairing cut
      (cut.rows.get index).a first,
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.IntersectionResolution.CutBank.intersection_pairing cut
        (cut.rows.get index).b last,
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.IntersectionResolution.CutBank.intersection_pairing cut
        (cut.rows.get index).b first,
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.IntersectionResolution.CutBank.intersection_pairing cut
        (cut.rows.get index).a last])

/-- Transport to the existing full handle coordinates; unused coordinates remain present. -/
theorem handle_reconstruction
  (rows : CutBank.HandleRows cut)
    (left right : Data.Vector Int lifted.cutBoundaryWord.alphabet.count) :
    Pairing.handlePairing cut.normal.pivots left right = FiniteSum.Fin.sumFin (fun index : Fin genus =>
      Pairing.handlePairing cut.normal.pivots (rows.get index).a left * Pairing.handlePairing cut.normal.pivots
        (rows.get index).b right -
      Pairing.handlePairing cut.normal.pivots (rows.get index).b left * Pairing.handlePairing cut.normal.pivots
        (rows.get index).a right) := by
  have reconstruction :=
    pairing_reconstruction cut
    (cut.normal.normal.reduction.dualBackward left)
    (cut.normal.normal.reduction.dualBackward right)
  have readback := cut.normal.normal.pairing (cut.normal.normal.reduction.dualBackward left)
    (cut.normal.normal.reduction.dualBackward right)
  rw [cut.normal.normal.reduction.dualForward_dualBackward,
    cut.normal.normal.reduction.dualForward_dualBackward] at readback
  apply readback.symm.trans (reconstruction.trans ?_)
  apply FiniteSum.Fin.sumFin_congr
  intro index
  have first (value : Data.Vector Int lifted.cutBoundaryWord.alphabet.count) :
      Integral.pairing cut.integral.paired (cut.rows.get index).a.span.coefficients
        (cut.normal.normal.reduction.dualBackward value) = Pairing.handlePairing cut.normal.pivots (rows.get index).a
          value :=
    (cut.normal.normal.pairing _ _).trans (congrArg₂ (Pairing.handlePairing cut.normal.pivots)
      (rows.get index).a_eq.symm (cut.normal.normal.reduction.dualForward_dualBackward value))
  have last (value : Data.Vector Int lifted.cutBoundaryWord.alphabet.count) :
      Integral.pairing cut.integral.paired (cut.rows.get index).b.span.coefficients
        (cut.normal.normal.reduction.dualBackward value) = Pairing.handlePairing cut.normal.pivots (rows.get index).b
          value :=
    (cut.normal.normal.pairing _ _).trans (congrArg₂ (Pairing.handlePairing cut.normal.pivots)
      (rows.get index).b_eq.symm (cut.normal.normal.reduction.dualForward_dualBackward value))
  exact congrArg₂ (· - ·) (congrArg₂ (· * ·) (first left) (last right))
    (congrArg₂ (· * ·) (last left) (first right))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank

end
end
