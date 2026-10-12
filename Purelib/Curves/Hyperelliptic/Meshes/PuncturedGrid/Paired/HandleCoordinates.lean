module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Pairing
import Purelib.LinearAlgebra.Bilinear.Integral
import Purelib.LinearAlgebra.Bilinear.Matrix.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.CutIntersection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
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
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.Dual
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Topology.Surface.Word.Surgery
import Purelib.Tactic.Ring
public import Purelib.LinearAlgebra.Alternating.NormalForm.Evaluation

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Data.Vector

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Alternating.Handle

open Purelib.LinearAlgebra.Bilinear

open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord

open Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing

public section

/-!
# Ordered period rows in the retained cut normal form

The coordinate change is computed once per A/B row and has an exact inverse
readback to the retained chord coefficients. Physical and face corrections
remain owned by the original cut row. The intersection formulas below reduce
the geometric basis obligation to the actual transformed rows; they do not
assert a standard intersection table for those rows.
-/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.LinearAlgebra.Alternating.Handle.Pairing (handlePairing)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
    sheet} {paired : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
    {prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

namespace CutBank

/-- The complete integer coordinate vector on the original retained cut alphabet. -/
@[expose] def HandleVector (_cut : PeriodCoordinates.CutBank prepared) := Data.Vector Int
  lifted.cutBoundaryWord.alphabet.count

/-- The supplied vector is the original A row transported by the retained dual normal-form map. -/
@[expose] def AHandleCoordinates (cut : PeriodCoordinates.CutBank prepared) (index : Fin genus) (values :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleVector cut) : Prop :=
  values = cut.normal.normal.reduction.dualForward (cut.rows.get index).a.span.coefficients

/-- The supplied vector is the original B row transported by that same retained dual normal-form map. -/
@[expose] def BHandleCoordinates (cut : PeriodCoordinates.CutBank prepared) (index : Fin genus) (values :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleVector cut) : Prop :=
  values = cut.normal.normal.reduction.dualForward (cut.rows.get index).b.span.coefficients

set_option genInjectivity false in
/-- Complete normal-form coordinates, including unused coordinates. Keeping these entries makes the inverse readback
exact, without quotienting away a physical or radical term. -/
structure HandleRow (cut : PeriodCoordinates.CutBank prepared) (index : Fin genus) where
  /-- The complete retained transformed A coordinate vector. -/ a :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleVector cut
  /-- The complete retained transformed B coordinate vector. -/ b :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleVector cut
  /-- The A coordinates are exactly the original row's dual-forward image. -/ a_eq :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.AHandleCoordinates cut index a
  /-- The B coordinates are exactly the original row's dual-forward image. -/ b_eq :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.BHandleCoordinates cut index b

constructive_injectivity HandleRow

namespace HandleRow

variable {cut : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared} {first last
  : Fin genus}

/-- Cache both original row images under the retained cut's dual normal-form map. -/
@[expose] def build (cut : PeriodCoordinates.CutBank prepared) (index : Fin genus) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut index :=
  ⟨cut.normal.normal.reduction.dualForward (cut.rows.get index).a.span.coefficients,
    cut.normal.normal.reduction.dualForward (cut.rows.get index).b.span.coefficients, rfl, rfl⟩

/-- Applying the retained dual inverse recovers the exact original A coefficient vector. -/
theorem a_readback (row : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut
  first) :
    cut.normal.normal.reduction.dualBackward row.a = (cut.rows.get first).a.span.coefficients := by
  rw [row.a_eq]
  exact cut.normal.normal.reduction.dualBackward_dualForward _

/-- Applying the retained dual inverse recovers the exact original B coefficient vector. -/
theorem b_readback (row : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut
  first) :
    cut.normal.normal.reduction.dualBackward row.b = (cut.rows.get first).b.span.coefficients := by
  rw [row.b_eq]
  exact cut.normal.normal.reduction.dualBackward_dualForward _

/-- The actual spanning-chain intersection is the original integral coefficient pairing. -/
private theorem intersection_pairing
    {leftRow rightRow : Data.Vector Int lifted.cutBoundaryWord.alphabet.count}
    (left : IntegralPairing.SpanningCoordinates cut.integral leftRow)
    (right : IntegralPairing.SpanningCoordinates cut.integral rightRow) :
    Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection
      left right = Integral.pairing cut.integral.paired
      left.coefficients right.coefficients := by
  unfold SpanningCoordinates.intersection
    Integral.pairing Bilinear.Matrix.Basic.bilinear
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply FiniteSum.Fin.sumFin_congr
  intro column
  dsimp only
  rw [Int.cast_id]
  ring1

/-- The actual A/A intersection equals the handle pairing of the two retained transformed A rows. -/
theorem aa_intersection (left : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut
  first) (right : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut last) :
    cut.intersections.aa first last = Pairing.handlePairing cut.normal.pivots left.a right.a := by
  rw [cut.intersections.aa_eq, left.a_eq, right.a_eq]
  exact (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow.intersection_pairing _
    _).trans (cut.normal.normal.pairing _ _)

/-- The actual A/B intersection equals the handle pairing of the retained transformed A and B rows. -/
theorem ab_intersection (left : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut
  first) (right : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut last) :
    cut.intersections.ab first last = Pairing.handlePairing cut.normal.pivots left.a right.b := by
  rw [cut.intersections.ab_eq, left.a_eq, right.b_eq]
  exact (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow.intersection_pairing _
    _).trans (cut.normal.normal.pairing _ _)

/-- The actual B/B intersection equals the handle pairing of the two retained transformed B rows. -/
theorem bb_intersection (left : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut
  first) (right : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut last) :
    cut.intersections.bb first last = Pairing.handlePairing cut.normal.pivots left.b right.b := by
  rw [cut.intersections.bb_eq, left.b_eq, right.b_eq]
  exact (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow.intersection_pairing _
    _).trans (cut.normal.normal.pairing _ _)

end HandleRow

/-- All A/B rows use the same cut normal form and its certified genus count. -/
@[expose] def HandleRows (cut : PeriodCoordinates.CutBank prepared) :=
  Data.Vector.DependentVector (fun index : Fin genus =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow cut index)

/-- Cache every original genus-indexed A/B handle row using the same retained cut normal form. -/
@[expose] def handleRows (cut : PeriodCoordinates.CutBank prepared) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRows cut :=
  DependentVector.ofFn (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank.HandleRow.build cut)

end CutBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates
