module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.CutIntersection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchIntersectionRelations
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PrefixValues
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates.Pair

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchIntersectionRelations

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchIntersectionRelations.Pair

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PrefixValues

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing

@[expose] public section

/-! Reference-cycle reduction of intersections of the actual corrected A/B programs. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ReferenceIntersections

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered
  Pair)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank ClosedCoordinates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates (ReferenceRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates.Pair (CutCoordinates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchIntersectionRelations.Pair (repeated_value_zero
  reference_value_closed)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut (GeneratorValuation)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

local infixl:70 " ⋂ₚ " =>
  Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection

/-- Casting a finite integer sum to Gaussian rationals preserves the actual indexed summands. -/
private theorem cast_sum {count : Nat} (values : Fin count → Int) :
    ((sumFin values : Int) : Data.Gaussian.Basic.Canonical) = sumFin (fun index => (values index :
      Data.Gaussian.Basic.Canonical)) := by
  induction count with
  | zero => exact Algebra.Ring.IntCast.cast_zero
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ, Algebra.Ring.IntCast.add, ih]

/-- The real component of the original Gaussian integer cast is its rational integer cast. -/
private theorem gaussian_int_re (value : Int) :
    (value : Data.Gaussian.Basic.Canonical).re = (value : Fraction.Rational) :=
  Data.Gaussian.Cast.gaussian_int_re value

/-- Equality of the original Gaussian integer casts implies equality of their integer sources. -/
private theorem gaussian_int_injective {first last : Int} (same : (first : Data.Gaussian.Basic.Canonical) = (last :
  Data.Gaussian.Basic.Canonical)) : first = last := by
  apply Fraction.Cast.Compatibility.intCast_injective_direct
  have realPart := congrArg Data.Gaussian.Basic.re same
  exact (gaussian_int_re first).symm.trans
    (realPart.trans (gaussian_int_re last))

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

namespace CutBank

set_option genInjectivity false in
/-- Reference rows share the existing cut pairing, normal form and retraction. -/
structure ReferenceReduction (cut : PeriodCoordinates.CutBank prepared) where
  /-- The cached reference-cycle rows sharing the exact original cut pairing, normal form and retraction. -/ rows :
    Data.Vector.DependentVector (fun index : BranchIsolation.Data.Index branches =>
    BasedBranchCutCoordinates.ReferenceRow bank index paired.split.ending.reference sheet cut.integral)

constructive_injectivity ReferenceReduction

namespace ReferenceReduction
variable {cut : CutBank prepared}

/-- Construct each actual branch-to-reference row using the original cut's retained retraction and integral normal form.
-/
def build (cut : PeriodCoordinates.CutBank prepared) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ReferenceIntersections.CutBank.ReferenceReduction cut :=
  ⟨DependentVector.ofFn fun index =>
    let pair := bank.pair index paired.split.ending.reference sheet
    ⟨pair, CutCoordinates.ofRetraction pair cut.retraction cut.integral cut.normal.normal⟩⟩

variable (data :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ReferenceIntersections.CutBank.ReferenceReduction cut) {word
  : List (Purelib.Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)}
  (right : ClosedCoordinates word
    cut.integral)

/-- The repeated reference cycle has zero actual intersection with every retained closed coordinate row. -/
theorem reference_zero :
    (data.rows.get paired.split.ending.reference).cut.span ⋂ₚ right.span = 0 := by
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ReferenceIntersections.gaussian_int_injective
  exact (ClosedCoordinates.intersection_value right (CutCoordinates.asClosed (data.rows.get
    paired.split.ending.reference).cut)).symm.trans
    ((Pair.repeated_value_zero (data.rows.get paired.split.ending.reference).pair (ClosedCoordinates.dualValuation
      right)).trans Algebra.Ring.IntCast.cast_zero.symm)

/-- The actual A intersection is the difference of its two original branch-to-reference intersections. -/
theorem a_intersection (index : Fin genus) :
    (cut.rows.get index).a.span ⋂ₚ right.span =
      (data.rows.get (paired.split.pairs[(Fin.cast paired.split.count_eq.symm index).val]'(Fin.cast
        paired.split.count_eq.symm index).isLt).1).cut.span ⋂ₚ right.span -
      (data.rows.get (paired.split.pairs[(Fin.cast paired.split.count_eq.symm index).val]'(Fin.cast
        paired.split.count_eq.symm index).isLt).2).cut.span ⋂ₚ right.span := by
  have relation := Pair.reference_value_closed (paired.row index).row.a
    (data.rows.get _).pair (data.rows.get _).pair (ClosedCoordinates.dualValuation right)
  rw [← prepared.aWord_eq index, ClosedCoordinates.intersection_value right (cut.rows.get index).a,
    ClosedCoordinates.intersection_value right (CutCoordinates.asClosed (data.rows.get _).cut),
      ClosedCoordinates.intersection_value right (CutCoordinates.asClosed (data.rows.get _).cut)] at relation
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ReferenceIntersections.gaussian_int_injective
  rw [Algebra.Ring.IntCast.sub]
  exact relation

/-- The actual corrected B intersection retains its original reference intersection and complete preceding A prefix. -/
theorem b_intersection (index : Fin genus) :
    (cut.rows.get index).b.span ⋂ₚ right.span =
      (data.rows.get (paired.split.pairs[(Fin.cast paired.split.count_eq.symm index).val]'(Fin.cast
        paired.split.count_eq.symm index).isLt).1).cut.span ⋂ₚ right.span +
      sumFin (fun earlier : Fin genus => if earlier.val < index.val then
        (cut.rows.get earlier).a.span ⋂ₚ right.span else 0) := by
  have relation := PrefixValues.Prepared.bWord_prefix_value
    paired prepared (ClosedCoordinates.dualValuation right).value index
  have reference := Pair.reference_value_closed (paired.row index).row.b
    (data.rows.get _).pair (data.rows.get paired.split.ending.reference).pair (ClosedCoordinates.dualValuation right)
  rw [ClosedCoordinates.intersection_value right (cut.rows.get index).b, reference,
    ClosedCoordinates.intersection_value right (CutCoordinates.asClosed (data.rows.get _).cut),
    ClosedCoordinates.intersection_value right (CutCoordinates.asClosed (data.rows.get
      paired.split.ending.reference).cut)] at relation
  dsimp only [CutCoordinates.asClosed] at relation
  rw [reference_zero
    data right, Algebra.Ring.IntCast.cast_zero, Data.Gaussian.Basic.sub_zero] at relation
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ReferenceIntersections.gaussian_int_injective
  rw [Algebra.Ring.IntCast.add, Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ReferenceIntersections.cast_sum,
    relation]
  apply congrArg (_ + ·)
  apply FiniteSum.Fin.sumFin_congr
  intro earlier
  by_cases before : earlier.val < index.val
  · rw [if_pos before, if_pos before, ClosedCoordinates.intersection_value right (cut.rows.get earlier).a]
  · rw [if_neg before, if_neg before, Algebra.Ring.IntCast.cast_zero]

/-- The same geometric reference reduction in the second intersection argument. -/
theorem intersection_a (index : Fin genus) :
    right.span ⋂ₚ (cut.rows.get index).a.span =
      right.span ⋂ₚ (data.rows.get (paired.split.pairs[(Fin.cast paired.split.count_eq.symm index).val]'(Fin.cast
        paired.split.count_eq.symm index).isLt).1).cut.span -
      right.span ⋂ₚ (data.rows.get (paired.split.pairs[(Fin.cast paired.split.count_eq.symm index).val]'(Fin.cast
        paired.split.count_eq.symm index).isLt).2).cut.span := by
  rw [SpanningCoordinates.intersection_skew right.span (cut.rows.get index).a.span,
    a_intersection
    data right index,
    SpanningCoordinates.intersection_skew (data.rows.get _).cut.span right.span,
    SpanningCoordinates.intersection_skew (data.rows.get _).cut.span right.span]
  ring1

/-- Corrected B intersections retain the complete preceding A prefix in either argument. -/
theorem intersection_b (index : Fin genus) :
    right.span ⋂ₚ (cut.rows.get index).b.span =
      right.span ⋂ₚ (data.rows.get (paired.split.pairs[(Fin.cast paired.split.count_eq.symm index).val]'(Fin.cast
        paired.split.count_eq.symm index).isLt).1).cut.span +
      sumFin (fun earlier : Fin genus => if earlier.val < index.val then
        right.span ⋂ₚ (cut.rows.get earlier).a.span else 0) := by
  rw [SpanningCoordinates.intersection_skew right.span (cut.rows.get index).b.span,
    b_intersection
    data right index,
    neg_add_rev, SpanningCoordinates.intersection_skew (data.rows.get _).cut.span right.span, neg_neg, add_comm]
  apply congrArg (_ + ·)
  rw [← FiniteSum.Fin.sumFin_neg]
  apply FiniteSum.Fin.sumFin_congr
  intro earlier
  by_cases before : earlier.val < index.val
  · rw [if_pos before, if_pos before,
      SpanningCoordinates.intersection_skew
        (cut.rows.get earlier).a.span right.span, neg_neg]
  · rw [if_neg before, if_neg before, neg_zero]

end ReferenceReduction
end CutBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ReferenceIntersections
