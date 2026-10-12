module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Ring.IntCast
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.CutIntersection
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.GeneratorValuation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Data.Int.Arithmetic
open Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing

open Purelib.Algebra.Ring

open Purelib.Data.Int

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Realize the retained geometric intersection pairing by closed valuations on the actual surface. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.SewingRetraction

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
local notation "vget" => Data.Vector.get

/-- Casting an integer finite sum to displayed Gaussian rationals equals the finite sum of the casts. -/
private theorem cast_sum {count : Nat} (values : Fin count → Int) :
    ((sumFin values : Int) : Gaussian.Basic.Canonical) = sumFin (fun index => (values index : Gaussian.Basic.Canonical))
      := open Purelib.Algebra in by
  induction count with
  | zero => exact IntCast.cast_zero
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ,
      FiniteSum.Fin.sumFin_succ, IntCast.add, ih]

/-- An actual signed face correction reads as zero under a valuation closed on each original face. -/
private theorem faceValue_zero {vertices count : Nat} (faces : Fin count → Topology.Polygon.Stokes.OrientedTriangle
  vertices)
    (value : Topology.Polygon.Stokes.OrientedEdge vertices → Gaussian.Basic.Canonical)
    (closed : ∀ face, Topology.Surface.Sewing.SewingRetraction.wordValue value (faces face).boundary = 0)
    (correction : List (Topology.Surface.Sewing.SewingRetraction.FaceTerm count)) :
      Topology.Surface.Sewing.SewingRetraction.faceValue faces value correction = 0 := by
  induction correction with
  | nil => rfl
  | cons term rest ih =>
      change (term.1 : Gaussian.Basic.Canonical) * Topology.Surface.Sewing.SewingRetraction.wordValue value (faces
        term.2).boundary + _ = 0
      rw [closed term.2, mul_zero, ih, zero_add]

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}

namespace ClosedCoordinates
variable {word : List (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)} (row :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates word integral)

/-- The dual generator vector reuses the cached integral spanning coefficients and masks physical slots. -/
def dualValues : Data.Vector Gaussian.Basic.Canonical lifted.cutBoundaryWord.alphabet.count :=
  Data.Vector.Basic.vectorOfFn fun index => if lifted.cutBoundaryWord.alphabet.oneSided index then 0 else
    (row.span.coefficients index : Gaussian.Basic.Canonical)

/-- The retained dual generator vector vanishes at every physical boundary slot. -/
theorem dualValues_physical (index : Fin lifted.cutBoundaryWord.alphabet.count)
    (side : lifted.cutBoundaryWord.alphabet.oneSided index = true) : vget
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.ClosedCoordinates.dualValues row) index = 0 := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.ClosedCoordinates.dualValues,
    Data.Vector.Basic.vectorOfFn_apply, side]
  rfl

/-- Construct the closed original generator valuation from the retained integral span, with physical slots masked to
zero. -/
def dualValuation : GeneratorValuation lifted
  (Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.ClosedCoordinates.dualValues row) :=
  GeneratorValuation.build lifted
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.ClosedCoordinates.dualValues row)
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.ClosedCoordinates.dualValues_physical row)

/-- The acquired dual valuation reads each original generator as its retained span coefficient, or zero at a physical
slot. -/
theorem dual_generator (index : Fin lifted.cutBoundaryWord.alphabet.count) :
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.ClosedCoordinates.dualValuation row).value
      (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators index)) =
      if lifted.cutBoundaryWord.alphabet.oneSided index then 0 else (row.span.coefficients index :
        Gaussian.Basic.Canonical) :=
  ((Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.ClosedCoordinates.dualValuation row).generator_readback
    index).trans (Data.Vector.Basic.vectorOfFn_apply _ _)

/-- The physical slots and the actual signed face correction vanish in the acquired dual valuation. -/
theorem intersection_value {firstWord : List (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)}
    (first : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates firstWord integral) :
    Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.ClosedCoordinates.dualValuation row).value firstWord
      = (Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection
      first.span row.span : Gaussian.Basic.Canonical) := open Purelib.Algebra in by
  have source := first.value_eq
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.ClosedCoordinates.dualValuation row).value
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.ClosedCoordinates.dualValuation row).value_reverse
  have facesZero := Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.faceValue_zero
    lifted.mesh.triangulation.faces
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.ClosedCoordinates.dualValuation row).value
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.ClosedCoordinates.dualValuation row).face_zero
      first.route.correction
  rw [facesZero, add_zero] at source
  apply source.trans
  rw
    [SpanningCoordinates.intersection_left_readback
    first.span row.span, Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.cast_sum]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  dsimp only
  rw [Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation.ClosedCoordinates.dual_generator row,
    first.span.physical_eq]
  cases side : lifted.cutBoundaryWord.alphabet.oneSided index
  · change (first.coordinates.totals index : Gaussian.Basic.Canonical) * (row.span.coefficients index :
      Gaussian.Basic.Canonical) =
      ((first.coordinates.totals index - 0) * row.span.coefficients index : Int)
    rw [Arithmetic.sub_zero, Ring.IntCast.intCast_mul]
  · change (first.coordinates.totals index : Gaussian.Basic.Canonical) * 0 =
      ((first.coordinates.totals index - first.coordinates.totals index) * row.span.coefficients index : Int)
    rw [sub_self, zero_mul, IntCast.cast_zero, mul_zero]

end ClosedCoordinates
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.IntersectionValuation

