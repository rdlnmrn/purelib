module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueStemRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueHoleRequests
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Polynomial

open Purelib

@[expose] public section

/-!
# Mixed surface residual assembly

`GridPairedBranchRemainders.surfaceResidual_split` writes the corrected
surface residual as

```
single + stems + cross + exterior + connectors - chainArea
```

The value-generic stem aggregate pays `stems`, and the value-generic hole
aggregate pays `single + single + physicalHoles`. The remaining term is the
physical ending/exterior/cross gap, which is a typed, value-generic
obligation: the same §1 physical-boundary comparison the single differential
owes. This module names the three pieces and combines them, so no consumer
mistakes the aggregates for a complete residual bound.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Surface.MixedSurfaceResidual

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct
  add_le_add_direct)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}

/-- The mixed single-lap hole sum with the physical hole boundaries, the term
paid by the value-generic hole aggregate. -/
def mixedHoleSum (_prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (value :
  OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  (paired.rows.holeAreas value + paired.ending.holeAreas value) +
    (paired.rows.holeAreas value + paired.ending.holeAreas value) +
    Geometry.Grid.CellBoundary.sumValues (fun hole => Topology.Mesh.RetracingWords.wordArea value (hole.liftedBoundary
      owner.lifted.vertices owner.lifted.edges)) owner.base.faces.holes

/-- The mixed stem defect, the term paid by the value-generic stem aggregate. -/
def mixedStemSum (_prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (value :
  OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  paired.rows.stemErrors value + paired.ending.stemErrors value

/-- The physical ending/exterior/cross gap: the part of the reduced residual
not already paid by the value-generic hole aggregate. -/
def mixedSurfaceGap (_prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  let single := paired.rows.holeAreas value + paired.ending.holeAreas value
  (single +
    Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value paired.rows.word)
      (-Topology.Surface.Sewing.SewingRetraction.wordValue value (paired.reference.hole.liftedBoundary
        owner.lifted.vertices owner.lifted.edges)) +
    paired.ending.exteriorArea value (Topology.Surface.Sewing.SewingRetraction.wordValue value paired.rows.word) +
    Topology.Mesh.RetracingWords.AreaTerm.total value ordered.prepared.compiled.areaTerms -
    owner.lifted.edges.chainArea owner.lifted.vertices value owner.base.bank.exterior sheet) -
  (single + single +
    Geometry.Grid.CellBoundary.sumValues (fun hole => Topology.Mesh.RetracingWords.wordArea value (hole.liftedBoundary
      owner.lifted.vertices owner.lifted.edges)) owner.base.faces.holes)

/-- The mixed corrected surface residual is the gap plus the hole aggregate
term plus the stem aggregate term. -/
theorem surfaceResidual_eq_gap_add (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared value =
      mixedSurfaceGap prepared value + (mixedHoleSum prepared value + mixedStemSum prepared value) := by
  rw [prepared.surfaceResidual_split]
  unfold mixedSurfaceGap mixedHoleSum mixedStemSum
  ring1

/-- The gap is exactly the base A/B pairing minus the two aggregate terms.
This makes the remaining obligation precise: the gap certificate is
equivalent to a bound on `prepared.pairing`, i.e. the §1 physical-boundary
gate, once the two aggregates are paid. -/
theorem mixedSurfaceGap_eq_pairing (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    mixedSurfaceGap prepared value =
      prepared.pairing value - (mixedHoleSum prepared value + mixedStemSum prepared value) := by
  have equal : prepared.pairing value =
      mixedSurfaceGap prepared value + (mixedHoleSum prepared value + mixedStemSum prepared value) :=
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.pairing_eq_surfaceResidual prepared value anti).trans
      (surfaceResidual_eq_gap_add prepared value)
  rw [equal]
  ring1

/-- The chain area and the connector terms cancel inside the gap: it is the
reference cross, the terminal exterior area, the branch word area and the
hole terms. -/
theorem mixedSurfaceGap_eq_areas (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    mixedSurfaceGap prepared value =
      Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value paired.rows.word)
        (-Topology.Surface.Sewing.SewingRetraction.wordValue value (paired.reference.hole.liftedBoundary
          owner.lifted.vertices owner.lifted.edges)) +
      paired.ending.exteriorArea value (Topology.Surface.Sewing.SewingRetraction.wordValue value paired.rows.word) -
      Topology.Mesh.RetracingWords.wordArea value ordered.word -
      (paired.rows.holeAreas value + paired.ending.holeAreas value) -
      Geometry.Grid.CellBoundary.sumValues (fun hole => Topology.Mesh.RetracingWords.wordArea value (hole.liftedBoundary
        owner.lifted.vertices owner.lifted.edges)) owner.base.faces.holes := by
  rw [mixedSurfaceGap, ordered.exterior_areas value anti]
  ring1

/-- The gap certificate follows from the base A/B pairing bound and the two
aggregates. The pairing bound is the §1 physical-boundary gate. -/
theorem gapBound_of_pairing (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge)
    {pairingTarget holeTarget stemTarget : Fraction.Rational}
    (pairingBound : Data.Gaussian.Norm.Basic.normSq (prepared.pairing value) < pairingTarget)
    (holeBound : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared value) < holeTarget)
    (stemBound : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared value) < stemTarget) :
    Data.Gaussian.Norm.Basic.normSq (mixedSurfaceGap prepared value) < 2 * (pairingTarget + 2 * (holeTarget +
      stemTarget)) := by
  rw [mixedSurfaceGap_eq_pairing prepared value anti]
  have inner : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared value + mixedStemSum prepared value) <
      2 * (holeTarget + stemTarget) :=
    (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct holeBound stemBound))
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct pairingBound inner))

/-- Algebraic assembly of the mixed residual from the three typed pieces.
The gap hypothesis is the value-generic ending/exterior obligation; the hole
and stem hypotheses are exactly the conclusions of the two value-generic
aggregates. -/
theorem surfaceResidual_bound (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    {stemTarget holeTarget gapTarget : Fraction.Rational}
    (stemBound : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared value) < stemTarget)
    (holeBound : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared value) < holeTarget)
    (gapBound : Data.Gaussian.Norm.Basic.normSq (mixedSurfaceGap prepared value) < gapTarget) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual
      prepared value) < 2 * (gapTarget + 2 * (holeTarget + stemTarget)) := by
  rw [surfaceResidual_eq_gap_add prepared value]
  have inner : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared value + mixedStemSum prepared value) <
      2 * (holeTarget + stemTarget) :=
    (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct holeBound stemBound))
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct gapBound inner))

end Purelib.Curves.Hyperelliptic.Integration.Surface.MixedSurfaceResidual
