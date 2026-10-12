module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

public import Purelib.Curves.Hyperelliptic.Integration.Surface.MixedSurfaceResidual
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PolarizationBound
public import Purelib.Topology.Surface.Chord.ValueChordLinearity
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueHoleRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueStemRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

public section

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families (Domains MagnitudeBank PrimitiveBank
  TriangleCache Source Sources Nonloop)

/-!
# Mixed ordered first-bilinear bound

The corrected route's endpoint. A `MixedResidualPiece` certifies the three
typed pieces of one mixed surface residual: the value-generic stem aggregate
term, the value-generic hole aggregate term, and the ending/exterior gap.
Four pieces, at `c = 1, -1, i, -i`, feed
`Purelib.Riemann.Periods.GridPairedBilinearIdentity.BilinearPolarization.bilinearResidual_normSq_le` and bound the
ordered
first-bilinear determinant.

New consumers should use this value-parameterized API (`EdgeMagnitude`,
`MixedChartAreaRequest` and the `Value*`/`Mixed*` modules); the legacy
`FaceMagnitudeBank` single-differential chain is retained only for its
existing callsites.
-/

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Ordered.Paired.Prepared (ValueStemAggregateRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueHoleRequests.Ordered.Paired.Prepared
  (ValueHoleAggregateRequest)
open Purelib.Curves.Hyperelliptic.Integration.Surface.MixedSurfaceResidual (mixedStemSum mixedHoleSum mixedSurfaceGap)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open Purelib.Topology.Surface.Chord.ValueChordLinearity

namespace Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}

/-- The three certified pieces of one mixed surface residual at a common
bound. The stem and hole pieces are the aggregate conclusions; the gap piece
is the retained ending/exterior obligation. -/
structure MixedResidualPiece (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) (bound : Fraction.Rational) where
  /-- The value-generic stem aggregate meets the common strict bound. -/ stemBound : Data.Gaussian.Norm.Basic.normSq
    (mixedStemSum prepared value) < bound
  /-- The value-generic hole aggregate meets the common strict bound. -/ holeBound : Data.Gaussian.Norm.Basic.normSq
    (mixedHoleSum prepared value) < bound
  /-- The retained ending and exterior gap meets the same common strict bound. -/ gapBound :
    Data.Gaussian.Norm.Basic.normSq (mixedSurfaceGap prepared value) < bound

namespace MixedResidualPiece

variable {prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired} {value : OrientedEdge
  owner.lifted.vertices.count → Gaussian.Basic.Canonical}
  {bound : Fraction.Rational}

/-- The retained stem, hole and geometric-gap bounds give a strict tenfold bound on their complete mixed surface
residual. -/
theorem surfaceResidual_bound (piece : MixedResidualPiece (owner := owner) prepared value bound) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual
      prepared value) < 10 * bound :=
  (Hyperelliptic.Integration.Surface.MixedSurfaceResidual.surfaceResidual_bound prepared value piece.stemBound
    piece.holeBound piece.gapBound).trans_eq
    (by ring1)

end MixedResidualPiece

/-- Four mixed residual certificates at the four polarization directions
bound the ordered first-bilinear determinant. -/
theorem bilinearResidual_bound (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (first second : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) {bound : Fraction.Rational}
    (one : MixedResidualPiece (owner := owner) prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second 1) bound)
    (negOne : MixedResidualPiece (owner := owner) prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second (-1)) bound)
    (im : MixedResidualPiece (owner := owner) prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary) bound)
    (negIm : MixedResidualPiece (owner := owner) prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
        (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)) bound) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual
      prepared first second) ≤ 160 * bound := by
  have oneBound := one.surfaceResidual_bound.le
  have negOneBound := negOne.surfaceResidual_bound.le
  have imBound := im.surfaceResidual_bound.le
  have negImBound := negIm.surfaceResidual_bound.le
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at oneBound negOneBound imBound negImBound
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.bilinearResidual_normSq_le
    prepared first second
    oneBound negOneBound imBound negImBound).trans_eq (by ring1)

end Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

namespace Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}
  {domains : Domains owner}

/-- The value-generic stem and hole aggregates plus the gap certificate
assemble the three pieces of one mixed residual certificate. The only input
not supplied by the aggregates is the gap certificate, i.e. the §1
physical-boundary gate. -/
theorem mixedResidualPiece_of_aggregates (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared
  paired)
    {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}
    {leftFixed : MagnitudeBank owner domains leftDifferential}
    {rightFixed : MagnitudeBank owner domains rightDifferential}
    {coefficient : Gaussian.Basic.Canonical} {bound : Fraction.Rational}
    (stem : ValueStemAggregateRequest (owner := owner) prepared leftFixed rightFixed coefficient bound)
    (hole : ValueHoleAggregateRequest (owner := owner) prepared leftFixed rightFixed coefficient bound)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank)
    (rightReadings : TriangleCache owner rightDifferential stage domains rightBank)
    (stemLater : stem.index ≤ stage) (holeLater : hole.index ≤ stage)
    (gapBound : Data.Gaussian.Norm.Basic.normSq (mixedSurfaceGap prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values
          coefficient))) < bound) :
    MixedResidualPiece (owner := owner) prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
      owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values
          coefficient)) bound :=
  ⟨stem.accurate leftReadings rightReadings stemLater,
    hole.accurate leftReadings rightReadings holeLater, gapBound⟩

end Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

namespace Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

/-- Four mixed residual certificates at the four polarization directions bound
the cross determinant of the two ordered word readings. -/
theorem crossWedge_normSq_le (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length →
      Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}
    {bound : Fraction.Rational}
    (one : MixedResidualPiece (owner := owner) prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues 1)) bound)
    (negOne : MixedResidualPiece (owner := owner) prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues (-1))) bound)
    (im : MixedResidualPiece (owner := owner) prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)) bound)
    (negIm : MixedResidualPiece (owner := owner) prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))) bound) :
    Data.Gaussian.Norm.Basic.normSq (crossWedge prepared leftValues rightValues) ≤ 160 * bound := by
  have extracted := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_normSq_le
    (value := fun coefficient : Gaussian.Basic.Canonical =>
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues coefficient)))
    (one := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues 1)))
    (negOne := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues (-1))))
    (im := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)))
    (negIm := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))))
    rfl rfl rfl rfl
  rw [extract_surfaceResidual_mixValues cut] at extracted
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  refine extracted.trans ?_
  have oneB := one.surfaceResidual_bound.le
  have negOneB := negOne.surfaceResidual_bound.le
  have imB := im.surfaceResidual_bound.le
  have negImB := negIm.surfaceResidual_bound.le
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at oneB negOneB imB negImB
  have sumBound : Gaussian.Basic.Canonical.normSq
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues 1))) +
      Gaussian.Basic.Canonical.normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual
        prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues (-1)))) +
      Gaussian.Basic.Canonical.normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual
        prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
          Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))) +
      Gaussian.Basic.Canonical.normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual
        prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
          (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)))) ≤
      4 * (10 * bound) := by
    calc
      _ ≤ ((10 * bound + 10 * bound) + 10 * bound) + 10 * bound :=
        Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.add_le_add_direct
          (Fraction.Order.Arithmetic.add_le_add_direct oneB negOneB) imB) negImB
      _ = 4 * (10 * bound) := by ring1
  calc
    4 * (Gaussian.Basic.Canonical.normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual
      prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
          (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues 1))) +
        Gaussian.Basic.Canonical.normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual
          prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
          (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues (-1)))) +
        Gaussian.Basic.Canonical.normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual
          prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
          (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
            Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))) +
        Gaussian.Basic.Canonical.normSq (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual
          prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
          (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
            (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))))) ≤
        4 * (4 * (10 * bound)) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound (by decide)
    _ = 160 * bound := by ring1

end Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

namespace Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

/-- The existing four-direction polarization bound, restated for the cross
determinant of the two ordered word readings. -/
theorem crossWedge_bound_of_bilinear (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared
  paired)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length →
      Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}
    {bound : Fraction.Rational}
    (one : MixedResidualPiece (owner := owner) prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) 1) bound)
    (negOne : MixedResidualPiece (owner := owner) prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) (-1))
        bound)
    (im : MixedResidualPiece (owner := owner) prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary) bound)
    (negIm : MixedResidualPiece (owner := owner) prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
        (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)) bound) :
    Data.Gaussian.Norm.Basic.normSq (crossWedge prepared leftValues rightValues) ≤ 160 * bound := by
  rw [← bilinearResidual_edgeValuation_eq_crossWedge]
  exact bilinearResidual_bound prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
    owner.lifted.mesh leftValues)
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) one negOne im
      negIm

end Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

namespace Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Rat.Fraction.Order.Arithmetic (add_le_add_direct mul_le_mul_of_nonneg_left_direct
  mul_le_mul_direct mul_nonneg_direct)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

/-- The mixed gap is bounded by the base A/B pairing bound and the two
aggregate bounds. -/
theorem mixedSurfaceGap_normSq_le (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge)
    {pairingBound holeBound stemBound : Fraction.Rational}
    (pairingLe : Data.Gaussian.Norm.Basic.normSq (prepared.pairing value) ≤ pairingBound)
    (holeLe : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared value) ≤ holeBound)
    (stemLe : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared value) ≤ stemBound) :
    Data.Gaussian.Norm.Basic.normSq (mixedSurfaceGap prepared value) ≤ 2 * (pairingBound + 2 * (holeBound +
      stemBound)) := by
  rw [Hyperelliptic.Integration.Surface.MixedSurfaceResidual.mixedSurfaceGap_eq_pairing prepared value anti]
  have inner : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared value + mixedStemSum prepared value) ≤
      2 * (holeBound + stemBound) :=
    (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct holeLe
        stemLe) (by decide))
  exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct pairingLe
      inner) (by decide))

/-- The mixed gap is bounded by the retained word-value magnitudes and the two
aggregate bounds. This discharges the gap from magnitude data alone, leaving
only the accuracy question, not existence. -/
theorem mixedSurfaceGap_normSq_le_of_magnitudes (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) {magnitude : Fraction.Rational}
    (nonnegative : 0 ≤ magnitude)
    (aBound : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.aWord index)) ≤ magnitude)
    (bBound : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.bWord index)) ≤ magnitude)
    {holeBound stemBound : Fraction.Rational}
    (holeLe : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared value) ≤ holeBound)
    (stemLe : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared value) ≤ stemBound) :
    Data.Gaussian.Norm.Basic.normSq (mixedSurfaceGap prepared value) ≤
      2 * ((genus : Fraction.Rational) ^ 2 * (4 * magnitude ^ 2) + 2 * (holeBound + stemBound)) :=
  mixedSurfaceGap_normSq_le prepared value anti
    (pairing_normSq_le prepared value nonnegative aBound bBound) holeLe stemLe

end Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

namespace Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

/-- Strict form of the magnitude pairing bound, with one unit of slack. -/
theorem pairing_lt_of_magnitudes (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) {magnitude : Fraction.Rational}
    (nonnegative : 0 ≤ magnitude)
    (aBound : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.aWord index)) ≤ magnitude)
    (bBound : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.bWord index)) ≤ magnitude) :
    Data.Gaussian.Norm.Basic.normSq (prepared.pairing value) < (genus : Fraction.Rational) ^ 2 * (4 * magnitude ^ 2)
      + 1 :=
  (pairing_normSq_le prepared value nonnegative aBound bBound).trans_lt (by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
      (by decide : (0 : Fraction.Rational) < 1) ((genus : Fraction.Rational) ^ 2 * (4 * magnitude ^ 2))
    simpa only [add_zero] using shifted)

/-- Strict gap certificate from the word magnitudes and the two aggregate
strict bounds. -/
theorem mixedSurfaceGap_lt_of_magnitudes (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared
  paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) {magnitude : Fraction.Rational}
    (nonnegative : 0 ≤ magnitude)
    (aBound : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.aWord index)) ≤ magnitude)
    (bBound : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.bWord index)) ≤ magnitude)
    {holeTarget stemTarget : Fraction.Rational}
    (holeLt : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared value) < holeTarget)
    (stemLt : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared value) < stemTarget) :
    Data.Gaussian.Norm.Basic.normSq (mixedSurfaceGap prepared value) <
      2 * (((genus : Fraction.Rational) ^ 2 * (4 * magnitude ^ 2) + 1) + 2 * (holeTarget + stemTarget)) :=
  Hyperelliptic.Integration.Surface.MixedSurfaceResidual.gapBound_of_pairing prepared value anti
    (pairing_lt_of_magnitudes prepared value nonnegative aBound bBound) holeLt stemLt

end Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

namespace Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

/-- The magnitude of the mixed word values at coefficient `coefficient`. -/
@[expose] def mixedWordMagnitude (leftMagnitude rightMagnitude coefficient : Fraction.Rational) : Fraction.Rational :=
  2 * (leftMagnitude + coefficient * rightMagnitude)

/-- The common bound produced by a magnitude-based mixed residual certificate. -/
@[expose] def magnitudePieceBound (genus : Nat) (magnitude holeTarget stemTarget : Fraction.Rational) :
  Fraction.Rational :=
  max (2 * (((genus : Fraction.Rational) ^ 2 * (4 * magnitude ^ 2) + 1) + 2 * (holeTarget + stemTarget)))
    (max holeTarget stemTarget)

/-- A complete mixed residual certificate at the mixed value, assembled from
the word-value magnitudes and the two aggregate strict bounds. This is the
existence half of `MixedResidualPiece.gapBound`; the retained accuracy is
exactly the magnitude and aggregate accuracy already supplied by the
value-generic requests. -/
theorem mixedResidualPiece_of_magnitudes (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared
  paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) {magnitude : Fraction.Rational}
    (nonnegative : 0 ≤ magnitude)
    (aBound : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.aWord index)) ≤ magnitude)
    (bBound : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.bWord index)) ≤ magnitude)
    {holeTarget stemTarget : Fraction.Rational}
    (holeLt : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared value) < holeTarget)
    (stemLt : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared value) < stemTarget) :
    MixedResidualPiece (owner := owner) prepared value (magnitudePieceBound genus magnitude holeTarget stemTarget) :=
  ⟨stemLt.trans_le ((Fraction.Order.Basic.le_max_right holeTarget stemTarget).trans (Fraction.Order.Basic.le_max_right _
    _)),
    holeLt.trans_le ((Fraction.Order.Basic.le_max_left holeTarget stemTarget).trans (Fraction.Order.Basic.le_max_right _
      _)),
    (mixedSurfaceGap_lt_of_magnitudes prepared value anti nonnegative aBound bBound holeLt stemLt).trans_le
      (Fraction.Order.Basic.le_max_left _ _)⟩

end Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

namespace Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

/-- A complete mixed residual certificate at the mixed value, assembled from
the two readings' word magnitudes and the two aggregate strict bounds. -/
theorem mixedResidualPiece_mixValues (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank
  prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length →
      Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical) {leftMagnitude rightMagnitude : Fraction.Rational}
    (leftNonnegative : 0 ≤ leftMagnitude) (rightNonnegative : 0 ≤ rightMagnitude)
    (aLeft : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
        (prepared.aWord index)) ≤ leftMagnitude)
    (bLeft : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
        (prepared.bWord index)) ≤ leftMagnitude)
    (aRight : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
        (prepared.aWord index)) ≤ rightMagnitude)
    (bRight : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
        (prepared.bWord index)) ≤ rightMagnitude)
    {holeTarget stemTarget : Fraction.Rational}
    (holeLt : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues coefficient))) <
          holeTarget)
    (stemLt : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues coefficient))) <
          stemTarget) :
    MixedResidualPiece (owner := owner) prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
      owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues coefficient))
      (magnitudePieceBound genus
        (mixedWordMagnitude leftMagnitude rightMagnitude (Data.Gaussian.Norm.Basic.normSq coefficient)) holeTarget
          stemTarget) :=
  mixedResidualPiece_of_magnitudes prepared _ (fun edge =>
    Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh _ edge)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg leftNonnegative (Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Norm.Basic.normSq_nonneg
        coefficient) rightNonnegative)))
    (aWord_mixValues_magnitude cut coefficient aLeft aRight)
    (bWord_mixValues_magnitude cut coefficient bLeft bRight) holeLt stemLt

end Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

namespace Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

/-- The Gaussian imaginary unit has squared norm one. -/
private theorem normSq_imaginary :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary :
      Gaussian.Basic.Canonical) = 1 := by decide

/-- The negative Gaussian imaginary unit has squared norm one. -/
private theorem normSq_neg_imaginary :
    Data.Gaussian.Norm.Basic.normSq
      (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary :
      Gaussian.Basic.Canonical) = 1 := by
  rw [Gaussian.Norm.Basic.normSq_neg, normSq_imaginary]

/-- The Gaussian value minus one has squared norm one. -/
private theorem normSq_neg_one : Data.Gaussian.Norm.Basic.normSq (-1 : Gaussian.Basic.Canonical) = 1 := by
  rw [Gaussian.Norm.Basic.normSq_neg,
    Gaussian.Norm.Basic.normSq_one]

end Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

namespace Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

/-- The ordered determinant is bounded by the two readings' word magnitudes
and the eight directional aggregate bounds. No gap hypothesis remains: the
gap is discharged by `mixedResidualPiece_mixValues`. -/
theorem crossWedge_bound_of_magnitudes (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank
  prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length →
      Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}
    {leftMagnitude rightMagnitude holeTarget stemTarget : Fraction.Rational}
    (leftNonnegative : 0 ≤ leftMagnitude) (rightNonnegative : 0 ≤ rightMagnitude)
    (aLeft : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
        (prepared.aWord index)) ≤ leftMagnitude)
    (bLeft : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
        (prepared.bWord index)) ≤ leftMagnitude)
    (aRight : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
        (prepared.aWord index)) ≤ rightMagnitude)
    (bRight : ∀ index : Fin genus, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
        (prepared.bWord index)) ≤ rightMagnitude)
    (holeOne : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues 1))) < holeTarget)
    (holeNegOne : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues (-1)))) <
          holeTarget)
    (holeIm : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))) < holeTarget)
    (holeNegIm : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)))) < holeTarget)
    (stemOne : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues 1))) < stemTarget)
    (stemNegOne : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues (-1)))) <
          stemTarget)
    (stemIm : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))) < stemTarget)
    (stemNegIm : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)))) < stemTarget) :
    Data.Gaussian.Norm.Basic.normSq (crossWedge prepared leftValues rightValues) ≤
      160 * magnitudePieceBound genus (mixedWordMagnitude leftMagnitude rightMagnitude 1)
        holeTarget stemTarget :=
  crossWedge_normSq_le cut
    (by
      simpa only [Gaussian.Norm.Basic.normSq_one] using
        mixedResidualPiece_mixValues cut 1 leftNonnegative rightNonnegative aLeft bLeft aRight bRight
          holeOne stemOne)
    (by
      simpa only [normSq_neg_one] using
        mixedResidualPiece_mixValues cut (-1) leftNonnegative rightNonnegative aLeft bLeft aRight bRight
          holeNegOne stemNegOne)
    (by
      simpa only [normSq_imaginary] using
        mixedResidualPiece_mixValues cut
          Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary leftNonnegative
          rightNonnegative
          aLeft bLeft aRight bRight holeIm stemIm)
    (by
      simpa only [normSq_neg_imaginary] using
        mixedResidualPiece_mixValues cut
          (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary) leftNonnegative
          rightNonnegative
          aLeft bLeft aRight bRight holeNegIm stemNegIm)

end Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

namespace Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

/-- Strict gap bound from the displayed row-sum pairing bound, with no
magnitude hypothesis: the pairing bound is unconditional. -/
theorem mixedSurfaceGap_lt_rowBound (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared
  paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge)
    {holeTarget stemTarget : Fraction.Rational}
    (holeLt : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared value) < holeTarget)
    (stemLt : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared value) < stemTarget) :
    Data.Gaussian.Norm.Basic.normSq (mixedSurfaceGap prepared value) <
      2 * ((pairingRowBound prepared value + 1) + 2 * (holeTarget + stemTarget)) :=
  Hyperelliptic.Integration.Surface.MixedSurfaceResidual.gapBound_of_pairing prepared value anti (pairing_lt_rowBound
    prepared value) holeLt stemLt

/-- The common bound of a row-bound-based mixed residual certificate. -/
@[expose] def rowBoundPieceBound (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    (holeTarget stemTarget : Fraction.Rational) : Fraction.Rational :=
  max (2 * ((pairingRowBound prepared value + 1) + 2 * (holeTarget + stemTarget)))
    (max holeTarget stemTarget)

/-- A complete mixed residual certificate from the row-sum pairing bound and
the two aggregate strict bounds. No magnitude hypothesis remains, and the
bound retains every row instead of the maximum word magnitude. -/
theorem mixedResidualPiece_of_rowBound (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared
  paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge)
    {holeTarget stemTarget : Fraction.Rational}
    (holeLt : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared value) < holeTarget)
    (stemLt : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared value) < stemTarget) :
    MixedResidualPiece (owner := owner) prepared value (rowBoundPieceBound prepared value holeTarget stemTarget) :=
  ⟨stemLt.trans_le ((Fraction.Order.Basic.le_max_right holeTarget stemTarget).trans (Fraction.Order.Basic.le_max_right _
    _)),
    holeLt.trans_le ((Fraction.Order.Basic.le_max_left holeTarget stemTarget).trans (Fraction.Order.Basic.le_max_right _
      _)),
    (mixedSurfaceGap_lt_rowBound prepared value anti holeLt stemLt).trans_le (Fraction.Order.Basic.le_max_left _ _)⟩

end Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

namespace Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

namespace MixedResidualPiece

/-- A mixed residual certificate can only be weakened to a larger bound. -/
theorem mono {value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical}
    {bound bound' : Fraction.Rational} (piece : MixedResidualPiece (owner := owner) prepared value bound)
    (le : bound ≤ bound') : MixedResidualPiece (owner := owner) prepared value bound' :=
  ⟨piece.stemBound.trans_le le, piece.holeBound.trans_le le, piece.gapBound.trans_le le⟩

end MixedResidualPiece

/-- `rowBoundPieceBound` is monotone in the displayed pairing bound. -/
theorem rowBoundPieceBound_le (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    {holeTarget stemTarget pairingBound : Fraction.Rational}
    (pairingLe : pairingRowBound prepared value ≤ pairingBound) :
    rowBoundPieceBound prepared value holeTarget stemTarget ≤
      max (2 * ((pairingBound + 1) + 2 * (holeTarget + stemTarget)))
        (max holeTarget stemTarget) := by
  unfold rowBoundPieceBound
  apply Fraction.Order.Basic.max_le
  · refine (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct
        (Fraction.Order.Arithmetic.add_le_add_direct pairingLe le_rfl) le_rfl)
      (by decide : (0 : Fraction.Rational) ≤ 2)).trans (Fraction.Order.Basic.le_max_left _ _)
  · exact Fraction.Order.Basic.le_max_right _ _

end Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

namespace Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

/-- The ordered determinant is bounded by a displayed row-sum pairing bound
and the eight aggregate bounds, with no magnitude or gap hypothesis. -/
theorem crossWedge_bound_of_rowBound (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared
  paired) (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length →
      Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}
    {pairingBound holeTarget stemTarget : Fraction.Rational}
    (rowOne : pairingRowBound prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
      owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues 1)) ≤ pairingBound)
    (rowNegOne : pairingRowBound prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
      owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues (-1))) ≤
          pairingBound)
    (rowIm : pairingRowBound prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
      owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)) ≤ pairingBound)
    (rowNegIm : pairingRowBound prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
      owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))) ≤ pairingBound)
    (holeOne : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues 1))) < holeTarget)
    (holeNegOne : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues (-1)))) <
          holeTarget)
    (holeIm : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))) < holeTarget)
    (holeNegIm : Data.Gaussian.Norm.Basic.normSq (mixedHoleSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)))) < holeTarget)
    (stemOne : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues 1))) < stemTarget)
    (stemNegOne : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues (-1)))) <
          stemTarget)
    (stemIm : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))) < stemTarget)
    (stemNegIm : Data.Gaussian.Norm.Basic.normSq (mixedStemSum prepared
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues
        (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)))) < stemTarget) :
    Data.Gaussian.Norm.Basic.normSq (crossWedge prepared leftValues rightValues) ≤ 160 *
      (max (2 * ((pairingBound + 1) + 2 * (holeTarget + stemTarget)))
        (max holeTarget stemTarget)) :=
  crossWedge_normSq_le cut
    (MixedResidualPiece.mono (mixedResidualPiece_of_rowBound prepared _ (fun edge =>
      Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh _ edge) holeOne
        stemOne)
      (rowBoundPieceBound_le prepared _ rowOne))
    (MixedResidualPiece.mono (mixedResidualPiece_of_rowBound prepared _ (fun edge =>
      Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh _ edge) holeNegOne
        stemNegOne)
      (rowBoundPieceBound_le prepared _ rowNegOne))
    (MixedResidualPiece.mono (mixedResidualPiece_of_rowBound prepared _ (fun edge =>
      Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh _ edge) holeIm
        stemIm)
      (rowBoundPieceBound_le prepared _ rowIm))
    (MixedResidualPiece.mono (mixedResidualPiece_of_rowBound prepared _ (fun edge =>
      Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh _ edge) holeNegIm
        stemNegIm)
      (rowBoundPieceBound_le prepared _ rowNegIm))

end Purelib.Curves.Hyperelliptic.Periods.MixedOrderedBilinear
