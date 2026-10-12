module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
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
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

public import Purelib.Curves.Hyperelliptic.Integration.Surface.MixedSurfaceResidual
public import Purelib.Topology.Surface.Chord.ValueChordLinearity
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
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
# The geometric terms of the polarized ordered gap

Expand the opposite-direction differences before estimating them. All areas
below belong to the same retained ordered bank. These identities retain the
terminal and reference corrections; they do not assert their decay.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.Surface.PolarizedSurfaceGap

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract
  extract_congr imaginary)
open Purelib.Curves.Hyperelliptic.Integration.Surface.MixedSurfaceResidual
open Purelib.Topology.Surface.Chord.ValueChordLinearity (crossWedge extract_surfaceResidual_mixValues)

namespace BilinearPolarization

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization
/-- Only the opposite-direction differences need be small. The common
Hermitian diagonal is cancelled before this squared-norm estimate. -/
theorem extract_normSq_le_differences (value : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract value) ≤ (1 / 8 :
      Fraction.Rational) *
      (Data.Gaussian.Norm.Basic.normSq (value 1 - value (-1)) +
        Data.Gaussian.Norm.Basic.normSq (value imaginary - value (-imaginary))) := by
  have quarter : Data.Gaussian.Norm.Basic.normSq (⟨1 / 4, 0⟩ : Gaussian.Basic.Canonical) = (1 / 16 :
    Fraction.Rational) := by decide
  have unit : Data.Gaussian.Norm.Basic.normSq (imaginary : Gaussian.Basic.Canonical) = 1 := by decide
  unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
  rw [Gaussian.Norm.Basic.normSq_mul, quarter]
  have bound := Gaussian.Norm.Bounds.normSq_sub_le_two (value 1 - value (-1))
    (imaginary * (value imaginary - value (-imaginary)))
  rw [Gaussian.Norm.Basic.normSq_mul, unit, _root_.one_mul] at bound
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bound
    (by decide : (0 : Fraction.Rational) ≤ 1 / 16)).trans_eq (by
      rw [← _root_.mul_assoc,
        show (1 / 16 : Fraction.Rational) * 2 = 1 / 8 by decide])

/-- Allocate the sum of the two squared difference errors below eight times
the requested squared determinant error. -/
theorem extract_normSq_lt_of_differences (value : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical)
    {requested : Fraction.Rational}
    (paid : Data.Gaussian.Norm.Basic.normSq (value 1 - value (-1)) +
      Data.Gaussian.Norm.Basic.normSq (value imaginary - value (-imaginary)) < 8 * requested) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract value) < requested :=
  (extract_normSq_le_differences value).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 1 / 8)
      paid).trans_eq (by
        rw [← _root_.mul_assoc,
          show (1 / 8 : Fraction.Rational) * 8 = 1 by decide, _root_.one_mul]))

end BilinearPolarization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin
    2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}

/-- Polarization distributes across the geometric gap, with the branch-word
and both kinds of hole area retaining their negative signs. -/
theorem extract_mixedSurfaceGap_eq_areas (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared
  paired)
    (values : Gaussian.Basic.Canonical → OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ coefficient edge, values coefficient edge.reverse = -values coefficient edge) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      mixedSurfaceGap prepared (values coefficient)) =
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Path.BoundaryRibbon.area
        (Topology.Surface.Sewing.SewingRetraction.wordValue (values coefficient) paired.rows.word)
        (-Topology.Surface.Sewing.SewingRetraction.wordValue (values coefficient)
          (paired.reference.hole.liftedBoundary owner.lifted.vertices owner.lifted.edges))) +
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        paired.ending.exteriorArea (values coefficient)
        (Topology.Surface.Sewing.SewingRetraction.wordValue (values coefficient) paired.rows.word)) -
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Topology.Mesh.RetracingWords.wordArea (values coefficient) ordered.word) -
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        paired.rows.holeAreas (values coefficient) +
        paired.ending.holeAreas (values coefficient)) -
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Geometry.Grid.CellBoundary.sumValues (fun hole => Topology.Mesh.RetracingWords.wordArea (values coefficient)
        (hole.liftedBoundary owner.lifted.vertices owner.lifted.edges)) owner.base.faces.holes) := by
  have expanded := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun
    coefficient =>
    mixedSurfaceGap_eq_areas prepared (values coefficient) (anti coefficient))
  refine expanded.trans ?_
  unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
  ring1

/-- The extracted residual consists of the extracted geometric gap and the
paid hole and stem defects, with no separate diagonal-energy hypothesis. -/
theorem extract_surfaceResidual_eq_gap_add (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared
  paired)
    (values : Gaussian.Basic.Canonical → OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared (values coefficient)) =
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        mixedSurfaceGap prepared (values coefficient)) +
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        mixedHoleSum prepared (values coefficient)) +
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
          mixedStemSum prepared (values coefficient))) := by
  have expanded := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun
    coefficient =>
    surfaceResidual_eq_gap_add prepared (values coefficient))
  refine expanded.trans ?_
  unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
  ring1

/-- The decomposition reads back to the actual ordered cross determinant of
the two face readings, rather than to a different cycle presentation. -/
theorem crossWedge_eq_extracted_gap_add {prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared
  paired}
    (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared)
    (leftValues rightValues : Fin owner.lifted.mesh.triangles.length →
      Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    crossWedge prepared leftValues rightValues =
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        mixedSurfaceGap prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues coefficient))) +
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        mixedHoleSum prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues coefficient))) +
       Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
         mixedStemSum prepared (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (Meshes.PuncturedGrid.Readings.EdgeMagnitude.mixValues (owner := owner) leftValues rightValues coefficient))))
            :=
  (extract_surfaceResidual_mixValues cut).symm.trans
    (extract_surfaceResidual_eq_gap_add prepared _)

end Purelib.Curves.Hyperelliptic.Integration.Surface.PolarizedSurfaceGap
