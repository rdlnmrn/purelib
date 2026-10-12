module
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! The remaining terminal correction is a polarized product of a bounded
ordered prefix factor and the actual original exterior total. -/
section

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal (resplitExteriorFactor
  resplitPhysicalExteriorCorrection)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {current :
    Meshes.LiftedPuncturedGrid next}
  (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames next.faces.regulars}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalExteriorProduct

/-- The original physical exterior correction polarizes to the paired area of its retained prefix factor and literal
exterior total. -/
theorem product_readback (newSheet : Fin 2)
    (first second : Topology.Polygon.Stokes.OrientedEdge current.vertices.count → Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
      included current.edges current.vertices newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient))
        =
    Topology.Polygon.Stokes.edgeArea (⟨resplitExteriorFactor (paired := paired) included current.edges current.vertices
      newSheet first,
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor (paired := paired) included
        current.edges current.vertices newSheet second⟩ : Topology.Polygon.Stokes.PrimitivePoint)
      (⟨current.edges.chainValue current.vertices first (included.resplit base.bank.exterior
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet,
        current.edges.chainValue current.vertices second (included.resplit base.bank.exterior
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet⟩ :
          Topology.Polygon.Stokes.PrimitivePoint) := open Purelib.Integration in by
  have equal (coefficient : Gaussian.Basic.Canonical) :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factor_mix (paired :=
    paired) included newSheet first second coefficient
  have scalar (coefficient : Gaussian.Basic.Canonical) :
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
        included current.edges current.vertices newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient) =
      Path.BoundaryRibbon.area
        (Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor
          (paired := paired) included current.edges current.vertices newSheet first) +
          coefficient * Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor (paired :=
            paired) included current.edges current.vertices newSheet second)
        (Data.Gaussian.Basic.conj (current.edges.chainValue current.vertices first
          (included.resplit base.bank.exterior
            (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet) +
          coefficient * current.edges.chainValue current.vertices second
            (included.resplit base.bank.exterior
              (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet)
              := by
    rw [Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection, equal coefficient,
      SquareRoot.Grid.RootEdgeBank.chainValue,
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix]
    rfl
  have readback := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr scalar
  exact readback.trans (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_area _ _
    _ _)

/-- The original exterior product is bounded by four times the larger retained factor bound times the common exterior
tolerance. -/
theorem product_bound {i j : Fin genus}
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential i))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential j))
    (newSheet : Fin 2) {stage : Nat}
    {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential i) stage domains}
    {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential j) stage domains}
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (right
      : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (firstLater : first.index ≤ stage) (secondLater : second.index ≤ stage)
    {tolerance : Fraction.Rational}
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (current.edges.chainValue current.vertices
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values)
      (included.resplit base.bank.exterior
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet) ≤
        tolerance)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (current.edges.chainValue current.vertices
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values)
      (included.resplit base.bank.exterior
        (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet) ≤
        tolerance) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
      included current.edges current.vertices newSheet
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)))
        ≤
      4 * max (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound
        (paired := paired) included first)
        (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
          paired) included second) * tolerance := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.PhysicalExteriorProduct.product_readback]
  have canonicalBound {point : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Norm.Basic.normSq point ≤ limit) :
      Gaussian.Basic.Canonical.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound
    ⟨canonicalBound
      ((Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factor_bounded included
      first newSheet left firstLater).trans (Data.Rat.Fraction.Order.Basic.le_max_left
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) included first)
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) included second))),
      canonicalBound
        ((Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factor_bounded
        included second newSheet right secondLater).trans (Data.Rat.Fraction.Order.Basic.le_max_right
        (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
        paired) included first)
        (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
        paired) included second)))⟩
    ⟨canonicalBound leftSmall, canonicalBound rightSmall⟩

/-- Flattening the original ordered pairs gives exactly twice their retained list length. -/
private theorem pair_length {Alpha : Type} (pairs : List (Alpha × Alpha)) :
    (pairs.flatMap (fun pair => [pair.1, pair.2])).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      change ((rest.flatMap (fun pair => [pair.1, pair.2])).length + 1) + 1 = 2 * (rest.length + 1)
      rw [ih]
      omega

/-- Odd polynomial degree forces the odd ending of the actual ordered
branch split, so its terminal factor is exactly zero. -/
theorem factor_zero_of_odd (degree : curve.polynomial.natDegree = 2 * genus + 1)
    (newSheet : Fin 2) (value : Topology.Polygon.Stokes.OrientedEdge current.vertices.count → Gaussian.Basic.Canonical)
      :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor (paired := paired) included
      current.edges current.vertices newSheet value = 0 := by
  have labels := ((Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.labels_length ordered).trans
    branches.count_eq).trans degree
  have count := congrArg List.length paired.split.labels_eq
  rw [Append.length_append, Hyperelliptic.Meshes.PuncturedGrid.PhysicalExteriorProduct.pair_length,
    paired.split.count_eq] at count
  unfold Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor
  cases ending : paired.split.ending with
  | odd reference => rfl
  | even reference last =>
      rw [ending] at count
      change ordered.prepared.labels.length = 2 * genus + 2 at count
      omega

/-- Odd polynomial degree makes the original polarized physical exterior product exactly zero. -/
theorem product_zero_of_odd (degree : curve.polynomial.natDegree = 2 * genus + 1)
    (newSheet : Fin 2) (first second : Topology.Polygon.Stokes.OrientedEdge current.vertices.count →
      Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
      included current.edges current.vertices newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient))
        = 0 := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.PhysicalExteriorProduct.product_readback,
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalExteriorProduct.factor_zero_of_odd included degree,
    Hyperelliptic.Meshes.PuncturedGrid.PhysicalExteriorProduct.factor_zero_of_odd included degree]
  change Topology.Polygon.Stokes.edgeArea Topology.Polygon.Stokes.PrimitivePoint.zero _ = 0
  unfold Topology.Polygon.Stokes.edgeArea Topology.Polygon.Stokes.PrimitivePoint.zero
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalExteriorProduct

end
