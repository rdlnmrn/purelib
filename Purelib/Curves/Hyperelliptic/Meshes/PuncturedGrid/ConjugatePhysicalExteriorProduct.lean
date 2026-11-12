module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior
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
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalExteriorProduct
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
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
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Data.Gaussian.Norm

public section

/-! The conjugated terminal product has the same quantitative bound as the
holomorphic product, using the original retained total estimates. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugatePhysicalExteriorProduct

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
open Purelib.Data.Rat
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal (resplitExteriorFactor
  resplitPhysicalExteriorCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest (factorBound
  factor_bounded)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalExteriorProduct (product_readback)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : FramedPuncturedGrid curve branches higher}
  {lifted : Riemann.Meshes.LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted} {sheet : Fin
    2}
  {ordered : Ordered bank
    sheet} {paired : OrderedBranchPairs.Ordered.Paired ordered} {current :
    Riemann.Meshes.LiftedPuncturedGrid next}
  (included : Polynomial.Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)
  {domains : FaceDomainBank current.frames
    next.faces.regulars}

/-- Conjugation commutes with the finite Gaussian edge-word value. -/
private theorem word_conj {count : Nat} (value : OrientedEdge count → Canonical)
    (word : List (OrientedEdge count)) :
    SewingRetraction.wordValue (fun edge => Data.Gaussian.Basic.conj (value edge)) word =
      Data.Gaussian.Basic.conj (SewingRetraction.wordValue value word) := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      change Data.Gaussian.Basic.conj (value edge) + SewingRetraction.wordValue _ rest =
        Data.Gaussian.Basic.conj (value edge + SewingRetraction.wordValue value rest)
      rw [ih, Data.Gaussian.Basic.conj_add]

/-- Conjugation commutes with the retained resplit exterior factor for either branch-ending parity. -/
private theorem factor_conj (newSheet : Fin 2)
    (value : OrientedEdge current.vertices.count → Canonical) :
    ExteriorTotal.resplitExteriorFactor (paired := paired) included
      current.edges current.vertices newSheet
        (fun edge => Data.Gaussian.Basic.conj (value edge)) =
      Data.Gaussian.Basic.conj
        (ExteriorTotal.resplitExteriorFactor (paired := paired)
        included current.edges current.vertices newSheet value) := by
  unfold ExteriorTotal.resplitExteriorFactor
  cases paired.split.ending with
  | odd index => rfl
  | even firstIndex lastIndex =>
    dsimp only
    rw [← bank.resplit_pairs_value included current.edges current.vertices,
      ← bank.resplit_pairs_value included current.edges current.vertices,
      word_conj,
        word_conj,
        Data.Gaussian.Basic.conj_add]

/-- The conjugated physical exterior product satisfies the original retained factor and total bounds.

Both differential readings use the supplied paid magnitude banks; conjugation preserves the first component's
squared-norm estimate. -/
theorem conjugate_product_bound {i j : Fin genus}
    (first : FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i))
    (second : FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j))
    (newSheet : Fin 2) {stage : Nat}
    {leftBank : FacePrimitiveBank (PeriodMatrix.standardDifferential i) stage domains}
    {rightBank : FacePrimitiveBank (PeriodMatrix.standardDifferential j) stage domains}
    (left : TriangleReadings leftBank current.mesh) (right :
      TriangleReadings rightBank current.mesh)
    (firstLater : first.index ≤ stage) (secondLater : second.index ≤ stage)
    {tolerance : Rational}
    (leftSmall : Basic.normSq (current.edges.chainValue current.vertices
      (CanonicalEdgeValues.edgeValuation current.mesh left.values)
      (included.resplit base.bank.exterior (FramedBranchCellBank.baseMember base.bank)) newSheet) ≤ tolerance)
    (rightSmall : Basic.normSq (current.edges.chainValue current.vertices
      (CanonicalEdgeValues.edgeValuation current.mesh right.values)
      (included.resplit base.bank.exterior (FramedBranchCellBank.baseMember base.bank)) newSheet) ≤ tolerance) :
    Basic.normSq (BilinearPolarization.extract (fun coefficient =>
      ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
      included current.edges current.vertices newSheet
      (BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation
        current.mesh left.values edge))
        (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient))) ≤
      4 * max (PolarizedExteriorRequest.factorBound (paired := paired) included first)
        (PolarizedExteriorRequest.factorBound (paired := paired) included second) * tolerance := by
  rw [PhysicalExteriorProduct.product_readback,
    factor_conj]
  have conjugateTotal := word_conj
    (CanonicalEdgeValues.edgeValuation current.mesh left.values)
    (current.edges.indexedEdges current.vertices (included.resplit base.bank.exterior (FramedBranchCellBank.baseMember
      base.bank)) newSheet)
  have canonicalBound {point : Canonical} {limit : Rational}
      (h : Basic.normSq point ≤ limit) :
      Canonical.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [← Basic.normSq_eq_canonical]
    exact h
  rw [Basic.normSq_eq_canonical]
  exact PrimitivePoint.area_bound
    ⟨canonicalBound (((Basic.normSq_conj _).trans_le (PolarizedExteriorRequest.factor_bounded
      included first newSheet left firstLater)).trans (Fraction.Order.Basic.le_max_left
      (PolarizedExteriorRequest.factorBound (paired := paired) included first) (PolarizedExteriorRequest.factorBound
      (paired := paired) included second))),
      canonicalBound ((PolarizedExteriorRequest.factor_bounded included second newSheet right secondLater).trans
        (Fraction.Order.Basic.le_max_right (PolarizedExteriorRequest.factorBound (paired := paired) included first)
        (PolarizedExteriorRequest.factorBound (paired := paired) included second)))⟩
    ⟨canonicalBound ((congrArg Basic.normSq conjugateTotal).trans_le
      ((Basic.normSq_conj _).trans_le leftSmall)), canonicalBound rightSmall⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugatePhysicalExteriorProduct
