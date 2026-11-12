module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Polynomial.Geometry.Grid

open Purelib.Topology.Surface.Sewing

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

public section

/-! The same exterior request controls conjugate pairing, retaining the physical exterior. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateExterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal (resplitExteriorFactor
  resplitPhysicalExteriorCorrection resplit_exterior_integral_partition resplit_physical_exterior_difference)

open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest
  (factorBound factorBound_nonnegative factor_bounded factor_mix canonicalWeight RegularRequest)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : OrderedBranchPairs.Ordered.Paired ordered} {current :
    Meshes.LiftedPuncturedGrid next}
  (included : Extension.CoordinateInclusion base.bank.grid next.bank.grid)
  {domains : Face.DomainBanks.FaceDomainBank current.frames next.faces.regulars}

namespace PolarizedExteriorRequest

/-- Conjugating each original edge value conjugates the value of its retained word. -/
private theorem word_conj {count : Nat} (value : Topology.Polygon.Stokes.OrientedEdge count → Gaussian.Basic.Canonical)
    (word : List (Topology.Polygon.Stokes.OrientedEdge count)) :
    SewingRetraction.wordValue (fun edge => Gaussian.Basic.conj (value edge))
      word = Gaussian.Basic.conj (SewingRetraction.wordValue value word) := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      change Gaussian.Basic.conj (value edge) + SewingRetraction.wordValue _ rest =
        Gaussian.Basic.conj (value edge + SewingRetraction.wordValue value rest)
      rw [ih, Gaussian.Basic.conj_add]

/-- The finite sum of conjugated original word values is the conjugate of their retained total. -/
private theorem sum_word_conj {Alpha : Type} {count : Nat}
    (value : Topology.Polygon.Stokes.OrientedEdge count → Gaussian.Basic.Canonical) (word : Alpha → List
      (Topology.Polygon.Stokes.OrientedEdge count))
    (entries : List Alpha) :
    CellBoundary.sumValues (fun entry =>
      SewingRetraction.wordValue (fun edge => Gaussian.Basic.conj (value edge))
      (word entry)) entries =
      Gaussian.Basic.conj (CellBoundary.sumValues (fun entry =>
        SewingRetraction.wordValue value (word entry)) entries) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      change SewingRetraction.wordValue _ (word entry) + CellBoundary.sumValues _
        rest = Gaussian.Basic.conj (SewingRetraction.wordValue value (word entry) +
        CellBoundary.sumValues _ rest)
      rw [PolarizedExteriorRequest.word_conj, ih,
        Gaussian.Basic.conj_add]

/-- Conjugating the original edge readings conjugates the retained terminal exterior factor. -/
private theorem factor_conj (newSheet : Fin 2)
    (value : Topology.Polygon.Stokes.OrientedEdge current.vertices.count → Gaussian.Basic.Canonical) :
    ExteriorTotal.resplitExteriorFactor (paired := paired) included
      current.edges current.vertices newSheet
        (fun edge => Gaussian.Basic.conj (value edge)) =
      Gaussian.Basic.conj (ExteriorTotal.resplitExteriorFactor
        (paired := paired) included current.edges current.vertices newSheet value) := by
  unfold ExteriorTotal.resplitExteriorFactor
  cases paired.split.ending with
  | odd index => rfl
  | even firstIndex lastIndex =>
    dsimp only
    rw [← bank.resplit_pairs_value included current.edges current.vertices,
      ← bank.resplit_pairs_value included current.edges current.vertices,
      PolarizedExteriorRequest.word_conj,
        PolarizedExteriorRequest.word_conj,
        Gaussian.Basic.conj_add]

variable {newSheet : Fin 2}
  (compiled : OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
    included current.edges current.vertices
    (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
    ordered.prepared.partition newSheet)

/-- The physical-minus-terminal polarized exterior correction is the exact paired area of the retained factors and
regular-loop totals. -/
private theorem difference_readback
    (reference : ∀ point, FromStates.ContainsVertex next.bank.grid point →
      Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    (first second : Topology.Polygon.Stokes.OrientedEdge current.vertices.count → Gaussian.Basic.Canonical)
    (firstAnti : ∀ edge, first edge.reverse = -first edge) (secondAnti : ∀ edge, second edge.reverse = -second edge) :
    BilinearPolarization.extract (fun coefficient =>
      ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
        included current.edges current.vertices newSheet
        (BilinearPolarization.mix first second coefficient))
          -
      BilinearPolarization.extract (fun coefficient =>
        TerminalCorrection.resplitExteriorCorrection (paired := paired)
          included current.edges current.vertices newSheet
          (BilinearPolarization.mix first second
            coefficient)) =
      Topology.Polygon.Stokes.edgeArea
        (⟨resplitExteriorFactor (paired := paired) included current.edges current.vertices newSheet first,
          ExteriorTotal.resplitExteriorFactor (paired := paired) included
            current.edges current.vertices newSheet second⟩ : Topology.Polygon.Stokes.PrimitivePoint)
        (⟨sumValues (fun occurrence => SewingRetraction.wordValue first occurrence.word)
          compiled.regulars,
          CellBoundary.sumValues (fun occurrence =>
            SewingRetraction.wordValue second occurrence.word) compiled.regulars⟩ :
            Topology.Polygon.Stokes.PrimitivePoint) := open Purelib.Integration in open RootIsolation in by
  have partition (value : Topology.Polygon.Stokes.OrientedEdge current.vertices.count → Gaussian.Basic.Canonical) (anti
    : ∀ edge, value edge.reverse = -value edge) :
      CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue value
        occurrence.word) compiled.regulars =
        current.edges.chainValue current.vertices value (included.resplit base.bank.exterior
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet -
        SewingRetraction.wordValue value (current.edges.indexedEdges current.vertices
          (included.resplit (bank.loopProduct ordered.prepared.labels)
            (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet)
            := by
    rw [ExteriorTotal.resplit_exterior_integral_partition included
      current.edges current.vertices reference compiled value anti]
    ring1
  have read (coefficient : Gaussian.Basic.Canonical) :=
    ExteriorTotal.resplit_physical_exterior_difference (paired := paired)
    included
    current.edges current.vertices reference compiled
      (BilinearPolarization.mix first second coefficient)
    (BilinearPolarization.mix_reverse first second firstAnti
      secondAnti coefficient)
  have polarized := BilinearPolarization.extract_congr read
  have linear (coefficient : Gaussian.Basic.Canonical) :
      CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue
        (BilinearPolarization.mix first second coefficient)
        occurrence.word)
        compiled.regulars = Gaussian.Basic.conj (CellBoundary.sumValues (fun occurrence =>
          SewingRetraction.wordValue first occurrence.word) compiled.regulars) +
          coefficient * CellBoundary.sumValues (fun occurrence =>
            SewingRetraction.wordValue second occurrence.word) compiled.regulars := by
    rw [partition _ (BilinearPolarization.mix_reverse first
      second firstAnti secondAnti coefficient),
      partition first firstAnti, partition second secondAnti]
    unfold SquareRoot.Grid.RootEdgeBank.chainValue
    rw [BilinearPolarization.word_mix,
      BilinearPolarization.word_mix]
    have conjugateSub (a b : Gaussian.Basic.Canonical) : Gaussian.Basic.conj (a - b) =
      Gaussian.Basic.conj a - Gaussian.Basic.conj b := by
      apply Gaussian.Basic.ext
      · rfl
      · change -(a.im - b.im) = -a.im - -b.im
        ring1
    rw [conjugateSub]
    ring1
  have target := (BilinearPolarization.extract_congr
    (first := fun coefficient => Path.BoundaryRibbon.area
      (ExteriorTotal.resplitExteriorFactor (paired := paired) included
        current.edges current.vertices newSheet
        (BilinearPolarization.mix first second coefficient))
      (CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue
        (BilinearPolarization.mix first second coefficient)
        occurrence.word)
        compiled.regulars)) (fun coefficient => by
    rw [PolarizedExterior.PolarizedExteriorRequest.factor_mix,
      linear])).trans (BilinearPolarization.extract_area
      (ExteriorTotal.resplitExteriorFactor (paired := paired) included
        current.edges current.vertices newSheet first)
      (CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue first
        occurrence.word) compiled.regulars)
      (ExteriorTotal.resplitExteriorFactor (paired := paired) included
        current.edges current.vertices newSheet second)
      (CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue second
        occurrence.word) compiled.regulars))
  refine Eq.trans ?_ (polarized.trans target)
  unfold BilinearPolarization.extract
  ring1

variable {firstIndex secondIndex : Fin genus}

/-- The common original exterior factor weight is nonnegative. -/
private theorem weight_nonnegative
    (first : Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex)) :
    0 ≤ PolarizedExterior.PolarizedExteriorRequest.canonicalWeight (paired
      := paired) included first second :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    ((PolarizedExterior.PolarizedExteriorRequest.factorBound_nonnegative
    included first).trans (Fraction.Order.Basic.le_max_left _ _))

variable {included compiled}
  {first : Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential firstIndex)}
  {second : Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential secondIndex)} {error : Fraction.Rational}

/-- The retained original compiled regular-loop total meets its requested allowance at every sufficient stage. -/
private theorem regular_bound {differential : Fin genus} {tolerance : Fraction.Rational}
    (positive : 0 < tolerance) (request :
      RegularRequest (domains :=
      domains) included compiled differential tolerance)
    {stage : Nat} {shared : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (later : request.val ≤ stage) :
    Gaussian.Norm.Basic.normSq (CellBoundary.sumValues (fun occurrence =>
      SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
      occurrence.word) compiled.regulars) ≤ tolerance := open Approximation in by
  have listRead {Alpha : Type} (value : Alpha → Gaussian.Basic.Canonical) (entries : List Alpha) :
      CellBoundary.sumValues value entries = Gaussian.Norm.Sum.Basic.gaussianSum (entries.map value)
        := by
    induction entries with
    | nil => rfl
    | cons entry rest ih => exact congrArg (value entry + ·) ih
  rw [listRead]
  apply (Gaussian.Budget.Aggregate.normSq_sum_lt _ positive ?_).le
  intro value member
  obtain ⟨entry, present, equal⟩ := Data.List.Map.mem_map.mp member
  rw [← equal, List.Map.length_map]
  exact (request.property stage shared readings later entry present).le

open Purelib.Approximation in
/-- The replacement error is paid at every later common sample. The
physical exterior itself has not been asserted small. -/
theorem conjugate_accurate (request :
  PolarizedExterior.PolarizedExteriorRequest (paired := paired) included
  compiled first second error)
    (reference : ∀ point, FromStates.ContainsVertex next.bank.grid point →
      Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    {stage : Nat} {leftShared : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential firstIndex) stage domains}
    {rightShared : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential secondIndex) stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftShared
      current.mesh) (rightReadings : TrianglePrimitiveReadings.TriangleReadings
      rightShared current.mesh)
    (later : request.index ≤ stage) :
    let left := fun edge => Gaussian.Basic.conj
      (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values edge)
    let right := CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values
    Gaussian.Norm.Basic.normSq
      (BilinearPolarization.extract (fun coefficient =>
      ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
        included current.edges current.vertices newSheet
        (BilinearPolarization.mix left right coefficient)) -
      BilinearPolarization.extract (fun coefficient =>
        TerminalCorrection.resplitExteriorCorrection (paired := paired)
          included current.edges current.vertices newSheet
          (BilinearPolarization.mix left right coefficient)))
            ≤ error := by
  intro left right
  rw [PolarizedExteriorRequest.difference_readback
    included compiled reference left right
    (fun edge => by
        dsimp only [left];
        rw [CanonicalEdgeValues.edgeValuation_reverse];
        rfl)
    (CanonicalEdgeValues.edgeValuation_reverse current.mesh rightReadings.values)]
  rw [PolarizedExteriorRequest.factor_conj,
    PolarizedExteriorRequest.sum_word_conj]
  have fixedLater := (Nat.Order.le_max_left _ _).trans later
  have requestLater := (Nat.Order.le_max_right _ _).trans later
  have leftBound :=
    PolarizedExterior.PolarizedExteriorRequest.factor_bounded (paired :=
    paired) included first newSheet leftReadings
    ((Nat.Order.le_max_left _ _).trans fixedLater)
  have rightBound :=
    PolarizedExterior.PolarizedExteriorRequest.factor_bounded (paired :=
    paired) included second newSheet rightReadings
    ((Nat.Order.le_max_right _ _).trans fixedLater)
  have weightNonnegative : 0 ≤ request.weight := request.weight_eq ▸
    PolarizedExteriorRequest.weight_nonnegative included
    first second
  have tolerancePositive := Rational.Budget.Weighted.allowance_positive request.positive weightNonnegative
  have leftSmall :=
    PolarizedExteriorRequest.regular_bound
    tolerancePositive request.left leftReadings ((Nat.Order.le_max_left _ _).trans requestLater)
  have rightSmall :=
    PolarizedExteriorRequest.regular_bound
    tolerancePositive request.right rightReadings ((Nat.Order.le_max_right _ _).trans requestLater)
  have canonicalBound {point : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Gaussian.Norm.Basic.normSq point ≤ limit) :
      Gaussian.Basic.Canonical.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  have estimate := Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound
    (first := (⟨_, _⟩ : Topology.Polygon.Stokes.PrimitivePoint)) (last := (⟨_, _⟩ :
      Topology.Polygon.Stokes.PrimitivePoint))
    ⟨canonicalBound (((Gaussian.Norm.Basic.normSq_conj _).trans_le leftBound).trans (Fraction.Order.Basic.le_max_left
      (PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) included first)
      (PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) included second))),
      canonicalBound (rightBound.trans (Fraction.Order.Basic.le_max_right
        (PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
        paired) included first)
        (PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
        paired) included second)))⟩
    ⟨canonicalBound ((Gaussian.Norm.Basic.normSq_conj _).trans_le leftSmall), canonicalBound rightSmall⟩
  refine estimate.trans ?_
  change PolarizedExterior.PolarizedExteriorRequest.canonicalWeight (paired
    := paired) included first second * Rational.Budget.Weighted.allowance error request.weight ≤ error
  rw [← request.weight_eq]
  exact Rational.Budget.Weighted.mul_allowance_le request.positive.le weightNonnegative

end PolarizedExteriorRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateExterior
