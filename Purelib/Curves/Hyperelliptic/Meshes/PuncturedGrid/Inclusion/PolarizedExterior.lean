module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! Requested polarized replacement of the terminal total by the physical
exterior. The physical exterior correction itself remains in the result. -/

section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

open Purelib.Data.List

open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal (resplitExteriorFactor
  resplitPhysicalExteriorCorrection resplitExteriorCorrection_total resplit_exterior_integral_partition
  resplit_physical_exterior_difference)

open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)

open Purelib.Data.Gaussian.Basic (Canonical)

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

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

/-- The squared original walk length times the retained fourfold edge magnitude bound. -/
@[expose] def walkBound {differential : Fin genus}
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential differential))
    {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk next.bank.grid start finish) :
      Fraction.Rational :=
  (walk.edgeCount : Fraction.Rational)^2 * (4 * fixed.bound)

/-- The original walk bound is nonnegative. -/
theorem walkBound_nonnegative {differential : Fin genus}
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential differential))
    {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk next.bank.grid start finish) : 0 ≤
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.walkBound fixed walk :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2) (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      fixed.nonnegative)

/-- The original cached word observation satisfies its squared-length magnitude estimate. -/
private theorem walk_bounded {differential : Fin genus}
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential differential))
    {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk next.bank.grid start finish) (incoming :
      Fin 2)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (later : fixed.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Purelib.Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)
      (current.edges.indexedEdges current.vertices walk incoming)) ≤
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.walkBound fixed walk :=
        by
  let retainedMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison.ownerFromMesh current.mesh) fixed later
      readings
  let observation := Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations.realize retainedMagnitude
    (current.edges.indexedEdges current.vertices walk incoming)
  have cached := observation.bounded
  change Data.Gaussian.Norm.Basic.normSq observation.total ≤ observation.bound at cached
  rw [observation.total_readback, observation.bound_readback,
    Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations.BoundSpecification] at cached
  change Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)
    (current.edges.indexedEdges current.vertices walk incoming)) ≤
    ((current.edges.indexedEdges current.vertices walk incoming).length : Fraction.Rational) ^ 2 * (4 * fixed.bound)
      at cached
  rw [current.edges.indexedEdges_length] at cached
  exact cached
/-- Twice the sum of the original reference and paired-prefix walk bounds. -/
@[expose] def factorBound {differential : Fin genus}
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential differential)) : Fraction.Rational :=
  2 * (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.walkBound fixed
    (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk
    (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) +
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.walkBound fixed
      (included.resplit (bank.loopProduct (paired.split.pairs.flatMap (fun pair => [pair.1, pair.2])))
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)))

/-- The original exterior factor bound is nonnegative. -/
theorem factorBound_nonnegative {differential : Fin genus}
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential differential)) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) included fixed :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.walkBound_nonnegative fixed
    _) (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.walkBound_nonnegative
    fixed _))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest in
/-- The actual terminal exterior factor satisfies its retained magnitude bound. -/
theorem factor_bounded {differential : Fin genus}
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential differential)) (newSheet : Fin 2)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (later : fixed.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor (paired := paired) included
      current.edges current.vertices newSheet
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)) ≤
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
        paired) included fixed := by
  have referenceBound :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.walk_bounded fixed
    (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet readings
      later
  have priorBound :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.walk_bounded fixed
    (included.resplit (bank.loopProduct (paired.split.pairs.flatMap (fun pair => [pair.1, pair.2])))
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
    newSheet readings later
  rw [bank.resplit_pairs_value included current.edges current.vertices] at priorBound
  have nonnegative :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound_nonnegative
    (paired := paired) included fixed
  unfold Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor
  cases endingEq : paired.split.ending with
  | odd index => exact Gaussian.Norm.Basic.normSq_zero.trans_le nonnegative
  | even first last =>
    have referenceEq : paired.split.ending.reference = first := congrArg
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding.reference endingEq
    rw [referenceEq] at referenceBound
    have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct referenceBound priorBound) (by decide))
    unfold Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound
    rw [endingEq]
    exact estimate

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest in
/-- Mixing the original readings conjugates and combines their retained exterior factors. -/
theorem factor_mix (newSheet : Fin 2)
    (first second : Topology.Polygon.Stokes.OrientedEdge current.vertices.count → Gaussian.Basic.Canonical) (coefficient
      : Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor (paired := paired) included
      current.edges current.vertices newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient) =
      Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor
        (paired := paired) included current.edges current.vertices newSheet first) +
        coefficient * Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor (paired :=
          paired) included current.edges current.vertices newSheet second := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor
  cases paired.split.ending with
  | odd index => rw [Gaussian.Basic.conj_zero]; ring1
  | even firstIndex lastIndex =>
    dsimp only
    rw [← bank.resplit_pairs_value included current.edges current.vertices,
      ← bank.resplit_pairs_value included current.edges current.vertices,
      ← bank.resplit_pairs_value included current.edges current.vertices,
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix,
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix,
      Gaussian.Basic.conj_add]
    ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

variable {newSheet : Fin 2}
  (compiled : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
    included current.edges current.vertices
    (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
    ordered.prepared.partition newSheet)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

/-- The physical-minus-terminal polarized correction is exactly the paired area of the original factors and regular-loop
totals. -/
private theorem difference_readback
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex next.bank.grid point →
      Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    (first second : Topology.Polygon.Stokes.OrientedEdge current.vertices.count → Gaussian.Basic.Canonical)
    (firstAnti : ∀ edge, first edge.reverse = -first edge) (secondAnti : ∀ edge, second edge.reverse = -second edge) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
        included current.edges current.vertices newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient))
          -
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection (paired := paired)
          included current.edges current.vertices newSheet
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
            coefficient)) =
      Topology.Polygon.Stokes.edgeArea
        (⟨resplitExteriorFactor (paired := paired) included current.edges current.vertices newSheet first,
          Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor (paired := paired) included
            current.edges current.vertices newSheet second⟩ : Topology.Polygon.Stokes.PrimitivePoint)
        (⟨sumValues (fun occurrence => Purelib.Topology.Surface.Sewing.SewingRetraction.wordValue first occurrence.word)
          compiled.regulars,
          Purelib.Polynomial.Geometry.Grid.CellBoundary.sumValues (fun occurrence =>
            Purelib.Topology.Surface.Sewing.SewingRetraction.wordValue second occurrence.word) compiled.regulars⟩ :
            Topology.Polygon.Stokes.PrimitivePoint) := open Purelib.Integration in open Purelib.RootIsolation in by
  have partition (value : Topology.Polygon.Stokes.OrientedEdge current.vertices.count → Gaussian.Basic.Canonical) (anti
    : ∀ edge, value edge.reverse = -value edge) :
      Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Surface.Sewing.SewingRetraction.wordValue value
        occurrence.word) compiled.regulars =
        current.edges.chainValue current.vertices value (included.resplit base.bank.exterior
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet -
        Topology.Surface.Sewing.SewingRetraction.wordValue value (current.edges.indexedEdges current.vertices
          (included.resplit (bank.loopProduct ordered.prepared.labels)
            (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet)
            := by
    rw [Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplit_exterior_integral_partition included
      current.edges current.vertices reference compiled value anti]
    ring1
  have read (coefficient : Gaussian.Basic.Canonical) :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplit_physical_exterior_difference (paired := paired)
    included
    current.edges current.vertices reference compiled
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix_reverse first second firstAnti
      secondAnti coefficient)
  have polarized := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr read
  have linear (coefficient : Gaussian.Basic.Canonical) :
      Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
        occurrence.word)
        compiled.regulars = Data.Gaussian.Basic.conj (Geometry.Grid.CellBoundary.sumValues (fun occurrence =>
          Topology.Surface.Sewing.SewingRetraction.wordValue first occurrence.word) compiled.regulars) +
          coefficient * Geometry.Grid.CellBoundary.sumValues (fun occurrence =>
            Topology.Surface.Sewing.SewingRetraction.wordValue second occurrence.word) compiled.regulars := by
    rw [partition _ (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix_reverse first
      second firstAnti secondAnti coefficient),
      partition first firstAnti, partition second secondAnti]
    unfold SquareRoot.Grid.RootEdgeBank.chainValue
    rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix,
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix]
    have conjugateSub (a b : Gaussian.Basic.Canonical) : Data.Gaussian.Basic.conj (a - b) =
      Data.Gaussian.Basic.conj a - Data.Gaussian.Basic.conj b := by
      apply Gaussian.Basic.ext
      · rfl
      · change -(a.im - b.im) = -a.im - -b.im
        ring1
    rw [conjugateSub]
    ring1
  have target := (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr
    (first := fun coefficient => Path.BoundaryRibbon.area
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor (paired := paired) included
        current.edges current.vertices newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient))
      (Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
        occurrence.word)
        compiled.regulars)) (fun coefficient => by
    rw [Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factor_mix,
      linear])).trans (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_area
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor (paired := paired) included
        current.edges current.vertices newSheet first)
      (Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Surface.Sewing.SewingRetraction.wordValue first
        occurrence.word) compiled.regulars)
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor (paired := paired) included
        current.edges current.vertices newSheet second)
      (Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Surface.Sewing.SewingRetraction.wordValue second
        occurrence.word) compiled.regulars))
  refine Eq.trans ?_ (polarized.trans target)
  unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

variable {firstIndex secondIndex : Fin genus}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

/-- Four times the larger original exterior factor bound, shared by both regular-loop requests. -/
@[expose] def canonicalWeight
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex)) : Fraction.Rational :=
  4 * max (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired
    := paired) included first)
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
    paired) included second)

/-- The common exterior factor weight is nonnegative. -/
theorem weight_nonnegative
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex)) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.canonicalWeight (paired
      := paired) included first second :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    ((Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound_nonnegative
    included first).trans (Data.Rat.Fraction.Order.Basic.le_max_left _ _))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest in
/-- The retained regular-loop threshold and its exact per-entry bound. -/
@[expose] def RegularRequest (differential : Fin genus) (tolerance : Fraction.Rational) :=
  { index : Nat //
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.RegularsSmallAt
    current.mesh domains differential
      (Rational.Budget.Aggregate.perTerm tolerance compiled.regulars.length) compiled.regulars index }

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

end

variable {newSheet : Fin 2}
  (compiled : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
    included current.edges current.vertices
    (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
    ordered.prepared.partition newSheet)
  {firstIndex secondIndex : Fin genus}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior

set_option genInjectivity false in
/-- A paid comparison between the original physical and terminal polarized exterior corrections.

It retains both magnitude banks, their common factor weight and separate regular-loop requests at the same allocated
tolerance. -/
structure PolarizedExteriorRequest
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) where
  /-- The requested comparison target is positive. -/ positive : 0 < error
  /-- The cached common exterior factor weight. -/ weight : Fraction.Rational
  /-- The cached weight is computed from the original two magnitude banks. -/ weight_eq : weight =
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.canonicalWeight (paired :=
    paired) included first second
  /-- The regular-loop request for the first original differential at the common allowance. -/ left :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.RegularRequest (domains :=
    domains) (compiled := compiled) included firstIndex (Rational.Budget.Weighted.allowance error weight)
  /-- The regular-loop request for the second original differential at the common allowance. -/ right :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.RegularRequest (domains :=
    domains) (compiled := compiled) included secondIndex (Rational.Budget.Weighted.allowance error weight)

constructive_injectivity PolarizedExteriorRequest

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

variable {included compiled}
  {first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential firstIndex)}
  {second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential secondIndex)} {error : Fraction.Rational}

/-- Prepare both original regular-loop requests using their common exterior factor weight. -/
@[expose] def build (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)
    (compiled : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included current.edges current.vertices
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
      ordered.prepared.partition newSheet)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) (positive : 0 < error) (minimum : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest (paired := paired) included
      compiled first second error :=
  let weight := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.canonicalWeight
    (paired := paired) included first second
  have tolerancePositive := Rational.Budget.Weighted.allowance_positive positive
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.weight_nonnegative included
    first second)
  ⟨positive, weight, rfl,
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.regularZeroRequests
      current.mesh domains (Periods.PeriodMatrix.standardDifferential firstIndex) firstIndex
      (Rational.Budget.Aggregate.perTerm (Rational.Budget.Weighted.allowance error weight) compiled.regulars.length)
        (Rational.Budget.Aggregate.perTerm_positive tolerancePositive _) minimum compiled.regulars,
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.regularZeroRequests
      current.mesh domains (Periods.PeriodMatrix.standardDifferential secondIndex) secondIndex
      (Rational.Budget.Aggregate.perTerm (Rational.Budget.Weighted.allowance error weight) compiled.regulars.length)
        (Rational.Budget.Aggregate.perTerm_positive tolerancePositive _) minimum compiled.regulars⟩

/-- The common stage threshold covering both original magnitude banks and regular-loop requests. -/
@[expose] def index (request : Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest
  (paired := paired) included compiled first second error) : Nat :=
  max (max first.index second.index) (max request.left.val request.right.val)

/-- The original compiled regular-loop total meets the common allowance at every sufficient stage. -/
private theorem regular_bound {differential : Fin genus} {tolerance : Fraction.Rational}
    (positive : 0 < tolerance) (request :
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.RegularRequest (domains :=
      domains) (compiled := compiled) included differential tolerance)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (later : request.val ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Purelib.Polynomial.Geometry.Grid.CellBoundary.sumValues (fun occurrence =>
      Purelib.Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)
      occurrence.word) compiled.regulars) ≤ tolerance := by
  have listRead {Alpha : Type} (value : Alpha → Gaussian.Basic.Canonical) (entries : List Alpha) :
      Geometry.Grid.CellBoundary.sumValues value entries = Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map value)
        := by
    induction entries with
    | nil => rfl
    | cons entry rest ih => exact congrArg (value entry + ·) ih
  rw [listRead]
  apply (Gaussian.Budget.Aggregate.normSq_sum_lt _ positive ?_).le
  intro value member
  obtain ⟨entry, present, equal⟩ := Data.List.Map.mem_map.mp member
  rw [← equal, Map.length_map]
  exact (request.property stage shared readings later entry present).le

/-- The replacement error is paid at every later common sample. The
physical exterior itself has not been asserted small. -/
theorem accurate (request : Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest
  (paired := paired) included compiled first second error)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex next.bank.grid point →
      Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    {stage : Nat} {leftShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential firstIndex) stage domains}
    {rightShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential secondIndex) stage domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftShared
      current.mesh) (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
      rightShared current.mesh)
    (later : request.index ≤ stage) :
    let left := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values
    let right := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
        included current.edges current.vertices newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix left right coefficient)) -
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection (paired := paired)
          included current.edges current.vertices newSheet
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix left right coefficient)))
            ≤ error := by
  intro left right
  rw [Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.difference_readback
    included compiled reference left right
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse current.mesh leftReadings.values)
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse current.mesh rightReadings.values)]
  have fixedLater := (Data.Nat.Order.le_max_left _ _).trans later
  have requestLater := (Data.Nat.Order.le_max_right _ _).trans later
  have leftBound :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factor_bounded (paired :=
    paired) included first newSheet leftReadings
    ((Data.Nat.Order.le_max_left _ _).trans fixedLater)
  have rightBound :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factor_bounded (paired :=
    paired) included second newSheet rightReadings
    ((Data.Nat.Order.le_max_right _ _).trans fixedLater)
  have weightNonnegative : 0 ≤ request.weight := request.weight_eq ▸
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.weight_nonnegative included
    first second
  have tolerancePositive := Rational.Budget.Weighted.allowance_positive request.positive weightNonnegative
  have leftSmall :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.regular_bound
    tolerancePositive request.left leftReadings ((Data.Nat.Order.le_max_left _ _).trans requestLater)
  have rightSmall :=
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.regular_bound
    tolerancePositive request.right rightReadings ((Data.Nat.Order.le_max_right _ _).trans requestLater)
  have canonicalBound {point : Canonical} {limit : Rational}
      (h : Data.Gaussian.Norm.Basic.normSq point ≤ limit) :
      Canonical.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  have estimate := Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound
    (first := (⟨_, _⟩ : Topology.Polygon.Stokes.PrimitivePoint)) (last := (⟨_, _⟩ :
      Topology.Polygon.Stokes.PrimitivePoint))
    ⟨canonicalBound (leftBound.trans (Data.Rat.Fraction.Order.Basic.le_max_left
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) included first)
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
      paired) included second))),
      canonicalBound (rightBound.trans (Data.Rat.Fraction.Order.Basic.le_max_right
        (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
        paired) included first)
        (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.factorBound (paired :=
        paired) included second)))⟩
    ⟨canonicalBound leftSmall, canonicalBound rightSmall⟩
  refine estimate.trans ?_
  change Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.canonicalWeight (paired
    := paired) included first second * Rational.Budget.Weighted.allowance error request.weight ≤ error
  rw [← request.weight_eq]
  exact Rational.Budget.Weighted.mul_allowance_le request.positive.le weightNonnegative

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest

end
