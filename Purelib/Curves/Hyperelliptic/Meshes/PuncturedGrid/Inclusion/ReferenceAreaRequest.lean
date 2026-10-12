module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Paired.Increments
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

@[expose] public section

/-! Requested control of the original reference double-loop term. The
request shares the current primitive bank and pays its actual prefix size. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

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
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}

namespace ReferenceAreaRequest

/-- The original paired-prefix branch walk resplit through the retained coordinate inclusion. -/
public def prefixWalk := included.resplit
  (bank.loopProduct (paired.split.pairs.flatMap (fun pair => [pair.1, pair.2])))
    (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)

/-- The original terminal reference walk resplit through the retained inclusion. -/
public def referenceWalk := included.resplit
  (bank.rows.get paired.split.ending.reference).reference.walk
    (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)

/-- The squared original prefix length and magnitude bound weighted for the reference ribbon estimate. -/
public def referenceWeight (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential) : Fraction.Rational :=
  4 * (((Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.prefixWalk (paired := paired)
    included).edgeCount : Fraction.Rational)^2 * (4 * fixed.bound))

/-- The original reference ribbon weight is nonnegative. -/
public theorem referenceWeight_nonnegative (fixed :
  Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.referenceWeight (paired := paired) included
      fixed :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) fixed.nonnegative))

end ReferenceAreaRequest

set_option genInjectivity false in
/-- A paid request for the original terminal reference double-loop correction.

It retains the actual prefix weight and reference walk on the same current primitive bank and requested sheet. -/
structure ReferenceAreaRequest (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential) (newSheet : Fin 2) (error : Fraction.Rational) where
  /-- The requested reference correction target is positive. -/ positive : 0 < error
  /-- The cached reference ribbon weight. -/ weight : Fraction.Rational
  /-- The weight is computed from the retained original paired-prefix walk. -/ weight_eq : weight =
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.referenceWeight (paired := paired) included
    fixed
  /-- The actual paired occurrences of the retained terminal reference walk. -/ reference :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk current.mesh
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.referenceWalk (paired := paired) included)
  /-- The weighted increment request on the original reference occurrences. -/ request :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk.IncrementRequest
    reference domains differential newSheet (Rational.Budget.Weighted.allowance error weight)

constructive_injectivity ReferenceAreaRequest

namespace ReferenceAreaRequest.mk

end ReferenceAreaRequest.mk

namespace ReferenceAreaRequest

variable {included} {fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential} {newSheet : Fin 2} {error : Fraction.Rational}

/-- Prepare the actual reference occurrences and their paid weighted increment request. -/
def build (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (newSheet :
      Fin 2) (error : Fraction.Rational) (positive : 0 < error) :
    ReferenceAreaRequest (paired := paired) included
      fixed newSheet error :=
  let weight := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.referenceWeight (paired :=
    paired) included fixed
  let reference := Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk.build current.mesh
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.referenceWalk (paired := paired) included)
  ⟨positive, weight, rfl, reference,
    Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk.IncrementRequest.build
    reference domains differential newSheet
    (Rational.Budget.Weighted.allowance error weight)
    (Rational.Budget.Weighted.allowance_positive positive
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.referenceWeight_nonnegative included
      fixed))⟩

/-- The common threshold covering the original magnitude bank and reference increment request. -/
def index (prepared : ReferenceAreaRequest (paired :=
  paired) included fixed newSheet error) : Nat :=
  max fixed.index prepared.request.index

/-- The original magnitude bank bounds the retained paired-prefix total with its actual squared edge count. -/
private theorem prefix_bound {stage : Nat} {shared :
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (later : fixed.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Purelib.Integration.Path.Paired.Increments.total
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PairedArea.resplitReadings included current.edges
        current.vertices bank newSheet
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)
          paired.split.pairs)) ≤
      ((Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.prefixWalk (paired := paired)
        included).edgeCount : Fraction.Rational)^2 * (4 * fixed.bound) := open Purelib in by
  let retainedMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison.ownerFromMesh current.mesh) fixed later
      readings
  let observation := Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations.realize retainedMagnitude
    (current.edges.indexedEdges current.vertices
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.prefixWalk (paired := paired) included) newSheet)
  have cached := observation.bounded
  change Data.Gaussian.Norm.Basic.normSq observation.total ≤ observation.bound at cached
  rw [observation.total_readback, observation.bound_readback,
    Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations.BoundSpecification] at cached
  change Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)
    (current.edges.indexedEdges current.vertices
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.prefixWalk (paired := paired) included)
    newSheet)) ≤
    ((current.edges.indexedEdges current.vertices
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.prefixWalk (paired := paired) included)
      newSheet).length : Fraction.Rational) ^ 2 * (4 * fixed.bound) at cached
  rw [current.edges.indexedEdges_length] at cached
  rw [← bank.resplit_pairs_value included current.edges current.vertices]
  exact cached
/-- At every sufficient shared stage the retained reference ribbon correction meets its requested target. -/
theorem accurate (prepared : ReferenceAreaRequest
  (paired := paired) included fixed newSheet error)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains} (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      current.mesh)
    (later : prepared.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitReferenceCorrection (paired := paired)
      included current.edges current.vertices newSheet
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)) ≤ error :=
        open Purelib.Integration in by
  have prefixBound :=
    prefix_bound (paired :=
    paired) (included := included) (newSheet := newSheet)
    readings ((Nat.Order.le_max_left _ _).trans later)
  have small := prepared.request.accurate readings ((Nat.Order.le_max_right _ _).trans later)
  have prefixNonnegative : 0 ≤ ((Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.prefixWalk
    (paired := paired) included).edgeCount : Fraction.Rational)^2 * (4 * fixed.bound) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2) (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide) fixed.nonnegative)
  have weightNonnegative : 0 ≤ prepared.weight := prepared.weight_eq ▸
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.referenceWeight_nonnegative included fixed
  have estimate := (Path.BoundaryRibbon.area_bound _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct prefixBound
      (by decide)) small
      (Gaussian.Norm.Basic.normSq_nonneg _) (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) prefixNonnegative))
  change Data.Gaussian.Norm.Basic.normSq
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitReferenceCorrection (paired := paired)
    included current.edges current.vertices newSheet
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)) ≤ _ at estimate
  have weight : 4 * (((Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ReferenceAreaRequest.prefixWalk (paired :=
    paired) included).edgeCount : Fraction.Rational)^2 * (4 * fixed.bound)) =
      prepared.weight := prepared.weight_eq.symm
  exact estimate.trans ((congrArg (fun factor => factor * Rational.Budget.Weighted.allowance error prepared.weight)
    weight).trans_le
    (Rational.Budget.Weighted.mul_allowance_le prepared.positive.le weightNonnegative))

/-- Only the reference part is removed. The even exterior-total correction
remains in the conclusion until its physical comparison is paid. -/
theorem end_accurate (prepared : ReferenceAreaRequest
  (paired := paired) included fixed newSheet error)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains} (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      current.mesh)
    (later : prepared.index ≤ stage) :
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired :=
      paired) included current.edges current.vertices newSheet value -
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection (paired := paired)
        included current.edges current.vertices newSheet value) ≤ error := by
  intro value
  have split := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitEndCorrection_split (paired :=
    paired) included current.edges current.vertices newSheet value
  have read := (congrArg (fun total => total -
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection (paired := paired)
    included current.edges current.vertices newSheet value) split).trans (add_sub_cancel_right _ _)
  exact (congrArg Data.Gaussian.Norm.Basic.normSq read).trans_le (prepared.accurate readings later)

end ReferenceAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
