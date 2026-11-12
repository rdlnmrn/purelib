module
import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Periods.PeriodMatrix
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
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

public section

/-! Remove the terminal/reference and connector corrections together on one
retained compiler. The actual physical exterior remains in the comparison. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference (PolarizedReferenceRequest)

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : OrderedBranchPairs.Ordered.Paired ordered} {current :
    Meshes.LiftedPuncturedGrid next}
  (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)
  {domains : Face.DomainBanks.FaceDomainBank current.frames next.faces.regulars}
    {newSheet : Fin 2}
  (compiled : OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
    included current.edges current.vertices
    (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
    ordered.prepared.partition newSheet)
  {firstIndex secondIndex : Fin genus}

set_option genInjectivity false in
/-- The original reference, exterior and connector requests paid together on one retained compiler.

Each receives one sixteenth of the target, preserving the actual physical exterior and connector terms for the combined
comparison. -/
structure PolarizedCorrectionRequest
    (first : Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) where
  /-- The original reference correction request at one sixteenth of the target. -/ reference :
    PolarizedReferenceRequest (paired := paired)
    included first second newSheet (error / 16)
  /-- The original physical-to-terminal exterior request at one sixteenth of the target. -/ exterior :
    PolarizedExterior.PolarizedExteriorRequest (paired := paired) included
    compiled first second (error / 16)
  /-- The actual retained compiler connector request at one sixteenth of the target. -/ connectors :
    PolarizedConnectors.PolarizedConnectorRequest (mesh := current.mesh)
    compiled first second (error / 16)

constructive_injectivity PolarizedCorrectionRequest

namespace PolarizedCorrectionRequest

variable {included compiled}
  {first : Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential firstIndex)}
  {second : Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential secondIndex)} {error : Fraction.Rational}

/-- Prepare the three original correction requests with a shared target allocation and retained compiler. -/
@[expose] def build (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)
    (compiled : OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included current.edges current.vertices
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
      ordered.prepared.partition newSheet)
    (first : Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) (positive : 0 < error) (minimum : Nat) :
    PolarizedCorrectionRequest (paired := paired)
      included compiled first second error :=
  let partPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 16)
  ⟨PolarizedReferenceRequest.build included first second newSheet (error / 16) partPositive,
    PolarizedExterior.PolarizedExteriorRequest.build included compiled
      first second (error / 16) partPositive minimum,
    PolarizedConnectors.PolarizedConnectorRequest.build compiled
      current.mesh first second (error / 16) partPositive minimum⟩

/-- The common numerical threshold covering the supplied minimum and all three original requests. -/
@[expose] def index (request :
  PolarizedCorrectionRequest (paired := paired)
  included compiled first second error) (minimum : Nat) : Nat :=
  max minimum (max request.reference.index (max request.exterior.index request.connectors.index))

/-- The combined correction threshold is at least the supplied minimum. -/
theorem minimum_le (request :
  PolarizedCorrectionRequest (paired := paired)
  included compiled first second error) (minimum : Nat) :
    minimum ≤ request.index minimum := Nat.Order.le_max_left _ _

/-- The correction removed from the original polygon/period comparison is
small on every later common sample. The statement keeps the actual connector
terms, rather than substituting regular polygon areas or another compiler. -/
theorem accurate (request : PolarizedCorrectionRequest
  (paired := paired) included compiled first second error)
    (reference : ∀ point, Geometry.Grid.FromStates.ContainsVertex next.bank.grid point →
      Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    (minimum : Nat)
    {stage : Nat} {leftShared : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential firstIndex) stage domains}
    {rightShared : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential secondIndex) stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftShared
      current.mesh) (rightReadings : TrianglePrimitiveReadings.TriangleReadings
      rightShared current.mesh)
    (later : request.index minimum ≤ stage) :
    Gaussian.Norm.Basic.normSq
      (BilinearPolarization.extract (fun coefficient =>
      let value := BilinearPolarization.mix
        (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
        (CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient
      Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) included current.edges
        current.vertices newSheet value +
        Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms -
        ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
          included current.edges current.vertices newSheet value)) < error := by
  let values := fun coefficient => BilinearPolarization.mix
    (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
    (CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values) coefficient
  let terminal := BilinearPolarization.extract (fun
    coefficient =>
    Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) included current.edges
      current.vertices newSheet (values coefficient))
  let exterior := BilinearPolarization.extract (fun
    coefficient =>
    TerminalCorrection.resplitExteriorCorrection (paired := paired)
      included current.edges current.vertices newSheet (values coefficient))
  let physical := BilinearPolarization.extract (fun
    coefficient =>
    ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
      included current.edges current.vertices newSheet (values coefficient))
  let connector := BilinearPolarization.extract (fun
    coefficient => Topology.Mesh.RetracingWords.AreaTerm.total (values coefficient) compiled.connectorTerms)
  have innerLater := (Nat.Order.le_max_right _ _).trans later
  have referenceLater := (Nat.Order.le_max_left _ _).trans innerLater
  have pairLater := (Nat.Order.le_max_right _ _).trans innerLater
  have referenceBound : Gaussian.Norm.Basic.normSq (terminal - exterior) ≤ error / 16 :=
    request.reference.end_accurate leftReadings rightReadings referenceLater
  have exteriorBound : Gaussian.Norm.Basic.normSq (physical - exterior) ≤ error / 16 :=
    request.exterior.accurate reference leftReadings rightReadings ((Nat.Order.le_max_left _ _).trans pairLater)
  have connectorBound : Gaussian.Norm.Basic.normSq connector ≤ error / 16 := by
    have bound := request.connectors.accurate leftReadings rightReadings ((Nat.Order.le_max_right _ _).trans pairLater)
    have read := BilinearPolarization.extract_congr (fun
      coefficient =>
      (congrArg (fun total => total - Geometry.Grid.CellBoundary.sumValues (fun occurrence =>
        Topology.Mesh.RetracingWords.wordArea (values coefficient) occurrence.word) compiled.regulars)
        (compiled.area_split (values coefficient))).trans (Group.add_sub_cancel_left _ _))
    exact (congrArg Gaussian.Norm.Basic.normSq read.symm).trans_le bound
  have difference : Gaussian.Norm.Basic.normSq ((terminal - exterior) - (physical - exterior)) ≤
      2 * (error / 16 + error / 16) :=
    (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        referenceBound exteriorBound) (by decide))
  have sumBound : Gaussian.Norm.Basic.normSq (((terminal - exterior) - (physical - exterior)) + connector) ≤
      2 * (2 * (error / 16 + error / 16) + error / 16) :=
    (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        difference connectorBound) (by decide))
  have read : BilinearPolarization.extract (fun coefficient
    =>
      Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) included current.edges
        current.vertices newSheet (values coefficient) +
        Topology.Mesh.RetracingWords.AreaTerm.total (values coefficient) compiled.connectorTerms -
        ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
          included current.edges current.vertices newSheet (values coefficient)) =
      ((terminal - exterior) - (physical - exterior)) + connector := by
    unfold terminal exterior physical connector
      BilinearPolarization.extract
    ring1
  have paid : 2 * (2 * (error / 16 + error / 16) + error / 16) < error :=
    (by ring1 : 2 * (2 * (error / 16 + error / 16) + error / 16) = 10 * (error / 16)).trans_lt
      ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct (by decide : (10 : Fraction.Rational) < 16)
        request.reference.positive).trans_eq
        ((by ring1 : 16 * (error / 16) = error / 16 * 16).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))
  exact (congrArg Gaussian.Norm.Basic.normSq read).trans_le sumBound |>.trans_lt paid

end PolarizedCorrectionRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections
