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
    {newSheet : Fin 2}
  (compiled : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
    included current.edges current.vertices
    (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
    ordered.prepared.partition newSheet)
  {firstIndex secondIndex : Fin genus}

set_option genInjectivity false in
/-- The original reference, exterior and connector requests paid together on one retained compiler.

Each receives one sixteenth of the target, preserving the actual physical exterior and connector terms for the combined
comparison. -/
structure PolarizedCorrectionRequest
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) where
  /-- The original reference correction request at one sixteenth of the target. -/ reference :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedReference.PolarizedReferenceRequest (paired := paired)
    included first second newSheet (error / 16)
  /-- The original physical-to-terminal exterior request at one sixteenth of the target. -/ exterior :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest (paired := paired) included
    compiled first second (error / 16)
  /-- The actual retained compiler connector request at one sixteenth of the target. -/ connectors :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest (mesh := current.mesh)
    compiled first second (error / 16)

constructive_injectivity PolarizedCorrectionRequest

namespace PolarizedCorrectionRequest

variable {included compiled}
  {first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential firstIndex)}
  {second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential secondIndex)} {error : Fraction.Rational}

/-- Prepare the three original correction requests with a shared target allocation and retained compiler. -/
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
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections.PolarizedCorrectionRequest (paired := paired)
      included compiled first second error :=
  let partPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 16)
  ⟨PolarizedReferenceRequest.build included first second newSheet (error / 16) partPositive,
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedExterior.PolarizedExteriorRequest.build included compiled
      first second (error / 16) partPositive minimum,
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.build compiled
      current.mesh first second (error / 16) partPositive minimum⟩

/-- The common numerical threshold covering the supplied minimum and all three original requests. -/
@[expose] def index (request :
  Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections.PolarizedCorrectionRequest (paired := paired)
  included compiled first second error) (minimum : Nat) : Nat :=
  max minimum (max request.reference.index (max request.exterior.index request.connectors.index))

/-- The combined correction threshold is at least the supplied minimum. -/
theorem minimum_le (request :
  Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections.PolarizedCorrectionRequest (paired := paired)
  included compiled first second error) (minimum : Nat) :
    minimum ≤ request.index minimum := Nat.Order.le_max_left _ _

/-- The correction removed from the original polygon/period comparison is
small on every later common sample. The statement keeps the actual connector
terms, rather than substituting regular polygon areas or another compiler. -/
theorem accurate (request : Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections.PolarizedCorrectionRequest
  (paired := paired) included compiled first second error)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex next.bank.grid point →
      Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    (minimum : Nat)
    {stage : Nat} {leftShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential firstIndex) stage domains}
    {rightShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential secondIndex) stage domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftShared
      current.mesh) (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
      rightShared current.mesh)
    (later : request.index minimum ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      let value := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values)
          coefficient
      Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) included current.edges
        current.vertices newSheet value +
        Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms -
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
          included current.edges current.vertices newSheet value)) < error := by
  let values := fun coefficient => Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values)
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values) coefficient
  let terminal := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
    coefficient =>
    Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) included current.edges
      current.vertices newSheet (values coefficient))
  let exterior := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
    coefficient =>
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection (paired := paired)
      included current.edges current.vertices newSheet (values coefficient))
  let physical := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
    coefficient =>
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
      included current.edges current.vertices newSheet (values coefficient))
  let connector := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
    coefficient => Topology.Mesh.RetracingWords.AreaTerm.total (values coefficient) compiled.connectorTerms)
  have innerLater := (Nat.Order.le_max_right _ _).trans later
  have referenceLater := (Nat.Order.le_max_left _ _).trans innerLater
  have pairLater := (Nat.Order.le_max_right _ _).trans innerLater
  have referenceBound : Data.Gaussian.Norm.Basic.normSq (terminal - exterior) ≤ error / 16 :=
    request.reference.end_accurate leftReadings rightReadings referenceLater
  have exteriorBound : Data.Gaussian.Norm.Basic.normSq (physical - exterior) ≤ error / 16 :=
    request.exterior.accurate reference leftReadings rightReadings ((Nat.Order.le_max_left _ _).trans pairLater)
  have connectorBound : Data.Gaussian.Norm.Basic.normSq connector ≤ error / 16 := by
    have bound := request.connectors.accurate leftReadings rightReadings ((Nat.Order.le_max_right _ _).trans pairLater)
    have read := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun
      coefficient =>
      (congrArg (fun total => total - Geometry.Grid.CellBoundary.sumValues (fun occurrence =>
        Topology.Mesh.RetracingWords.wordArea (values coefficient) occurrence.word) compiled.regulars)
        (compiled.area_split (values coefficient))).trans (Group.add_sub_cancel_left _ _))
    exact (congrArg Data.Gaussian.Norm.Basic.normSq read.symm).trans_le bound
  have difference : Data.Gaussian.Norm.Basic.normSq ((terminal - exterior) - (physical - exterior)) ≤
      2 * (error / 16 + error / 16) :=
    (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        referenceBound exteriorBound) (by decide))
  have sumBound : Data.Gaussian.Norm.Basic.normSq (((terminal - exterior) - (physical - exterior)) + connector) ≤
      2 * (2 * (error / 16 + error / 16) + error / 16) :=
    (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        difference connectorBound) (by decide))
  have read : Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient
    =>
      Hyperelliptic.Meshes.Newton.OriginalPeriodArea.resplitEndCorrection (paired := paired) included current.edges
        current.vertices newSheet (values coefficient) +
        Topology.Mesh.RetracingWords.AreaTerm.total (values coefficient) compiled.connectorTerms -
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
          included current.edges current.vertices newSheet (values coefficient)) =
      ((terminal - exterior) - (physical - exterior)) + connector := by
    unfold terminal exterior physical connector
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
    ring1
  have paid : 2 * (2 * (error / 16 + error / 16) + error / 16) < error :=
    (by ring1 : 2 * (2 * (error / 16 + error / 16) + error / 16) = 10 * (error / 16)).trans_lt
      ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct (by decide : (10 : Fraction.Rational) < 16)
        request.reference.positive).trans_eq
        ((by ring1 : 16 * (error / 16) = error / 16 * 16).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))
  exact (congrArg Data.Gaussian.Norm.Basic.normSq read).trans_le sumBound |>.trans_lt paid

end PolarizedCorrectionRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections
