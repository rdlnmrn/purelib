module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateReference
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateExterior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateConnectors
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
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateConnectors

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateExterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateReference

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Riemann.Paths

open Purelib.Riemann.Periods

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.RetracingWords

public section

/-! Conjugate correction control on the retained compiler and existing request. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateCorrections

open Purelib.Data

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
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections (PolarizedCorrectionRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea (resplitEndCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection (resplitExteriorCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal (resplitPhysicalExteriorCorrection)
open Purelib.Topology.Mesh.RetracingWords (AreaTerm wordArea)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : FramedPuncturedGrid curve branches
    higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {current : LiftedPuncturedGrid next}
  (included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)
  {domains : FaceDomainBank current.frames
    next.faces.regulars} {newSheet : Fin 2}
  (compiled :
    OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
    included current.edges current.vertices
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
    ordered.prepared.partition newSheet)
  {firstIndex secondIndex : Fin genus}

namespace PolarizedCorrectionRequest

variable {included compiled}
  {first : FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential firstIndex)}
  {second : FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential secondIndex)} {error :
    Rational}

/-- The correction removed from the original polygon/period comparison is small on every later common sample. The
statement keeps the actual connector terms, rather than substituting regular polygon areas or another compiler. -/
theorem conjugate_accurate (request : PolarizedCorrections.PolarizedCorrectionRequest (paired := paired) included
  compiled first second error)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex next.bank.grid point →
      OwnerLoopMonodromy.WindingOneLoop curve.polynomial
      point)
    (minimum : Nat)
    {stage : Nat} {leftShared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential firstIndex) stage
      domains}
    {rightShared : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential secondIndex) stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftShared current.mesh) (rightReadings :
      TrianglePrimitiveReadings.TriangleReadings rightShared current.mesh)
    (later : request.index minimum ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
      coefficient =>
      let value := BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj
        (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values edge))
        (CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values) coefficient
      OriginalPeriodArea.resplitEndCorrection (paired := paired) included current.edges current.vertices newSheet value
        +
        AreaTerm.total value compiled.connectorTerms -
        ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired) included current.edges current.vertices
          newSheet value)) < error := by
  let values := fun coefficient => BilinearPolarization.mix
    (fun edge => Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh leftReadings.values
      edge))
    (CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values) coefficient
  let terminal := BilinearPolarization.extract (fun coefficient =>
    OriginalPeriodArea.resplitEndCorrection (paired := paired) included current.edges current.vertices newSheet (values
      coefficient))
  let exterior := BilinearPolarization.extract (fun coefficient =>
    TerminalCorrection.resplitExteriorCorrection (paired := paired) included current.edges current.vertices newSheet
      (values coefficient))
  let physical := BilinearPolarization.extract (fun coefficient =>
    ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired) included current.edges current.vertices newSheet
      (values coefficient))
  let connector := BilinearPolarization.extract (fun coefficient => AreaTerm.total (values coefficient)
    compiled.connectorTerms)
  have innerLater := (Nat.Order.le_max_right _ _).trans later
  have referenceLater := (Nat.Order.le_max_left _ _).trans innerLater
  have pairLater := (Nat.Order.le_max_right _ _).trans innerLater
  have referenceBound : Data.Gaussian.Norm.Basic.normSq (terminal - exterior) ≤ error / 16 :=
    PolarizedReferenceRequest.conjugate_end_accurate
      request.reference leftReadings rightReadings referenceLater
  have exteriorBound : Data.Gaussian.Norm.Basic.normSq (physical - exterior) ≤ error / 16 :=
    PolarizedExteriorRequest.conjugate_accurate
      request.exterior reference leftReadings rightReadings ((Nat.Order.le_max_left _ _).trans pairLater)
  have connectorBound : Data.Gaussian.Norm.Basic.normSq connector ≤ error / 16 := by
    have bound := PolarizedConnectorRequest.conjugate_accurate
      request.connectors leftReadings rightReadings ((Nat.Order.le_max_right _ _).trans pairLater)
    have read := BilinearPolarization.extract_congr (fun coefficient =>
      (congrArg (fun total => total - CellBoundary.sumValues (fun occurrence => RetracingWords.wordArea (values
        coefficient) occurrence.word) compiled.regulars)
        (compiled.area_split (values coefficient))).trans
        (show _ = AreaTerm.total (values coefficient) compiled.connectorTerms by ring1))
    exact (congrArg Data.Gaussian.Norm.Basic.normSq read.symm).trans_le bound
  have difference : Data.Gaussian.Norm.Basic.normSq ((terminal - exterior) - (physical - exterior)) ≤
      2 * (error / 16 + error / 16) :=
    (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        referenceBound exteriorBound) (by decide))
  have sumBound : Data.Gaussian.Norm.Basic.normSq (((terminal - exterior) - (physical - exterior)) + connector)
    ≤
      2 * (2 * (error / 16 + error / 16) + error / 16) :=
    (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        difference connectorBound) (by decide))
  have read : BilinearPolarization.extract (fun coefficient =>
      OriginalPeriodArea.resplitEndCorrection (paired := paired) included current.edges current.vertices newSheet
        (values coefficient) +
        AreaTerm.total (values coefficient) compiled.connectorTerms -
        ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired) included current.edges current.vertices
          newSheet (values coefficient)) =
      ((terminal - exterior) - (physical - exterior)) + connector := by
    unfold terminal exterior physical connector BilinearPolarization.extract
    ring1
  have paid : 2 * (2 * (error / 16 + error / 16) + error / 16) < error :=
    (by ring1 : 2 * (2 * (error / 16 + error / 16) + error / 16) = 10 * (error / 16)).trans_lt
      ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct (by decide : (10 : Fraction.Rational) < 16)
        request.reference.positive).trans_eq
        ((by ring1 : 16 * (error / 16) = error / 16 * 16).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))
  exact (congrArg Data.Gaussian.Norm.Basic.normSq read).trans_le sumBound |>.trans_lt paid

end PolarizedCorrectionRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateCorrections
