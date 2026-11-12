module
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SurfacePeriods

namespace TestPurelib.Curves.Hyperelliptic.CanonicalWordReadings

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SurfacePeriods.Prepared
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
open Purelib.Data
open Purelib.Data.Rat.Fraction
open Purelib.Riemann
open Purelib.Topology.Surface.Sewing
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
open Purelib.Riemann.Branches.RectangularSheetGauge
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus}
  {branches : Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank : BasedBranchBank lifted}
  {sheet : Fin 2} {ordered : Ordered bank sheet}
  {paired : OrderedBranchPairs.Ordered.Paired ordered}
  {prepared : PeriodPrograms.Prepared paired}
  {domains : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {differential : Fin genus} {target : Rational} {minimumStage : Nat}

/-- One actual supplied surface bank pays its canonical word combination at the retained common period stage.

The bank is passed literally to the original request factory. The closed
word's physical value and face residual use that exact request's valuation;
its integral coordinates and coefficient caches use the original builders.
No independent primitive bank or zero-residual hypothesis occurs here.
-/
private theorem supplied_bank_word (budget : SurfaceBudget prepared domains differential target)
    {numericalIndex : Nat} (later : budget.minimum ≤ numericalIndex)
    (numerics : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (minimumStage : Nat) (cut : PeriodCoordinates.CutBank prepared)
    {word : List (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)}
    (row : PeriodCoordinates.ClosedCoordinates word cut.integral) :
    let request := budget.requestWith later numerics minimumStage
    let coordinates := SpanningRows.BasisCoordinates.build cut row
    let aCoefficients := Periods.WeightedPeriods.Coefficients.build coordinates.a
    let bCoefficients := Periods.WeightedPeriods.Coefficients.build coordinates.b
    let stage := request.family.requested.stage
    Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue request.value word -
      (aCoefficients.combine (fun index =>
          ((prepared.periodData.aProgram differential index).integral.model stage).integralSample) +
        bCoefficients.combine (fun index =>
          ((prepared.periodData.bProgram differential index).integral.model stage).integralSample) +
        coordinates.physicalValue request.value + coordinates.faceResidual request.value)) ≤
      2 * (aCoefficients.charge (fun _ => target) + bCoefficients.charge (fun _ => target)) := by
  let request := budget.requestWith later numerics minimumStage
  let coordinates := SpanningRows.BasisCoordinates.build cut row
  let aCoefficients := Periods.WeightedPeriods.Coefficients.build coordinates.a
  let bCoefficients := Periods.WeightedPeriods.Coefficients.build coordinates.b
  exact request.word_accurate coordinates aCoefficients bCoefficients _ (Nat.le_refl _)

/-- The same client retains the whole supplied bank, including its indexed primitive and corner caches. -/
private theorem supplied_bank_retained (budget : SurfaceBudget prepared domains differential target)
    {numericalIndex : Nat} (later : budget.minimum ≤ numericalIndex)
    (numerics : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (minimumStage : Nat) :
    HEq (budget.requestWith later numerics minimumStage).family.numerics numerics :=
  budget.requestWith_numerics later numerics minimumStage

/-- Default face preparation preserves the complete original primitive, anchor, offset and corner factory.

This compares the whole retained value, including its original selected
corner owners and dependent certificates, at every genus and stage.
-/
private theorem default_domain_factory
    {face : Meshes.PuncturedGridFaces.RegularFace base.bank.toBranchCellBank}
    {models : Face.InverseModels.BranchCellBank.FaceModels lifted.frames face}
    (domain : PeriodDomain models sheet) (source : Differentials.Basic.Differential genus) (index : Nat) :
    DomainPrimitives.build domain source index =
  let sheets := domain.patch.sheets.refine index
  let primitives := Primitives.build (Transitions.oriented sheets.transitions sheets.gauge)
    (PreparedPrimitiveSamples.differentialNumerator source)
  let anchors := PrimitiveAnchors.build primitives
  let offsets := anchors.offsets
  let owners := Data.Vector.Basic.vectorOfFn fun corner =>
    let located := Face.EnteredPaths.PeriodDomain.locate domain
      (FaceCorners.point face.cell.box corner)
      (FaceCorners.inside face.cell.box corner)
    (⟨located.column, located.row, FaceCorners.point face.cell.box corner, located.inside⟩ :
      OwnedVertex domain.geometry)
  let corners := PointReadings.build anchors offsets (FaceCorners.point face.cell.box) owners
    (fun corner => by rw [Data.Vector.Basic.vectorOfFn_apply])
  ⟨primitives, anchors, offsets, corners⟩ := (rfl)

end TestPurelib.Curves.Hyperelliptic.CanonicalWordReadings
