module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Junction
import Purelib.Polynomial.Dense.Gaussian.Basic

/-! # Actual cached gaps of covered original junction attempts

Both actual old domains, primitive/reading banks, physical Points/Entries
and join remain those of the original Attempt. The cache binds one attempt
and one original readGap, then consumes those values with actual coverage.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {leftFace rightFace : RegularFace bank}
variable {leftModels : FaceModels frames leftFace} {rightModels : FaceModels frames rightFace}
variable {start finish : Canonical} {leftCount rightCount : Nat}
variable {leftPatch : ContinuedNeighborhood curve.polynomial leftCount}
variable {rightPatch : ContinuedNeighborhood curve.polynomial rightCount}
variable (leftPoint : ContinuedNeighborhood.Point leftPatch start)
variable (rightPoint : ContinuedNeighborhood.Point rightPatch start) (leftPointInside : leftPatch.box.Contains start)
variable (leftEntry : Entry leftModels start leftPoint.owner) (rightEntry : Entry rightModels start rightPoint.owner)
variable (joined : OwnerJoin leftPoint.owner rightPoint.owner)
variable {leftDomain : PeriodDomain leftModels leftEntry.sheet}
variable {rightDomain : PeriodDomain rightModels rightEntry.sheet} {differential : Differential genus}
variable {leftIndex rightIndex leftSize rightSize : Nat}
variable {numerator : CoefficientPolynomial}
variable (leftData : DomainPrimitives leftDomain differential leftIndex (numerator := numerator))
variable (rightData : DomainPrimitives rightDomain differential rightIndex (numerator := numerator))
variable {leftPoints : Fin leftSize → Canonical} {rightPoints : Fin rightSize → Canonical}
variable (leftReadings : PointReadings leftData.anchors leftData.offsets leftPoints)
variable (rightReadings : PointReadings rightData.anchors rightData.offsets rightPoints)
variable (leftFirst : Fin leftSize) (rightFirst : Fin rightSize)
variable (leftStart : leftPoints leftFirst = start) (rightStart : rightPoints rightFirst = start)

/-- One exact original attempt and gap-reading factory, with success derived on those same cached values. -/
abbrev CachedGap :=
  Σ attempted : {value : Attempt leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
      leftReadings rightReadings leftFirst rightFirst leftStart rightStart (finish := finish) //
    value = attempt leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
      leftReadings rightReadings leftFirst rightFirst leftStart rightStart (finish := finish)},
  {value : Attempt.GapReading attempted.val // value = Attempt.readGap attempted.val} × Attempt.Gap attempted.val

/-- Execute one original covered attempt and one gap read, preserving both independent old numerical banks. -/
def cacheGap (covered : EndInside leftData rightData leftReadings rightReadings leftFirst rightFirst
    (finish := finish)) :
    CachedGap leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
      leftReadings rightReadings leftFirst rightFirst leftStart rightStart (finish := finish) :=
  let attempted : {value : Attempt leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
      leftReadings rightReadings leftFirst rightFirst leftStart rightStart (finish := finish) //
    value = attempt leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
      leftReadings rightReadings leftFirst rightFirst leftStart rightStart (finish := finish)} :=
    ⟨attempt leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
      leftReadings rightReadings leftFirst rightFirst leftStart rightStart (finish := finish), rfl⟩
  let reading : {value : Attempt.GapReading attempted.val // value = Attempt.readGap attempted.val} :=
    ⟨Attempt.readGap attempted.val, rfl⟩
  let gap := Attempt.gapOfCovered attempted.val reading.val covered
  ⟨attempted, reading, gap⟩

namespace CachedGap

variable {leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData}
variable {leftReadings rightReadings leftFirst rightFirst leftStart rightStart}
variable (cached : CachedGap leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
  leftReadings rightReadings leftFirst rightFirst leftStart rightStart (finish := finish))

/-- Read the whole actual attempt and its original retained inputs. -/
@[expose] def attempted : Attempt leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
    leftReadings rightReadings leftFirst rightFirst leftStart rightStart (finish := finish) := cached.1.val

/-- Read the same already computed success reading. -/
@[expose] def reading : Attempt.GapReading cached.attempted := cached.2.1.val

/-- Read the successful old-bank difference without another primitive evaluation. -/
@[expose] def value : Canonical := cached.2.2.val

/-- The complete attempt is its original actual factory. -/
theorem attempted_eq : cached.attempted = attempt leftPoint rightPoint leftPointInside leftEntry rightEntry joined
    leftData rightData leftReadings rightReadings leftFirst rightFirst leftStart rightStart (finish := finish) :=
  cached.1.property

/-- The stored reading is the original readGap on the same retained attempt. -/
theorem reading_eq : cached.reading = Attempt.readGap cached.attempted := cached.2.1.property

/-- The scalar is the difference of the two original old reading occurrences. -/
theorem value_eq : cached.value = leftReadings.values leftFirst - rightReadings.values rightFirst :=
  cached.2.2.property.1

/-- The scalar belongs to the SAME actual successful preparation, never an uncovered replacement. -/
theorem prepared : Attempt.PreparedGap cached.attempted cached.value := cached.2.2.property.2

end CachedGap

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction
