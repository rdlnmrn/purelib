module
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Approximation.Budget.VanishingSamples
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.WeightedPeriodNames
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ZeroPeriods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Polynomial.Geometry.Grid.Extension
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

section

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Budget

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Geometric

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ZeroPeriods.PeriodMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid

open Purelib.Data.Rat

open Purelib.Riemann.Meshes

open Purelib.Riemann.Periods

open Purelib.RootIsolation.SquareRoot.Grid

public section

/-! Original regular-face zero periods with the enlarged grid's actual
cached owners. Subdivision changes neither the selected sheet nor the
original program used in the finite tail estimate. -/

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Periods.WeightedPeriodNames (programApproximation)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain ContainedPeriod PeriodMesh)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  (face : RegularFace bank) {base : FramedPuncturedGrid
    curve branches higher}
  (included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion bank.grid base.bank.grid)
  (frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FacePeriods

/-- Reuse the entire cached list; restrict only its coverage certificate. No root isolation or owner selection is
repeated. -/
@[expose] def includedFrames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid :=
  ⟨frames.entries, fun point member => frames.covers point (included.vertex member)⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FacePeriods

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace

/-- Prepare the original regular face using the enlarged grid's exact retained frame cache. -/
@[expose] def includedModels : BranchCellBank.FaceModels
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FacePeriods.includedFrames included frames) face :=
  FaceModels.build (Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FacePeriods.includedFrames included frames) face

/-- Prepare the original face boundary period on the enlarged grid's actual retained owner at the supplied sheet. -/
@[expose] def includedPeriod (sheet : Fin 2) (source : Differentials.Basic.Differential genus) :
    Periods.ContainedPeriod (face.includedModels included frames) sheet source :=
  Periods.boundaryPeriod (face.includedModels included frames) sheet source

/-- The old boundary starts with the literal new-grid owner at this sheet, not an independently prepared owner with
merely equal coordinates. -/
theorem included_owner (sheet : Fin 2) :
    (face.includedModels included frames).frame.owners sheet =
      (frames.frameAt face.cell.box.anchor (included.vertex (face.cell.anchor_mem face.member))).owners sheet := rfl

/-- Attach shared enlarged-grid face assignments to the exact resplit original face boundary and its retained owner. -/
@[expose] def includedFaces {vertices : LiftedVertices.VertexBank base.bank.grid} {edges : RootEdgeBank
  frames}
    (mesh : GridLiftedMesh.LiftedMesh vertices edges base.faces) (sheet : Fin 2) :
    FramedPuncturedGrid.OwnerWalkFaces mesh
      (included.resplit face.boundary (face.cell.anchor_mem face.member))
      ((face.includedModels included frames).frame.owners sheet) :=
  OwnerWalkFaces.ofSheet mesh _
    (included.vertex (face.cell.anchor_mem face.member)) sheet
    ⟨NamedEquivalent.refl _⟩

/-- An automatic all-later bound on the actual original program. The finite zero-sample producer and its movement
estimate choose the threshold; no smallness certificate or successful search is supplied by the caller. -/
@[expose] def includedZeroTail (sheet : Fin 2) (source : Differentials.Basic.Differential genus)
    (differential : Fin genus) (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
    Gaussian.Equivalence.Comparison
      (WeightedPeriodNames.programApproximation ((face.includedPeriod included frames sheet source).period.program
        differential).integral).toApproximation
      (GeometricApproximation.exact 0).toApproximation minimum 0 target :=
  let loop := face.includedPeriod included frames sheet source
  let domain := PeriodDomain.build (face.includedModels included frames) sheet
  let prepared := PeriodMesh.build domain loop (PeriodMatrix.standardDifferential differential)
  (VanishingSamples.equivalentZero (WeightedPeriodNames.programApproximation (loop.period.program
    differential).integral)
    (fun allowance valid floor =>
      (ZeroRequest.acquire prepared allowance valid floor).toZeroSample)).compare
    minimum 0 target positive

/-- Every later actual sample of the retained original face-period program satisfies the automatically requested
zero-tail bound. -/
theorem included_sample_small (sheet : Fin 2) (source : Differentials.Basic.Differential genus)
    (differential : Fin genus) (target : Fraction.Rational) (positive : 0 < target) (minimum stage : Nat)
    (later : (face.includedZeroTail included frames sheet source differential target positive minimum).leftIndex ≤
      stage) :
    Data.Gaussian.Norm.Basic.normSq ((((face.includedPeriod included frames sheet source).period.program
      differential).integral.model stage).integralSample) < target := by
  have bound := (face.includedZeroTail included frames sheet source differential target positive minimum).close
    later (Nat.le_refl _)
  change Data.Gaussian.Norm.Basic.normSq (_ - 0) < target at bound
  rw [show (_ - 0 : Data.Gaussian.Basic.Canonical) = _ by ring1] at bound
  exact bound

end Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace

end
