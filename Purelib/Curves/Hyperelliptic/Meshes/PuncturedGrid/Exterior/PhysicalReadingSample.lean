module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Integration.Polynomial.Rectangle.SampleReadback
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSideOwnerRequest
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Batteries.Logic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Integration.Path

open Purelib.Integration.Polynomial.Rectangle

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Common cached reading samples, independent of the geometric representation of a side. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Coordinate} {minimum
    stage fine index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}

variable {data : FirstData occurrence
  index} {otherData : SecondData
  occurrence other index}

open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)

set_option genInjectivity false in
/-- A conjugate centered physical sample retaining both original point-reading banks and exact pointwise value
readbacks.

The original anchor and offset owners are preserved at the supplied physical points. -/
structure PhysicalReadingSample (data : PairedFragmentValues.FirstData occurrence index) (otherData :
  PairedFragmentValues.SecondData occurrence other index)
    {count : Nat} (points : Fin (count + 1) → InverseRootPolynomial.Gaussian) (values : Fin (count + 1) →
      Stokes.PrimitivePoint) where
  /-- The original first-differential readings at the retained physical points. -/ first :
    RectangularPointReadings.PointReadings data.anchors data.offsets points
  /-- The original second-differential readings at the same retained physical points. -/ second :
    RectangularPointReadings.PointReadings otherData.anchors otherData.offsets points
  /-- The first retained readings equal the supplied left primitive values at every vertex. -/ first_eq : ∀ vertex,
    first.values vertex = (values vertex).left
  /-- The second retained readings equal the supplied right primitive values at every vertex. -/ second_eq : ∀ vertex,
    second.values vertex = (values vertex).right
  /-- The cached conjugate centered sample on the exact original paired values. -/ original :
    CenteredBilinearPath.Sample (fun vertex => ConjugateIncrementComparison.conjugateFirst (values vertex))

constructive_injectivity PhysicalReadingSample

namespace PhysicalReadingSample

/-- Build the area from cached reading vectors and transport only pointwise certificates. No primitive is evaluated
again to establish the readback. -/
def build {count : Nat} {points : Fin (count + 1) → InverseRootPolynomial.Gaussian}
    {values : Fin (count + 1) → Stokes.PrimitivePoint}
    (first : RectangularPointReadings.PointReadings data.anchors data.offsets points)
    (second : RectangularPointReadings.PointReadings otherData.anchors otherData.offsets points)
    (firstEq : ∀ vertex, first.values vertex = (values vertex).left)
    (secondEq : ∀ vertex, second.values vertex = (values vertex).right) :
    PhysicalReadingSample data otherData points
      values :=
  let original := CenteredBilinearPath.Sample.build (fun vertex => ConjugateIncrementComparison.conjugateFirst
    ⟨first.values vertex, second.values vertex⟩)
  ⟨first, second, firstEq, secondEq, SampleReadback.Sample.readback original (fun vertex =>
    congrArg ConjugateIncrementComparison.conjugateFirst (congrArg₂ PrimitivePoint.mk (firstEq vertex) (secondEq
      vertex)))⟩

end PhysicalReadingSample

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
