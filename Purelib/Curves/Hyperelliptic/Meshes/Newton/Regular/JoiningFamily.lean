module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateChordPolygons
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisArcRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

public section

/-! All basis-pair joining requests reuse the retained preparation vector. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningFamily

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Geometry
open Purelib.Riemann

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningRequest.RegularJoiningRequest (evaluate accurate)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- Pointwise ownership certificate for the shared executable preparation bank. -/
@[expose] def CanonicalJoiningPreparations (preparations :
  PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains) : Prop :=
  ∀ first, preparations.get first =
    PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
    regular domains (Periods.PeriodMatrix.standardDifferential first)

/-- The executable basis preparation bank has the canonical preparation at every original basis index. -/
theorem canonicalJoiningPreparations_build (regular : Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (domains : PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars) :
    CanonicalJoiningPreparations
      (PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations.build regular domains) := by
  intro first
  exact Vector.DependentVector.ofFn_get _ first

/-- The dependent bank of joining requests for every ordered pair of original basis magnitude banks. -/
@[expose] def RegularJoiningEntries (regular : Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (magnitudes : Vector.DependentVector (fun basis : Fin genus =>
      PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential basis)))
    (error : Fraction.Rational) (floor : Nat) :=
  Vector.DependentVector fun first : Fin genus => Vector.DependentVector fun second : Fin genus =>
    JoiningRequest.RegularJoiningRequest (paired := paired) regular (magnitudes.get
      first) (magnitudes.get second) error floor

namespace RegularJoiningEntries
variable {magnitudes : Vector.DependentVector (fun basis : Fin genus =>
  PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  (Periods.PeriodMatrix.standardDifferential basis))}
  {error : Fraction.Rational} {floor : Nat}

/-- Every ordered basis-pair request is ready by the supplied common model stage. -/
@[expose] def IndexBound (entries : RegularJoiningEntries (paired :=
  paired) regular magnitudes error floor) (stage : Nat) : Prop :=
  ∀ first second, ((entries.get first).get second).index ≤ stage

/-- Every ordered basis-pair cap request is ready by the supplied common reading stage. -/
@[expose] def ReadingBound (entries : RegularJoiningEntries (paired :=
  paired) regular magnitudes error floor) (stage : Nat) : Prop :=
  ∀ first second, ((entries.get first).get second).caps.readingIndex ≤ stage

end RegularJoiningEntries

set_option genInjectivity false in
/-- All ordered basis-pair joining requests on the same retained preparation vector.

Separate cached model and reading maxima retain the supplied floor and certify readiness of every original pair. -/
structure RegularJoiningFamily (preparations :
  PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular domains)
    (magnitudes : Vector.DependentVector (fun basis : Fin genus =>
      PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential basis)))
    (error : Fraction.Rational) (floor : Nat) where
  /-- Each retained basis preparation is the canonical constructor for its original row. -/ canonical :
    CanonicalJoiningPreparations preparations
  /-- The dependent request bank indexed by the original ordered basis pairs. -/ entries :
    RegularJoiningEntries (paired := paired) regular magnitudes error
    floor
  /-- The cached common model stage for every pair. -/ index : Nat
  /-- The model stage is the caller floor combined with the exact maximum of all pair requests. -/ index_eq : index =
    max floor (entries.maximum fun _ row => row.maximum fun _ request => request.index)
  /-- The common model stage respects the supplied floor. -/ floor_le : floor ≤ index
  /-- Every retained pair request is ready by the cached model stage. -/ index_ge : entries.IndexBound index
  /-- The cached common cap-reading stage. -/ readingIndex : Nat
  /-- The reading stage is the caller floor combined with the exact maximum of all retained pair reading stages. -/
    readingIndex_eq : readingIndex = max floor (entries.maximum fun _ row => row.maximum fun _ request =>
    request.caps.readingIndex)
  /-- Every retained pair cap request is ready by the common reading stage. -/ reading_ge : entries.ReadingBound
    readingIndex

constructive_injectivity RegularJoiningFamily

namespace RegularJoiningFamily
variable {preparations : PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations regular
  domains}
  {magnitudes : Vector.DependentVector (fun basis : Fin genus =>
    PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential basis))}
  {error : Fraction.Rational} {floor : Nat}

/-- Reuse the same preparations as the physical-surface schedule. Only the
pair-specific requests and their finite maxima are constructed here. -/
@[expose] def build (preparations : PuncturedGrid.Exterior.BasisArcRequest.BasisArcPreparations
  regular domains) (canonical : CanonicalJoiningPreparations
  preparations)
    (magnitudes : Vector.DependentVector (fun basis : Fin genus =>
      PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential basis)))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    RegularJoiningFamily (paired := paired) preparations magnitudes
      error floor := by
  let entries : RegularJoiningEntries (paired := paired) regular
    magnitudes error floor := Vector.DependentVector.ofFn fun first =>
    Vector.DependentVector.ofFn fun second =>
      JoiningRequest.RegularJoiningRequest.build regular (magnitudes.get first)
      (magnitudes.get second)
      (preparations.get first) (preparations.get second) (canonical first) (canonical second) error positive floor
  let index := max floor (entries.maximum fun _ row => row.maximum fun _ request => request.index)
  let readingIndex := max floor (entries.maximum fun _ row => row.maximum fun _ request => request.caps.readingIndex)
  refine ⟨canonical, entries, index, rfl, Nat.Order.le_max_left _ _, ?_, readingIndex, rfl, ?_⟩
  · intro first second
    exact ((entries.get first).get_le_maximum (fun _ request => request.index) second).trans
      ((entries.get_le_maximum (fun _ row => row.maximum fun _ request => request.index) first).trans
        (Nat.Order.le_max_right _ _))
  · intro first second
    exact ((entries.get first).get_le_maximum (fun _ request => request.caps.readingIndex) second).trans
      ((entries.get_le_maximum (fun _ row => row.maximum fun _ request => request.caps.readingIndex) first).trans
        (Nat.Order.le_max_right _ _))

variable (request : RegularJoiningFamily (paired := paired)
  preparations magnitudes error floor)
  {stage depth readingIndex : Nat} {box : Rational.Box}

/-- Every pair consumes the already supplied common cap and face samples. -/
@[expose] def Evaluations (polynomials :
  PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box)
    (cache : Vector.DependentVector (fun basis : Fin genus =>
      PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (Periods.PeriodMatrix.standardDifferential
      basis) stage domains))
    (depth readingIndex : Nat) :=
  Vector.DependentVector fun first : Fin genus => Vector.DependentVector fun second : Fin genus =>
    PuncturedGrid.Exterior.PairedCapRequest.Evaluation ((request.entries.get
      first).get second).caps
      (polynomials.get first) (polynomials.get second) (cache.get first) (cache.get second) depth depth readingIndex

/-- Evaluate every retained pair using the supplied common cap polynomials and face bank at the paid shared stages. -/
@[expose] def evaluate (polynomials : PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials
  cap stage box)
    (cache : Vector.DependentVector (fun basis : Fin genus =>
      PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (Periods.PeriodMatrix.standardDifferential
      basis) stage domains))
    (depth readingIndex : Nat) (later : request.index ≤ stage) (readingLater : request.readingIndex ≤ readingIndex) :
    request.Evaluations polynomials cache depth readingIndex :=
  Vector.DependentVector.ofFn fun first => Vector.DependentVector.ofFn fun second =>
    ((request.entries.get first).get second).evaluate (polynomials.get first) (polynomials.get second)
      (cache.get first) (cache.get second) depth depth readingIndex
      ((request.index_ge first second).trans later) ((request.reading_ge first second).trans readingLater)

/-- Pointwise transport preserves the supplied attachment; only its ownership
proof changes from the shared vector readback to the canonical constructor. -/
theorem accurate
    {polynomials : PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage box}
    {cache : Vector.DependentVector (fun basis : Fin genus =>
      PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (Periods.PeriodMatrix.standardDifferential
      basis) stage domains)}
    (evaluated : request.Evaluations polynomials cache depth readingIndex)
    (triangles : Vector.DependentVector (fun basis : Fin genus =>
      PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get basis) current.mesh))
    (attachments : Vector.DependentVector (fun first =>
      PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment (preparations.get first)))
    (later : request.index ≤ stage) (newSheet : Fin 2) (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (first second : Fin genus) :
    Gaussian.Norm.Basic.normSq (2 *
      ConjugatePhysicalRequest.exterior (paired := paired) newSheet
      (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh (triangles.get first).values)
      (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh (triangles.get second).values)
        -
      PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea
        (attachments.get first) (polynomials.get first) (polynomials.get second)) < error := by
  have applyTo (prepared :
    PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains (Periods.PeriodMatrix.standardDifferential first))
      (equal : prepared =
        PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation.build
        regular domains (Periods.PeriodMatrix.standardDifferential first))
      (attached : PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared) :
      Gaussian.Norm.Basic.normSq (2 *
        ConjugatePhysicalRequest.exterior (paired := paired)
        newSheet
        (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh (triangles.get first).values)
        (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh (triangles.get
          second).values) -
        PuncturedGrid.Exterior.ConjugateChordPolygons.CapAttachment.conjugateJoiningArea attached
          (polynomials.get first) (polynomials.get second)) < error := by
    cases equal
    exact ((request.entries.get first).get second).accurate ((evaluated.get first).get second)
      (triangles.get first) (triangles.get second) ((request.index_ge first second).trans later) newSheet attached
        degree
  exact applyTo _ (request.canonical first) (attachments.get first)

end RegularJoiningFamily
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.JoiningFamily
