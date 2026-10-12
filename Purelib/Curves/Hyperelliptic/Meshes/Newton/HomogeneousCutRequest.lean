module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousPhysicalComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateCutCorrection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalHoleReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
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
import Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Polynomial.Geometry.Grid

open Purelib.Topology.Surface.Sewing

public section

/-! All conjugate cut-correction requests share one later stage, retaining
their certificates for the existing cached period sample and actual holes. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousCutRequest

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest (EnergyPreparation)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}
  {preparation : NewtonPreparation
    base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {newSheet : Fin 2}
  {excision : AllHoleExcision grid current}
  {magnitudes : Purelib.Data.Vector.DependentVector (fun basis : Fin genus =>
    FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential basis))}
  {error : Rational} {floor : Nat}

namespace Request

/-- The certificate names the retained pair request and its actual excision list. Physical holes remain in the
expression throughout the tail. -/
@[expose] def CutAccurate (request : HomogeneousPhysicalComparison.Request prepared newSheet excision magnitudes error
  floor)
    (first second : Fin genus) (bound : Fraction.Rational) (index : Nat) : Prop :=
  ∀ stage (cache : RegularMeshes.Numerics domains stage)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get first) current.mesh)
    (right : TrianglePrimitiveReadings.TriangleReadings (cache.get second) current.mesh)
    (leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values)
    (rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values)
    (pair : SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
    (sample : ConjugatePhysicalRequest.PairRequest.Sample left right leftSurface rightSurface pair ((request.entries.get
        first).get second)),
    index ≤ stage → Data.Gaussian.Norm.Basic.normSq (sample.correction + CellBoundary.sumValues
      (fun entry => entry.conjugatePhysicalHoleArea left right) excision.entries) < bound

/-- The complete indexed family of cut-correction certificates for the original retained differential-pair requests. -/
@[expose] def CutEntries (request : HomogeneousPhysicalComparison.Request prepared newSheet excision magnitudes error
  floor) (bound : Fraction.Rational) (minimum : Nat) :=
  Data.Vector.DependentVector fun first : Fin genus => Data.Vector.DependentVector fun second : Fin genus =>
    {index : Nat // minimum ≤ index ∧ CutAccurate
      request first second bound index}

/-- The common stage pays every retained differential-pair cut certificate. -/
@[expose] def CutEntries.IndexBound {request : HomogeneousPhysicalComparison.Request prepared newSheet excision
  magnitudes error floor}
    {bound : Fraction.Rational} {minimum : Nat} (entries :
      CutEntries request bound minimum) (index : Nat) :
      Prop :=
  ∀ first second, ((entries.get first).get second).val ≤ index

set_option genInjectivity false in
/-- All original differential-pair cut certificates together with their shared paid stage.

The stage also pays the original period request and requested minimum, and each entry retains its physical-hole
expression. -/
structure CutRequest (request : HomogeneousPhysicalComparison.Request prepared newSheet excision magnitudes error floor)
  (bound : Fraction.Rational) (minimum : Nat) where
  /-- The complete retained matrix of differential-pair cut certificates. -/ entries :
    CutEntries request bound minimum
  /-- The common stage paying all retained cut certificates and original period data. -/ index : Nat
  /-- The requested minimum stage is paid. -/ minimum_le : minimum ≤ index
  /-- The original homogeneous period request is paid. -/ period_le : request.index ≤ index
  /-- Every retained differential-pair cut request is paid. -/ index_ge :
    Curves.Hyperelliptic.Meshes.Newton.HomogeneousCutRequest.Request.CutEntries.IndexBound entries index

constructive_injectivity CutRequest

/-- Prepare all original pairwise cut-correction certificates on the same sewing preparation and cache their common paid
stage. -/
@[expose] def CutRequest.build (request : HomogeneousPhysicalComparison.Request prepared newSheet excision magnitudes
  error floor)
    (sewing : SewnEnergyRequest.EnergyPreparation current.cutPolygon domains)
    (bound : Fraction.Rational) (positive : 0 < bound) (minimum : Nat) :
      CutRequest request bound minimum := by
  let entries : CutEntries request bound minimum :=
    DependentVector.ofFn fun first => DependentVector.ofFn fun second =>
    ((request.entries.get first).get second).cutCorrectionRequest (sewing.pair first second) bound positive minimum
  let maximum := entries.maximum (fun _ row => row.maximum fun _ entry => entry.val)
  let index := max (max minimum request.index) maximum
  refine ⟨entries, index, (Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_left _ _),
    (Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_left _ _), ?_⟩
  intro first second
  exact ((entries.get first).get_le_maximum (fun _ entry => entry.val) second).trans
    ((entries.get_le_maximum (fun _ row => row.maximum fun _ entry => entry.val) first).trans (Nat.Order.le_max_right _
      _))

end Request
end Purelib.Curves.Hyperelliptic.Meshes.Newton.HomogeneousCutRequest
