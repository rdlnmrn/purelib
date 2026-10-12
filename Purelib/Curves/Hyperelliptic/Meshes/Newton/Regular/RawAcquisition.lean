module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.LinearAlgebra.Gaussian.Energy

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.NewtonCombinedPeriodArea
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.RawCoercivity
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.NewtonRawPeriodSamples
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.RootContinuation.NewtonRawEnergyBudget
import Purelib.Riemann.RootContinuation.NewtonRawEnergyGrid
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

public section

/-! Acquire the numerical and reciprocal polynomial banks at any certified
later stage, then construct the complete regular raw sample package. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawAcquisition

open Purelib.Curves
open Purelib.Data.Rat
open Purelib
open Purelib.Riemann

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  (observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations base.bank.toBranchCellBank)
  (preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank)
    (radius : Fraction.Rational)
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)

variable {newSheet : Fin 2} {floor : Nat}
  (raw : Hyperelliptic.Meshes.Newton.Regular.RawRequest.RegularRawRequest prepared observations preparation radius
    regular newSheet floor)

set_option genInjectivity false in
/-- Retain the complete regular raw samples and the numerical banks they consume at one stage.

The polynomial bank and primitive cache are stored together with the sample package indexed by those exact banks. -/
structure RegularRawAcquisition (stage : Nat) (first : Fin genus) where
  /-- The reciprocal basis polynomials acquired at the retained stage on the original collar box. -/ polynomials :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage collar.box
  /-- The primitive numerical bank on the original retained raw grid domains at that same stage. -/ cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics raw.grid.domains stage
  /-- The regular raw sample package built from these exact acquired polynomial and primitive banks. -/ samples :
    Hyperelliptic.Meshes.Newton.Regular.RawSamples.RegularRawSamples prepared observations preparation radius regular
    raw polynomials cache first

constructive_injectivity RegularRawAcquisition

namespace RegularRawAcquisition

/-- Acquire both numerical banks at a certified later stage and construct the original regular raw sample package.

The degree equality selects the regular even-degree case; all sample certificates retain these same acquired banks. -/
@[expose] def build (stage : Nat) (first : Fin genus) (degree : curve.polynomial.natDegree = 2 * genus + 2)
    (later : raw.index ≤ stage) : Hyperelliptic.Meshes.Newton.Regular.RawAcquisition.RegularRawAcquisition prepared
      observations preparation radius regular raw stage first :=
  let polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap stage
    collar.box := Data.Vector.DependentVector.ofFn fun row =>
    Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample.build cap (Periods.PeriodMatrix.standardDifferential row)
      stage collar.box
  let cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics raw.grid.domains stage :=
    Data.Vector.DependentVector.ofFn fun row =>
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build
      (Periods.PeriodMatrix.standardDifferential row) stage raw.grid.domains
  let samples := Hyperelliptic.Meshes.Newton.Regular.RawSamples.RegularRawSamples.build prepared observations
    preparation radius regular raw polynomials cache first degree later
  ⟨polynomials, cache, samples⟩

variable {prepared observations preparation radius regular raw} {stage : Nat} {first : Fin genus}

/-- The acquired finite samples have the positive homogeneous observation margin. -/
theorem raw_lower (acquired : Hyperelliptic.Meshes.Newton.Regular.RawAcquisition.RegularRawAcquisition prepared
  observations preparation radius regular raw stage first)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (later : raw.index ≤ stage)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    let values := fun basis => Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation raw.grid.lifted.mesh
      (acquired.samples.period.triangles.get basis).values
    let aMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix prepared
      raw.grid.allocated.family.single.grid.shrunk.included raw.grid.lifted.edges raw.grid.lifted.vertices newSheet
      values false
    let bMatrix := Periods.NewtonCombinedPeriodArea.resplitPeriodMatrix prepared
      raw.grid.allocated.family.single.grid.shrunk.included raw.grid.lifted.edges raw.grid.lifted.vertices newSheet
      values true
    Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      LinearAlgebra.Gaussian.Energy.unnormalizedEnergyForm coefficients aMatrix bMatrix :=
  Hyperelliptic.Meshes.Newton.Regular.RawSamples.RegularRawSamples.remaining_regular_raw_lower
    acquired.samples coefficients later degree Hyperelliptic.Integration.Energy.Prepared.canonicalSurfaceFace

end RegularRawAcquisition
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RawAcquisition
