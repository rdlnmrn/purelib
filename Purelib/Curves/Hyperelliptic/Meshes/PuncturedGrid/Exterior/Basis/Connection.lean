module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonBankReturn
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! The requested homogeneous trace bound on an actual surface component,
using its retained common-basis preparation and one shared radial bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection

open Purelib.Data

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {bounds : ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Preparation.CommonBasisPreparation prepared}
  {basis : ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : InverseRootPolynomial.Coordinate} {coverFloor floor index minimum stage
    energyFloor radialDepth : Nat}
  {box : Rational.Box} {capSample : Cap.Primitives.Sample cap
    differential index box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace CommonBasisRequest

variable {request : Preparation.CommonBasisRequest retained basis
  target coefficientTarget coverFloor floor}
  {plans : request.Plans capSample polynomials minimum} {inputs : retained.Inputs index}
  {readings : Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
    request.schedule.bank plans inputs stage}

/-- Fan requests are prepared from the already acquired component readings. -/
@[expose] def FanPreparation (request : Preparation.CommonBasisRequest
  retained basis target coefficientTarget coverFloor floor)
    (plans : request.Plans capSample polynomials minimum) (inputs : retained.Inputs index)
    (readings : Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
      request.schedule.bank plans inputs stage)
    (energyFloor : Nat) :=
  Disk.Basis.CommonParentSamples.FanPreparations energyFloor retained.anchors
    retained.sources request.schedule.bank plans inputs readings

/-- Prepare radial fan requests from the already acquired common-parent readings and their exact numerical inputs. -/
@[expose] def prepareFans (request : Preparation.CommonBasisRequest
  retained basis target coefficientTarget coverFloor floor)
    (plans : request.Plans capSample polynomials minimum) (inputs : retained.Inputs index)
    (readings : Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
      request.schedule.bank plans inputs stage)
    (energyFloor : Nat) : FanPreparation
      request plans inputs readings energyFloor :=
  Disk.Basis.CommonParentSamples.prepareFans energyFloor retained.anchors
    retained.sources request.schedule.bank plans inputs readings

variable {fans :
  FanPreparation request
  plans inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- The retained coefficient-weighted parent samples from the exact fan preparations at one radial depth. -/
@[expose] def ParentSamples (fans :
  FanPreparation request plans inputs
  readings energyFloor)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (radialDepth : Nat) :=
  Disk.Basis.CommonParentSamples.Samples coefficients radialDepth retained.anchors
    retained.sources request.schedule.bank plans inputs readings fans

set_option genInjectivity false in
/-- The actual common-parent samples together with their paid connection at the original target.

The connection retains the same parent bank, acquired readings and chosen coefficient vector. -/
structure Sampled (fans : FanPreparation
  request plans inputs readings energyFloor)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (radialDepth : Nat) where
  /-- The original retained coefficient-weighted samples of the common parent bank. -/ parents :
    ParentSamples fans coefficients
    radialDepth
  /-- The paid connection on these exact retained parent samples. -/ connection :
    Disk.Basis.CommonParentConnection.Samples.PaidConnection parents target

constructive_injectivity Sampled

/-- All source/chart corrections and inter-parent joins are paid by the
component's original request. Sheet return and surface-path transport remain
separate obligations on the resulting literal trace. -/
@[expose] def sample (request : Preparation.CommonBasisRequest
  retained basis target coefficientTarget coverFloor floor)
    (plans : request.Plans capSample polynomials minimum) (inputs : retained.Inputs index)
    (readings : Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
      request.schedule.bank plans inputs stage)
    (fans : FanPreparation request plans
      inputs readings energyFloor)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (parameters :
      Path.Dyadic.RadialTriangles.Parameters radialDepth)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (readingLater : request.readingStage plans ≤ stage)
    (radialLater : fans.depth retained.anchors retained.sources request.schedule.bank plans inputs readings ≤
      radialDepth) :
    Sampled fans coefficients
      radialDepth :=
  let parents := Disk.Basis.CommonParentSamples.sample coefficients parameters branch
    retained.anchors retained.sources request.schedule.bank
    plans inputs readings fans radialLater
  ⟨parents, Disk.Basis.CommonParentConnection.Samples.connectPaid request.allocation
    parents request.schedule.joins branch
    (request.joins_later plans readingLater)⟩

end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
