module
import Purelib.Data.Nat.Order
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
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

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Use one radial parameter bank for all retained surface components.
Each component keeps its own trace and physical endpoint potentials. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples

open Purelib.Riemann.Normalization

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}

variable {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor index minimum
    readingIndex : Nat}
  {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

variable {energyFloor radialDepth : Nat}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Plans

/-- The dependent spine of original radial fan preparations for all surface components.

Each entry keeps its original plan, numerical inputs and acquired root readings at the shared energy floor. -/
def FanPreparations (energyFloor : Nat) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans readingIndex → Type
      2
  | [], _, _ => PUnit
  | head :: tail, plans, readings =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.FanPreparation head.request
        plans.1.plans plans.1.inputs readings.1 energyFloor ×
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations
          energyFloor tail plans.2 readings.2

/-- Prepare all original component fans from their retained plans and already acquired readings. -/
def prepareFans (energyFloor : Nat) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries plans
      readings
  | [], _, _ => PUnit.unit
  | head :: tail, plans, readings =>
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.prepareFans
        head.request plans.1.plans plans.1.inputs readings.1 energyFloor,
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.prepareFans energyFloor
          tail plans.2 readings.2)

/-- Compute the shared radial depth paying every retained component fan and the supplied energy floor. -/
def FanPreparations.depth :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries plans
      readings → Nat
  | [], _, _, _ => energyFloor
  | head :: tail, plans, readings, fans =>
      max (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations.depth
        head.retained.anchors head.retained.sources head.request.schedule.bank plans.1.plans plans.1.inputs readings.1
          fans.1)
        (depth tail plans.2 readings.2 fans.2)

/-- The dependent spine of coefficient-weighted samples on the original component fan preparations.

Every sample uses the same coefficient vector and radial depth while retaining its own original component. -/
def Samples (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (radialDepth : Nat) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries plans
      readings → Type 2
  | [], _, _, _ => PUnit
  | _ :: tail, plans, readings, fans =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans.1 coefficients
        radialDepth × Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples
        coefficients radialDepth tail plans.2 readings.2 fans.2

open Purelib.Data in
/-- Sample every retained component with one common radial parameter bank.

The branch condition and paid reading and radial thresholds supply each original fan's sampling requirements. -/
def sample (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (parameters :
  Path.Dyadic.RadialTriangles.Parameters radialDepth)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      → (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex) →
    (fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.FanPreparations energyFloor entries
      plans readings) →
    plans.stage entries ≤ readingIndex → fans.depth entries plans readings ≤ radialDepth →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.Samples coefficients radialDepth entries
      plans readings fans
  | [], _, _, _, _, _ => PUnit.unit
  | head :: tail, plans, readings, fans, readingLater, radialLater =>
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.sample head.request
        plans.1.plans plans.1.inputs readings.1 fans.1 coefficients parameters branch
        (plans.1.stage_eq.symm.trans_le ((Nat.Order.le_max_left ..).trans readingLater)) ((Nat.Order.le_max_left
          ..).trans radialLater),
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples.Plans.sample coefficients
          parameters branch tail plans.2 readings.2 fans.2
          ((Nat.Order.le_max_right ..).trans readingLater) ((Nat.Order.le_max_right ..).trans radialLater))

end Plans
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceSamples
