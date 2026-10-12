module
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest
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
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Curves

open Purelib.Geometry

open Purelib.Riemann

@[expose] public section

/-! Share cap polynomials and numerical inputs across every retained surface
component, then acquire all roots at one computed reading stage. -/
open Purelib.Data

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans

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

namespace Entry

set_option genInjectivity false in
/-- One retained component's numerical inputs, common-parent plans and cached reading threshold.

The exact original entry, supplied cap sample and basis polynomials index all retained data. -/
structure Plan (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
  (differential := differential) basis target coefficientTarget coverFloor floor)
    (capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (minimum : Nat) where
  /-- The retained numerical bank for this exact original component preparation. -/ inputs : entry.retained.Inputs index
  /-- The original common-parent plans on the supplied cap sample and basis polynomials. -/ plans : entry.request.Plans
    capSample polynomials minimum
  /-- The cached complete reading threshold for these plans. -/ stage : Nat
  /-- The cached threshold is exactly the original request's reading stage on these retained plans. -/ stage_eq : stage
    = entry.request.readingStage plans

constructive_injectivity Plan

/-- Prepare the original component plans and cache their shared numerical inputs and reading stage. -/
def Plan.build (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
  (differential := differential) basis target coefficientTarget coverFloor floor)
    (capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (minimum : Nat) : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Entry.Plan entry capSample
      polynomials minimum :=
  let plans := entry.request.plans capSample polynomials minimum
  ⟨entry.retained.inputs index, plans, entry.request.readingStage plans, rfl⟩

variable {entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
  (differential := differential) basis target coefficientTarget coverFloor floor}

/-- The root readings on the exact retained plans and numerical inputs at one common stage. -/
def Plan.Readings (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Entry.Plan entry capSample
  polynomials minimum) (stage : Nat) :=
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings
    entry.retained.anchors entry.retained.sources entry.request.schedule.bank plan.plans plan.inputs stage

end Entry

/-- The dependent plan spine following the complete original surface-entry list. -/
def Plans (capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (minimum : Nat) :
    List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains) (differential :=
      differential) basis target coefficientTarget coverFloor floor) → Type 2
  | [] => PUnit
  | head :: tail => Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Entry.Plan head capSample polynomials
    minimum × Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials
    minimum tail

namespace Plans

/-- Prepare every original surface entry with the same supplied cap polynomials and minimum stage. -/
def build (capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (minimum : Nat) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries
  | [] => PUnit.unit
  | head :: tail => (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Entry.Plan.build head capSample
    polynomials minimum, Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.build
    capSample polynomials minimum tail)

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans
/-- Compute the common reading threshold of the retained plan spine, including its supplied minimum. -/
def stage :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries → Nat
  | [], _ => minimum
  | _ :: tail, plans => max plans.1.stage (stage tail plans.2)

/-- The dependent reading spine on every original retained component plan at one shared stage. -/
def Readings :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries → Nat →
      Type 2
  | [], _, _ => PUnit
  | _ :: tail, plans, stage => Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Entry.Plan.Readings
    plans.1 stage × Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings tail
    plans.2 stage

end

/-- Acquire all original component root readings at the paid common stage.

The original entry maximum pays model acquisition, while the retained plan maximum pays all internal and closing reads.
-/
def acquire (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (readingIndex :
  Nat) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry (domains := domains)
      (differential := differential) basis target coefficientTarget coverFloor floor)) →
    (plans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans capSample polynomials minimum entries)
      →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfaceRequest.Entry.maximum entries ≤ index → plans.stage entries
      ≤ readingIndex → Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.Readings entries plans
      readingIndex
  | [], _, _, _ => PUnit.unit
  | head :: tail, plans, modelLater, readingLater =>
      (head.request.acquire capSample polynomials plans.1.plans plans.1.inputs branch
        ((Nat.Order.le_max_left ..).trans modelLater) readingIndex
        (plans.1.stage_eq.symm.trans_le ((Nat.Order.le_max_left ..).trans readingLater)),
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans.Plans.acquire branch readingIndex
          tail plans.2 ((Nat.Order.le_max_right ..).trans modelLater)
          ((Nat.Order.le_max_right ..).trans readingLater))

end Plans
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SurfacePlans
