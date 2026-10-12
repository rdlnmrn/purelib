module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Polynomial.Geometry.Grid.Extension
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
public import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

/-!
# Corrected original period requests on the Newton excision grid

Both comparisons keep the original ordered bank's programs. The Newton
grid supplies only the splitting axes, regular cells and local sheet frames.
-/

namespace Purelib.Riemann.Periods.NewtonPairedPeriodFragments

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments (IncludedFragments)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials)
open Purelib.Riemann.Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds (CoveredPeriodRequest)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
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
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {bandTarget radius : Rational}

open Purelib.Polynomial in
/-- The original grid coordinates are included in the retained Newton punctured grid. -/
public theorem newton_included (grid : NewtonGrid preparation bandTarget radius) :
    Geometry.Grid.Extension.CoordinateInclusion base.bank.grid grid.punctured.bank.grid := by
  change Geometry.Grid.Extension.CoordinateInclusion base.bank.grid grid.shrunk.prepared.grid
  rw [grid.grid_eq]
  exact grid.extension.originalIncluded

open Purelib.Curves in
open Purelib.Data in
set_option genInjectivity false in
/-- Paired original-period fragments on one retained Newton grid.

Each fragment retains its original program and requested accuracy; the common stage is the maximum of their cached
comparison stages. -/
structure NewtonFragments (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (grid :
  NewtonGrid preparation bandTarget radius)
    (differential index : Fin genus) (minimum : Nat) (target : Rat.Fraction.Rational) where
  /-- Fragments for the original prepared A-period program on the retained Newton grid. -/ a :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments.IncludedFragments (base := grid.punctured)
    (prepared.aWalk index) differential minimum target
  /-- Fragments for the original prepared B-period program on the retained Newton grid. -/ b :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments.IncludedFragments (base := grid.punctured)
    (prepared.bWalk index) differential minimum target
  /-- The retained common comparison stage. -/ stage : Nat
  /-- The common stage is exactly the maximum of the two fragment stages. -/ stage_eq : stage = max a.comparison.stage
    b.comparison.stage

constructive_injectivity NewtonFragments

namespace NewtonFragments

variable {prepared : Prepared paired} {grid :
  NewtonGrid preparation bandTarget radius}
  {differential index : Fin genus} {minimum : Nat} {target : Rational}

open Purelib.Curves in
/-- Construct paired Newton fragments from existing covered period requests.

Transport both original programs through the retained grid inclusion and cache the maximum of their comparison stages.
-/
def ofRequests (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (grid : NewtonGrid
  preparation bandTarget radius)
    (aRequest : CoveredPeriodRequest (prepared.aWalk index).initial
      (standardDifferentials genus) (standardDifferential differential) genus minimum target)
    (bRequest : CoveredPeriodRequest (prepared.bWalk index).initial
      (standardDifferentials genus) (standardDifferential differential) genus minimum target) :
    NewtonFragments prepared grid differential index minimum target :=
  let a := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments.IncludedFragments.ofRequest (prepared.aWalk
    index) (lifted.vertices.coordinate_onGrid _) (newton_included grid) aRequest
  let b := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments.IncludedFragments.ofRequest (prepared.bWalk
    index) (lifted.vertices.coordinate_onGrid _) (newton_included grid) bRequest
  ⟨a, b, max a.comparison.stage b.comparison.stage, rfl⟩

open Purelib.Curves in
open Purelib.Data in
/-- Acquire both covered period requests and construct their Newton fragments.

The positive target bounds the fragment comparisons for the selected original A and B programs. -/
def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (grid : NewtonGrid
  preparation bandTarget radius)
    (differential index : Fin genus) (minimum : Nat) (target : Rat.Fraction.Rational) (positive : 0 < target) :
    NewtonFragments prepared grid differential index minimum target :=
  ofRequests prepared grid
    (CoveredPeriodRequest.acquire (prepared.aWalk index).initial
      (standardDifferentials genus) (standardDifferential differential) genus minimum target positive)
    (CoveredPeriodRequest.acquire (prepared.bWalk index).initial
      (standardDifferentials genus) (standardDifferential differential) genus minimum target positive)

open Purelib.Data
/-- The retained common stage is at least the requested minimum stage. -/
theorem stage_ge (request : NewtonFragments prepared grid differential index minimum target) :
    minimum ≤ request.stage := by
  rw [request.stage_eq]
  exact request.a.comparison.stage_ge.trans (Nat.Order.le_max_left _ _)

/-- Beyond the common stage, the A-fragment sum approximates its original period reading within the target. -/
theorem a_accurate (request : NewtonFragments prepared grid differential index minimum target)
    (stage : Nat) (later : request.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (request.a.fragments.sum -
      ((prepared.periodData.aProgram differential index).integral.model stage).integralSample) < target :=
  request.a.accurate stage ((Nat.Order.le_max_left _ _).trans (request.stage_eq ▸ later))

/-- Beyond the common stage, the B-fragment sum approximates its original period reading within the target. -/
theorem b_accurate (request : NewtonFragments prepared grid differential index minimum target)
    (stage : Nat) (later : request.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (request.b.fragments.sum -
      ((prepared.periodData.bProgram differential index).integral.model stage).integralSample) < target :=
  request.b.accurate stage ((Nat.Order.le_max_right _ _).trans (request.stage_eq ▸ later))

end NewtonFragments
end Purelib.Riemann.Periods.NewtonPairedPeriodFragments
