module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests
import Init.Prelude
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Periods.PeriodMatrix
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Data.Rat

open Purelib.Data.Vector

public section

open Purelib.Data

/-! Retained finite thresholds for the witness-to-model offsets of all four
period entries in each corrected determinant row. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodOffsets

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)
open Purelib.Data.Rat.Fraction.Compatibility

section SynchronizedPeriodOffsets

set_option genInjectivity false in
/-- A retained finite geometric search paying an original nonnegative period offset scale. -/
structure QuarterRequest (scale target : Fraction.Rational) where
  /-- The original geometric offset scale is nonnegative. -/ nonnegative : 0 ≤ scale
  /-- The cached finite geometric search stage for this original scale and target. -/ index : Nat
  /-- The cached stage is exactly the original first geometric search below the target from floor zero. -/ index_eq :
    index = Search.firstQuarterBelow scale 0 target
  /-- The retained selected geometric radius is strictly below its original target. -/ accurate :
    Geometric.Basic.quarterRadius scale index < target

constructive_injectivity QuarterRequest

namespace QuarterRequest

/-- Run the finite geometric search on the original scale and retain its exact selected stage and strict accuracy
certificate. -/
@[expose] def build (scale target : Fraction.Rational) (nonnegative : 0 ≤ scale) (positive : 0 < target) :
  QuarterRequest scale
  target :=
  ⟨nonnegative, Search.firstQuarterBelow scale 0 target, rfl,
    Search.firstQuarterBelow_accurate scale nonnegative 0 target positive⟩

/-- Every stage beyond the retained geometric search index satisfies its original offset target. -/
theorem later {scale target : Fraction.Rational} (request :
  QuarterRequest scale
  target)
    {stage : Nat} (after : request.index ≤ stage) : Geometric.Basic.quarterRadius scale stage ≤ target :=
  ((quarterRadius_antitone request.nonnegative after).trans_lt request.accurate).le

end QuarterRequest

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
    sheet} {paired : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}
  {prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired} {first second
    cycle : Fin genus} {target : Purelib.Data.Rat.Fraction.Rational} {minimum : Nat}

set_option genInjectivity false in
/-- The four retained witness-to-model offset searches for one original corrected A/B determinant row. -/
structure Entry (prepared : PeriodPrograms.Prepared paired) (first second cycle : Fin genus) (target :
  Fraction.Rational) where
  /-- The retained offset request for the first differential's original A-period entry. -/ firstA :
    QuarterRequest (max
    (prepared.periodData.aProgram first cycle).integral.errorScale 1) target
  /-- The retained offset request for the second differential's original A-period entry. -/ secondA :
    QuarterRequest (max
    (prepared.periodData.aProgram second cycle).integral.errorScale 1) target
  /-- The retained offset request for the first differential's original B-period entry. -/ firstB :
    QuarterRequest (max
    (prepared.periodData.bProgram first cycle).integral.errorScale 1) target
  /-- The retained offset request for the second differential's original B-period entry. -/ secondB :
    QuarterRequest (max
    (prepared.periodData.bProgram second cycle).integral.errorScale 1) target

constructive_injectivity Entry

namespace Entry

/-- Prepare the four original A/B entry offset searches for this retained handle row. -/
@[expose] def build (prepared : PeriodPrograms.Prepared paired) (first second cycle : Fin genus) (target :
  Fraction.Rational) (positive : 0 < target) :
    Entry prepared first
      second cycle target :=
  ⟨QuarterRequest.build _ target ((by decide : (0 : Fraction.Rational) ≤ 1).trans (Fraction.Order.Basic.le_max_right _
    _)) positive,
    QuarterRequest.build _
      target ((by decide : (0 : Fraction.Rational) ≤ 1).trans (Fraction.Order.Basic.le_max_right _ _)) positive,
    QuarterRequest.build _
      target ((by decide : (0 : Fraction.Rational) ≤ 1).trans (Fraction.Order.Basic.le_max_right _ _)) positive,
    QuarterRequest.build _
      target ((by decide : (0 : Fraction.Rational) ≤ 1).trans (Fraction.Order.Basic.le_max_right _ _)) positive⟩

/-- The exact maximum of this original row's four retained offset stages. -/
@[expose] def index (entry :
  Entry prepared first
  second cycle target) : Nat :=
  max (max entry.firstA.index entry.secondA.index) (max entry.firstB.index entry.secondB.index)

end Entry

/-- The dependent complete offset request bank for every original finite handle row. -/
@[expose] def Entries (prepared : PeriodPrograms.Prepared paired) (first second : Fin genus) (target :
  Fraction.Rational) :=
  Data.Vector.DependentVector (fun cycle : Fin genus =>
    Entry prepared first
    second cycle target)

set_option genInjectivity false in
/-- The retained synchronized offset schedule for all original determinant entries.

Its cached stage pays every row and the supplied external minimum. -/
structure Request (prepared : PeriodPrograms.Prepared paired) (first second : Fin genus) (target : Fraction.Rational)
  (minimum : Nat) where
  /-- The actual four-offset request bank on every original handle row. -/ entries :
    Entries prepared first
    second target
  /-- The cached common stage paying the original minimum and every retained row offset. -/ index : Nat
  /-- The synchronized stage is exactly the original minimum combined with the complete retained row maximum. -/
    index_eq : index = max minimum (entries.maximum fun _ entry => entry.index)

constructive_injectivity Request

namespace Request

/-- Prepare every original handle row's four offset searches and cache their common stage with the supplied minimum. -/
@[expose] def build (prepared : PeriodPrograms.Prepared paired) (first second : Fin genus) (target : Fraction.Rational)
    (positive : 0 < target) (minimum : Nat) :
      Request prepared
      first second target minimum :=
  let entries := DependentVector.ofFn fun cycle =>
    Entry.build prepared
    first second cycle target positive
  ⟨entries, max minimum (entries.maximum fun _ entry => entry.index), rfl⟩

/-- The retained synchronized stage pays the original supplied minimum. -/
theorem minimum_le (request :
  Request prepared first
  second target minimum) : minimum ≤ request.index :=
  (Nat.Order.le_max_left _ _).trans_eq request.index_eq.symm

/-- Every actual retained row's offset stage is bounded by the complete synchronized stage. -/
theorem entry_le (request :
  Request prepared first
  second target minimum) (cycle : Fin genus) :
    (request.entries.get cycle).index ≤ request.index :=
  ((request.entries.get_le_maximum (fun _ entry => entry.index) cycle).trans
    (Nat.Order.le_max_right _ _)).trans_eq request.index_eq.symm

/-- The original first-differential A-entry offset is paid at every stage beyond the retained schedule. -/
theorem firstA (request :
  Request prepared first
  second target minimum) {stage : Nat}
    (later : request.index ≤ stage) (cycle : Fin genus) :
    Geometric.Basic.quarterRadius (max (prepared.periodData.aProgram first cycle).integral.errorScale 1) stage ≤ target
      :=
  (request.entries.get cycle).firstA.later
    (((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_left _ _)).trans ((request.entry_le cycle).trans later))

/-- The original second-differential A-entry offset is paid at every stage beyond the retained schedule. -/
theorem secondA (request :
  Request prepared first
  second target minimum) {stage : Nat}
    (later : request.index ≤ stage) (cycle : Fin genus) :
    Geometric.Basic.quarterRadius (max (prepared.periodData.aProgram second cycle).integral.errorScale 1) stage ≤ target
      :=
  (request.entries.get cycle).secondA.later
    (((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_left _ _)).trans ((request.entry_le cycle).trans later))

/-- The original first-differential B-entry offset is paid at every stage beyond the retained schedule. -/
theorem firstB (request :
  Request prepared first
  second target minimum) {stage : Nat}
    (later : request.index ≤ stage) (cycle : Fin genus) :
    Geometric.Basic.quarterRadius (max (prepared.periodData.bProgram first cycle).integral.errorScale 1) stage ≤ target
      :=
  (request.entries.get cycle).firstB.later
    (((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)).trans ((request.entry_le cycle).trans later))

/-- The original second-differential B-entry offset is paid at every stage beyond the retained schedule. -/
theorem secondB (request :
  Request prepared first
  second target minimum) {stage : Nat}
    (later : request.index ≤ stage) (cycle : Fin genus) :
    Geometric.Basic.quarterRadius (max (prepared.periodData.bProgram second cycle).integral.errorScale 1) stage ≤ target
      :=
  (request.entries.get cycle).secondB.later
    (((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _)).trans ((request.entry_le cycle).trans later))

end Request
end SynchronizedPeriodOffsets
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodOffsets
