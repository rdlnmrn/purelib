module

import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
public import Purelib.Integration.Path.Lifted.Model
public import Purelib.Integration.Program.Gaussian.Name
public import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Geometry.Path.Gaussian.Lifted.Refinement (LiftedCycleRefinement)

section
public section

/-!
# Finite sheet-aware paths for period integration

A lifted path below is an inductive finite chain.  Every geometric edge
carries an explicit permutation of the labelled sheets and a proof that the
chosen endpoint sheet is the transported start sheet.  A separate inductive
relation verifies that a progressive integration model follows exactly the
same displayed geometric edges.  This separation lets several algebraic
differentials share one persistent lifted cycle while retaining their own
local polynomial integrand models.
-/

namespace Purelib.Integration.Path.Lifted.Program

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Program in
set_option genInjectivity false in
/-- An integration program whose original model sequence follows the retained lifted-cycle refinement.

The stagewise following certificates keep the exact cycle path and model cells at the same original refinement index. -/
structure PeriodProgram {sheets : Nat}
    (cycle : LiftedCycleRefinement sheets) where
  /-- The retained Gaussian integration refinement program. -/ integral : Gaussian.Basic.RefinementProgram
  /-- Each original stage model follows the exact lifted path of the retained cycle at that stage. -/ follows : forall
    index,
    Lifted.Basic.LiftedPath.FollowedBy (integral.model index).cells
      (cycle.liftedPath index).path

constructive_injectivity PeriodProgram

namespace PeriodProgram

open Purelib.Approximation.Gaussian in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration in
/-- Read the coherent Gaussian name from the retained lifted-cycle integration program. -/
@[expose] def output {sheets : Nat} {cycle :
  LiftedCycleRefinement sheets}
    (program : Path.Lifted.Program.PeriodProgram cycle) : Name.Coherent.CoherentNamed :=
  program.integral.output

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration in
/-- At every original stage, the retained integral model and lifted cycle have the same cell count. -/
theorem refinement_cellCount {sheets : Nat}
    {cycle : LiftedCycleRefinement sheets} (program : Path.Lifted.Program.PeriodProgram cycle)
    (index : Nat) :
    (program.integral.model index).cells.length =
      (cycle.liftedPath index).cellCount :=
  Lifted.Basic.LiftedPath.followedBy_length (program.follows index)

open Purelib.Data.Rat in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration in
/-- The retained refinement procedure selects a stage whose original aggregate allowance is below the requested positive
target. -/
theorem subdivision_accurate {sheets : Nat}
    {cycle : LiftedCycleRefinement sheets} (program : Path.Lifted.Program.PeriodProgram cycle)
    (current : Nat) (target : Fraction.Rational)
    (positive : 0 < target) :
    let index := program.integral.approximation.refineIndex current target positive
    (program.integral.model index).aggregateAllowance < target :=
  program.integral.subdivision_accurate current target positive
end PeriodProgram
end Purelib.Integration.Path.Lifted.Program

end
