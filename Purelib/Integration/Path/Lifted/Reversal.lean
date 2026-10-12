module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
public import Purelib.Integration.Path.Cancellation
import Purelib.Integration.Path.Lifted.Model
import Purelib.Integration.Path.Lifted.Program
import Purelib.Integration.Polynomial.Gaussian.Path.Reversal
import Purelib.Integration.Program.Gaussian.Reversal
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Program.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Approximation.Gaussian.Sequence.Equivalence
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Geometry.Path.Gaussian.Lifted.Refinement (LiftedCycleRefinement)

section
@[expose] public section

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
namespace PeriodProgram

open Purelib.Approximation.Rational in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Path.Lifted in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Integration.Program in
/-- Construct a period program following the exact reversal of the retained original lifted cycle.

The supplied stagewise reversal models preserve their original allowance bounds and provide the reversed cell-following
certificates. -/
def reverse {sheets : Nat} {cycle :
  LiftedCycleRefinement sheets}
    (program : Program.PeriodProgram cycle)
    (reversals : forall index,
      Basic.PathModel.Reversal
        (program.integral.model index))
    (aggregate_le : forall index,
      ((program.integral.model index).reverse (reversals index)).aggregateAllowance <=
        Geometric.Basic.quarterRadius program.integral.errorScale index) :
    Program.PeriodProgram cycle.reverse := by
  let models := Gaussian.Reversal.RefinementProgram.ReversalModels.ofPathReversals
    program.integral reversals aggregate_le
  exact
    { integral := program.integral.reverse models
      follows := by
        intro index
        exact Lifted.Basic.LiftedPath.followedBy_reverse (program.follows index)
          (reversals index).cells }
end PeriodProgram
end Purelib.Integration.Path.Lifted.Program

end

section
@[expose] public section

/-!
# Operational linearity of finite period programs

This module records orientation reversal and path concatenation at the actual
finite `PeriodProgram` layer.  It also exposes the already constructive
cellular-boundary and exact-primitive cancellation theorems through one small
interface used by family transport.

The stronger `CertifiedPeriodProgram` contains local algebraic observations.
Reversing those observations requires a new parameter-reversal certificate;
it is intentionally not inferred merely from reversal of the geometric path.
-/

namespace Purelib.Integration.Path.Lifted.Reversal

/-! ## Orientation reversal -/

open Purelib.Approximation.Rational in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Path.Lifted in
open Purelib.Integration.Polynomial.Gaussian.Path in
set_option genInjectivity false in
/-- Retained stagewise reversal models and allowance bounds for an original lifted-cycle period program.

Each reversal is indexed by the exact original stage model and keeps its original geometric error scale. -/
structure ReversalData {sheets : Nat} {cycle :
  LiftedCycleRefinement sheets}
    (program : Program.PeriodProgram cycle) where
  /-- A retained reversal of each exact original stage path model. -/ reversal : forall index,
    Basic.PathModel.Reversal
      (program.integral.model index)
  /-- Every retained reversed stage model satisfies the original program's geometric allowance. -/ aggregate_le : forall
    index,
    ((program.integral.model index).reverse (reversal index)).aggregateAllowance <=
      Geometric.Basic.quarterRadius program.integral.errorScale index

constructive_injectivity ReversalData

namespace ReversalData

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Path.Lifted in
open Purelib.Integration.Program in
/-- Read the exact program reversal models from the retained path reversals and allowance certificates. -/
def models {sheets : Nat} {cycle :
  LiftedCycleRefinement sheets}
    {program : Program.PeriodProgram cycle} (data : Reversal.ReversalData program) :
    Gaussian.Basic.RefinementProgram.ReversalModels
      program.integral :=
  Gaussian.Reversal.RefinementProgram.ReversalModels.ofPathReversals
    program.integral
    data.reversal data.aggregate_le

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Path.Lifted in
/-- Build the reversed period program from the retained original reversal data. -/
def program {sheets : Nat} {cycle :
  LiftedCycleRefinement sheets}
    {source : Program.PeriodProgram cycle} (data : Reversal.ReversalData source) :
    Program.PeriodProgram cycle.reverse :=
  source.reverse data.reversal data.aggregate_le

open Purelib.Approximation.Gaussian in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Lifted in
/-- The retained reversed period output is coherently equivalent to the negated original output. -/
def output_equivalent_neg {sheets : Nat}
    {cycle : LiftedCycleRefinement sheets} {source : Program.PeriodProgram cycle}
    (data : Reversal.ReversalData source) :
    Equivalence.NamedEquivalent data.program.output.name
      (Name.Coherent.CoherentNamed.neg source.output).name := by
  let pair := Cancellation.BoundaryPair.ofProgramReversal
    source.integral data.models
  simpa only [Reversal.ReversalData.program, Program.PeriodProgram.reverse, Reversal.ReversalData.models, pair,
    Program.PeriodProgram.output,
    Cancellation.BoundaryPair.ofProgramReversal] using
    pair.reverse_eq_neg

end ReversalData
end Purelib.Integration.Path.Lifted.Reversal

end
