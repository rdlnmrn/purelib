module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Integration.Path.Lifted.Model
public import Purelib.Integration.Path.Lifted.Program
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Program.Comparison.Add
public import Purelib.Integration.Program.Gaussian.Concatenation
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Geometry.Path.Gaussian.Lifted.Refinement (LiftedCycleRefinement)

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

namespace Purelib.Integration.Path.Lifted.Concatenation

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Path.Lifted in
open Purelib.Integration.Program in
/-- A retained join of two original lifted-cycle programs with its exact concatenated-model allowance.

The cycle join keeps both input cycles and their common-basepoint evidence, while the allowance belongs to the original
integration programs. -/
structure ConcatenationData {sheets : Nat}
    {firstCycle secondCycle : LiftedCycleRefinement sheets}
    (first : Program.PeriodProgram firstCycle) (second : Program.PeriodProgram secondCycle)
    where
  /-- The retained cycle join linking the two exact original cycle refinements. -/ join : Lifted.Refinement.CycleJoin
    firstCycle secondCycle
  /-- The original programs' stagewise concatenated models satisfy the combined allowance bound. -/ allowance :
    Gaussian.Basic.RefinementProgram.ConcatenationAllowance
    first.integral second.integral

namespace ConcatenationData

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Path.Lifted in
open Purelib.Integration.Program in
/-- Construct the period program following the retained join of the two original cycles.

The original stage models are concatenated with the supplied allowance, and their following certificates transport
through the exact retained cycle join. -/
def program {sheets : Nat}
    {firstCycle secondCycle : LiftedCycleRefinement sheets}
    {first : Program.PeriodProgram firstCycle} {second : Program.PeriodProgram secondCycle}
    (data : Concatenation.ConcatenationData first second) : Program.PeriodProgram data.join.cycle := by
  refine
    { integral :=
        Gaussian.Basic.RefinementProgram.concat
          first.integral second.integral
        data.allowance
      follows := ?_ }
  intro index
  exact Lifted.Refinement.CycleJoin.appendFollowed
    (firstCycle.liftedPath index) (secondCycle.liftedPath index)
    (data.join.basepoint_eq index) (first.follows index) (second.follows index)

end ConcatenationData

open Purelib.Approximation.Gaussian in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Path.Lifted in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Integration.Program in
/-- The retained joined period output is coherently equivalent to the sum of the two original outputs. -/
def ConcatenationData.output_equivalent_add {sheets : Nat}
    {firstCycle secondCycle : LiftedCycleRefinement sheets}
    {first : Program.PeriodProgram firstCycle} {second : Program.PeriodProgram secondCycle}
    (data : ConcatenationData first second) :
    Equivalence.NamedEquivalent data.program.output.name
      (Name.Coherent.CoherentNamed.add
        first.output second.output).name := by
  exact Equivalence.NamedEquivalent.symm (by
    simpa only [ConcatenationData.program, Program.PeriodProgram.output,
      Gaussian.Basic.RefinementProgram.concat] using
      Comparison.Add.addProgram_output_equivalent first.integral second.integral
        { model := fun index =>
            (first.integral.model index).concat
              (second.integral.model index)
          integral_eq := fun index =>
            Basic.PathModel.integralSample_concat
              _ _
          aggregate_le := data.allowance.aggregate_le })
end Purelib.Integration.Path.Lifted.Concatenation

end
