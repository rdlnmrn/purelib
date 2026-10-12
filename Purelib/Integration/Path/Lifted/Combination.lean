module
public import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Arithmetic.Add
public import Purelib.Approximation.Gaussian.Coherent.Additive
public import Purelib.Approximation.Gaussian.Coherent.Additive.Multiple
public import Purelib.Approximation.Gaussian.Coherent.Additive.Sum
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
public import Purelib.Integration.Path.Lifted.Program
import Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
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

namespace Purelib.Integration.Path.Lifted.Combination

set_option genInjectivity false in
open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Path.Lifted in
/-- An integer coefficient paired with an original lifted cycle and its retained period program.

The dependent program field follows that exact cycle, preserving the geometry and refinement sequence used for the
term's coherent output. -/
structure IntegralPeriodTerm (sheets : Nat) where
  /-- The original lifted-cycle refinement retained by this term. -/ cycle : LiftedCycleRefinement
    sheets
  /-- The period program indexed by that exact retained cycle. -/ program : Program.PeriodProgram cycle
  /-- The original integer multiplier for the retained period output. -/ coefficient : Int

constructive_injectivity IntegralPeriodTerm

namespace IntegralPeriodTerm

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Path.Lifted in
/-- Multiply the original term's retained coherent period output by its integer coefficient. -/
def value {sheets : Nat} (term :
  Combination.IntegralPeriodTerm sheets) : CoherentNamed :=
  Coherent.Additive.Multiple.intMultiple term.coefficient term.program.output

open Purelib.Approximation.Gaussian
open Purelib.Geometry.Path.Gaussian
open Purelib.Integration.Path.Lifted
/-- The coefficient-one term output is coherently equivalent to the original period output. -/
def value_one {sheets : Nat} (cycle :
  LiftedCycleRefinement sheets)
    (program : Program.PeriodProgram cycle) :
    Equivalence.NamedEquivalent
      (Combination.IntegralPeriodTerm.value
        { cycle := cycle, program := program, coefficient := 1 }).name
      program.output.name :=
  Arithmetic.Add.coherentAdd_zero_right program.output

/-- The coefficient-minus-one term output is coherently equivalent to the negated original period output. -/
def value_negative_one {sheets : Nat}
    (cycle : LiftedCycleRefinement sheets) (program : Program.PeriodProgram cycle) :
    Equivalence.NamedEquivalent
      (Combination.IntegralPeriodTerm.value
        { cycle := cycle, program := program, coefficient := -1 }).name
      (CoherentNamed.neg program.output).name :=
  Coherent.Additive.coherentNeg_respects
    (Coherent.Additive.Multiple.natMultiple 1 program.output) program.output
    (Arithmetic.Add.coherentAdd_zero_right program.output)

end IntegralPeriodTerm

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Path.Lifted in
/-- Sum the coherent outputs of the original ordered list of integer-weighted period terms. -/
def integralCombination {sheets : Nat}
    (terms : List (IntegralPeriodTerm sheets)) : CoherentNamed :=
  Coherent.Additive.Sum.sumList (terms.map IntegralPeriodTerm.value)

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Path.Lifted in
open Purelib.Data.List in
/-- The concatenated original term list is coherently equivalent to adding the two original combination outputs. -/
def integralCombination_append {sheets : Nat}
    (first second : List (IntegralPeriodTerm sheets)) :
    Equivalence.NamedEquivalent (integralCombination (first ++ second)).name
      (CoherentNamed.add
        (integralCombination first) (integralCombination second)).name := by
  simpa only [integralCombination, Map.map_append, -eq_self, -iff_self] using
    Coherent.Additive.Sum.sumList_append (first.map IntegralPeriodTerm.value)
      (second.map IntegralPeriodTerm.value)
end Purelib.Integration.Path.Lifted.Combination

end
