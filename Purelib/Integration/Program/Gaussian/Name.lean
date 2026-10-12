module
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.SampleCarrier
import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.CertifiedProgram
public import Purelib.Integration.CCL.Program
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

section
@[expose] public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Program.Gaussian.Basic
namespace RefinementProgram

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Program.Gaussian in
/-- Read the coherent Gaussian name from the exact retained program's certified view. -/
def output (program : Basic.RefinementProgram) :
  CoherentNamed :=
  (program.certifiedView).program.output

open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration.Program.Gaussian in
/-- Represent a coherent Gaussian name by a refinement program of exact single-cell sample carriers.

Each stage retains the original name approximation's sample, geometric comparison and common center bound; the exact
carriers have zero model allowance. -/
def ofCoherentNamed (value :
  CoherentNamed) : Basic.RefinementProgram := by
  let source := Name.Sampling.approximation value.name
  exact
    { model := fun index => Basic.RefinementProgram.exactSamplePath (source.sample index)
      errorScale := 4
      errorScale_nonneg := by decide
      modelAllowance_le := by
        intro index
        rw [Basic.RefinementProgram.exactSamplePath_aggregateAllowance]
        exact Geometric.Basic.quarterRadius_nonneg (by decide) index
      later_close := by
        intro earlier later order
        rw [Basic.RefinementProgram.exactSamplePath_integralSample,
          Basic.RefinementProgram.exactSamplePath_integralSample]
        have scalar := source.later_close order
        change Data.Gaussian.Norm.Basic.normSq
          (source.sample later - source.sample earlier) ≤
          Geometric.Basic.quarterRadius 4 earlier at scalar
        simpa only [Norm.Basic.normSq_eq_canonical] using scalar
      centerBound := source.centerBound
      centerBound_nonneg := source.centerBound_nonneg
      sample_bounded := by
        intro index
        rw [Basic.RefinementProgram.exactSamplePath_integralSample]
        simpa only [Norm.Basic.normSq_eq_canonical] using source.sample_bounded index }

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Program.Gaussian in
/-- Each stage of the named carrier reads the original coherent name approximation's exact sample. -/
@[simp] theorem ofCoherentNamed_integralSample
  (value : CoherentNamed)
    (index : Nat) :
    ((ofCoherentNamed value).model index).integralSample =
      (Name.Sampling.approximation value.name).sample index :=
  Basic.RefinementProgram.exactSamplePath_integralSample _
end RefinementProgram

end Purelib.Integration.Program.Gaussian.Basic

end
