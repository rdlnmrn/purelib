module
public import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance

section
@[expose] public section
namespace Purelib.Integration.Program.Gaussian.Cached.Basic

open Purelib.Integration in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The exact integral-sample and aggregate-allowance operations on original Gaussian path models. -/
@[reducible] def modelOperations :
  CertifiedProgram.ModelOperations Basic.PathModel :=
  ⟨Basic.PathModel.integralSample, Basic.PathModel.aggregateAllowance⟩
end Purelib.Integration.Program.Gaussian.Cached.Basic

end

section
@[expose] public section
namespace Purelib.Integration.Program.Gaussian.Basic
namespace RefinementProgram

open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.Integration.Program.Gaussian in
/-- Present the original refinement program through the generic certified cache interface.

Each stage retains the original model and caches its exact sample and allowance; the program's original error and center
certificates are transported unchanged. -/
def certifiedView (program :
  Basic.RefinementProgram) :
    CertifiedProgram.View Basic.RefinementProgram Cached.Basic.modelOperations
      (fun owner index => owner.model index) :=
  let shared : CertifiedProgram.Program Cached.Basic.modelOperations :=
    { stage := fun index => CertifiedProgram.CachedModel.canonical
        (operations := Cached.Basic.modelOperations) (program.model index)
      errorScale := program.errorScale
      errorScale_nonneg := program.errorScale_nonneg
      modelAllowance_le := program.modelAllowance_le
      later_close := fun {earlier later} order => by
        change Data.Gaussian.Norm.Basic.normSq
          ((program.model later).integralSample - (program.model earlier).integralSample) ≤ _
        rw [Norm.Basic.normSq_eq_canonical]
        exact program.later_close order
      centerBound := program.centerBound
      centerBound_nonneg := program.centerBound_nonneg
      sample_bounded := fun index => by
        change Data.Gaussian.Norm.Basic.normSq (program.model index).integralSample ≤ _
        rw [Norm.Basic.normSq_eq_canonical]
        exact program.sample_bounded index }
  { producer := program
    program := shared
    model_eq := fun _ => rfl }
end RefinementProgram
end Purelib.Integration.Program.Gaussian.Basic

end

section
@[expose] public section
namespace Purelib.Integration.Program.Gaussian.Basic
namespace RefinementProgram

open Purelib.Integration.Program.Gaussian in
/-- The certified view's stage allowance is the original model's aggregate allowance. -/
theorem certifiedView_allowance (program :
  Basic.RefinementProgram) (index : Nat) :
    ((certifiedView program).program.stage index).allowance = (program.model
      index).aggregateAllowance := rfl
end RefinementProgram
end Purelib.Integration.Program.Gaussian.Basic

end

section
@[expose] public section
namespace Purelib.Integration.Program.Gaussian.Basic
namespace RefinementProgram

open Purelib.Integration.Program.Gaussian in
/-- The certified view retains the exact original stage model. -/
theorem certifiedView_model (program :
  Basic.RefinementProgram) (index : Nat) :
    ((certifiedView program).program.stage index).model = program.model index := rfl
end RefinementProgram
end Purelib.Integration.Program.Gaussian.Basic

end

section
@[expose] public section
namespace Purelib.Integration.Program.Gaussian.Basic
namespace RefinementProgram

open Purelib.Integration.Program.Gaussian in
/-- The certified view's stage sample is the original model's integral sample. -/
theorem certifiedView_sample (program :
  Basic.RefinementProgram) (index : Nat) :
    ((certifiedView program).program.stage index).sample = (program.model index).integralSample
      := rfl
end RefinementProgram
end Purelib.Integration.Program.Gaussian.Basic

end

section
@[expose] public section
namespace Purelib.Integration.Program.Gaussian.Cached.Basic

open Purelib.Integration in
open Purelib.Integration.Program.Gaussian in
/-- The generic retained model-cache carrier specialized to the exact Gaussian path operations. -/
@[reducible] def CachedModel := CertifiedProgram.CachedModel
  modelOperations
end Purelib.Integration.Program.Gaussian.Cached.Basic

end

section
@[expose] public section
namespace Purelib.Integration.Program.Gaussian.Cached.Basic

open Purelib.Integration in
open Purelib.Integration.Program.Gaussian in
/-- The generic certified program carrier specialized to the exact Gaussian path operations. -/
@[reducible] def CachedProgram := CertifiedProgram.Program
  modelOperations

end Purelib.Integration.Program.Gaussian.Cached.Basic

end
