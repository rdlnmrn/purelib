module
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Rational.Path.Basic
public import Purelib.Integration.Program.Rational.Antiderivative
import Purelib.Integration.Program.Rational.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Polynomial.Rational.Path.Allowance
import Purelib.Integration.Polynomial.Rational.Antiderivative
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section
namespace Purelib.Integration.Program.Rational.Cached.Basic

open Purelib.Integration in
open Purelib.Integration.Polynomial.Rational.Path in
/-- The exact rational path model's integral sample and aggregate allowance operations. -/
@[reducible] def modelOperations :
  CertifiedProgram.ModelOperations Basic.PathModel :=
  ⟨Basic.PathModel.integralSample, Basic.PathModel.aggregateAllowance⟩
end Purelib.Integration.Program.Rational.Cached.Basic

end

section
@[expose] public section
namespace Purelib.Integration.Program.Rational.Basic
namespace RefinementProgram
namespace AntiderivativeProcess

open Purelib.Integration.Program.Rational in
/-- An original refinement program paired dependently with its retained antiderivative process. -/
@[reducible] def FTCProducer
  :=
  Sigma (fun program : Basic.RefinementProgram => Basic.RefinementProgram.AntiderivativeProcess program)
end AntiderivativeProcess
end RefinementProgram
end Purelib.Integration.Program.Rational.Basic

end

section
@[expose] public section
namespace Purelib.Integration.Program.Rational.Basic
namespace RefinementProgram
namespace AntiderivativeProcess

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.Integration.Program.Rational in
/-- Build a certified view using the original antiderivative difference samples and retained path models.

The producer retains both the original program and its dependent antiderivative certificates; exact difference-sample
equalities transport the original quantitative bounds. -/
def differenceView (program :
  Basic.RefinementProgram)
    (antiderivative : Basic.RefinementProgram.AntiderivativeProcess program) :
    CertifiedProgram.View FTCProducer Cached.Basic.modelOperations
      (fun owner index => owner.1.model index) :=
  let shared : CertifiedProgram.Program Cached.Basic.modelOperations :=
    { stage := fun index =>
        let model := program.model index
        { model := model
          sample := (antiderivative.certificate index).differenceSample
          sample_eq := Antiderivative.RefinementProgram.AntiderivativeProcess.differenceSample_eq program antiderivative
            index
          allowance := model.aggregateAllowance
          allowance_eq := rfl }
      errorScale := program.errorScale
      errorScale_nonneg := program.errorScale_nonneg
      modelAllowance_le := program.modelAllowance_le
      later_close := by
        intro earlier later order
        change Data.Gaussian.Norm.Basic.normSq ((antiderivative.certificate later).differenceSample -
          (antiderivative.certificate earlier).differenceSample) ≤
            Geometric.Basic.quarterRadius program.errorScale earlier
        rw [(Antiderivative.RefinementProgram.AntiderivativeProcess.differenceSample_eq program antiderivative),
          (Antiderivative.RefinementProgram.AntiderivativeProcess.differenceSample_eq program antiderivative)]
        rw [Norm.Basic.normSq_eq_canonical]
        exact program.later_close order
      centerBound := program.centerBound
      centerBound_nonneg := program.centerBound_nonneg
      sample_bounded := by
        intro index
        change Data.Gaussian.Norm.Basic.normSq (antiderivative.certificate index).differenceSample ≤ program.centerBound
        rw [(Antiderivative.RefinementProgram.AntiderivativeProcess.differenceSample_eq program antiderivative)]
        rw [Norm.Basic.normSq_eq_canonical]
        exact program.sample_bounded index }
  { producer := ⟨program, antiderivative⟩
    program := shared
    model_eq := fun _ => rfl }
end AntiderivativeProcess
end RefinementProgram
end Purelib.Integration.Program.Rational.Basic

end

section
@[expose] public section
namespace Purelib.Integration.Program.Rational.Basic
namespace RefinementProgram

open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.Integration.Program.Rational in
/-- Expose the original rational refinement program as a certified program view with cached stage data.

Every stage retains the exact original model, canonical sample and allowance; the returned view keeps the original
producer and model identities. -/
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
end Purelib.Integration.Program.Rational.Basic

end

section
@[expose] public section
namespace Purelib.Integration.Program.Rational.Basic
namespace RefinementProgram

open Purelib.Integration.Program.Rational in
/-- The original certified stage's cached allowance equals the original model allowance. -/
theorem certifiedView_allowance (program :
  Basic.RefinementProgram) (index : Nat) :
    ((certifiedView program).program.stage index).allowance = (program.model
      index).aggregateAllowance := rfl
end RefinementProgram
end Purelib.Integration.Program.Rational.Basic

end

section
@[expose] public section
namespace Purelib.Integration.Program.Rational.Basic
namespace RefinementProgram

open Purelib.Integration.Program.Rational in
/-- The certified stage retains the exact original model at that index. -/
theorem certifiedView_model (program :
  Basic.RefinementProgram) (index : Nat) :
    ((certifiedView program).program.stage index).model = program.model index := rfl
end RefinementProgram
end Purelib.Integration.Program.Rational.Basic

end

section
@[expose] public section
namespace Purelib.Integration.Program.Rational.Basic
namespace RefinementProgram

open Purelib.Integration.Program.Rational in
/-- The certified stage's cached sample equals the exact original model sample. -/
theorem certifiedView_sample (program :
  Basic.RefinementProgram) (index : Nat) :
    ((certifiedView program).program.stage index).sample = (program.model index).integralSample
      := rfl
end RefinementProgram
end Purelib.Integration.Program.Rational.Basic

end
