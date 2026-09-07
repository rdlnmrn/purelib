import CCL.Riemann.ExplicitLegendreGeneratedBPeriodPropagation

/-!
# Uniform generated Legendre B-period lower bounds

This module transfers the positive initial certificate to every later finite
model and to the public coherent sampler.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedBCertificate

open CCL.Riemann.GeneratedLegendreBCertificateData
open CCL.Riemann.PreparedSwitchedRefinements

theorem generatedSharpBPeriodProgram_modelRealLower (token : Unit)
    (index : Nat) :
    generatedSharpUniformRealLower <=
      ((generatedSharpBPeriodProgram token).integral.model
        index).integralSample.re := by
  unfold generatedSharpUniformRealLower
  exact refinementProgram_laterRealLower
    (generatedSharpBPeriodProgram token).integral generatedSharpRealLower
    (1 / 2) (by decide)
    (generatedSharpBPeriodProgram_initialRealLower token)
    (by
      rw [generatedSharpBPeriodProgram_errorScale]
      exact generatedSharpSourceErrorScale_le_quarter)
    index

/-- The public coherent sampler selects some later model of the same sharp
program, so the uniform finite-model bound transfers without evaluating the
selected refinement index. -/
theorem generatedSharpBPeriodProgram_sampleRealLower (token : Unit)
    (sampleIndex : Nat) :
    generatedSharpUniformRealLower <=
      ((CCL.ProgressiveSampling.approximation
        (generatedSharpBPeriodProgram token).output.name).sample
          sampleIndex).re := by
  let program := generatedSharpBPeriodProgram token
  change generatedSharpUniformRealLower <=
    (program.integral.model
      (CCL.ProgressiveSampling.stateAt program.integral.approximation.toProcess
        (show program.integral.approximation.toProcess.State from (0 : Nat))
        sampleIndex)).integralSample.re
  exact generatedSharpBPeriodProgram_modelRealLower token _

end CCL.Riemann.ExplicitLegendreGeneratedBCertificate
