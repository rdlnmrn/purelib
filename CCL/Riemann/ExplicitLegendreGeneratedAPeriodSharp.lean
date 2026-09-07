import CCL.Riemann.ExplicitLegendreGeneratedAPeriodPropagation

/-!
# Uniform generated Legendre A-period lower bounds

This module transfers the positive initial certificate to every later finite
model and to the public coherent sampler.
-/

namespace CCL.Riemann.ExplicitLegendreGeneratedCertificate

open CCL.Riemann.GeneratedLegendreCertificateData
open CCL.Riemann.PreparedSwitchedRefinements

theorem generatedSharpAPeriodProgram_modelRealLower (token : Unit)
    (index : Nat) :
    generatedSharpUniformRealLower <=
      ((generatedSharpAPeriodProgram token).integral.model
        index).integralSample.re := by
  unfold generatedSharpUniformRealLower
  exact refinementProgram_laterRealLower
    (generatedSharpAPeriodProgram token).integral generatedSharpRealLower
    (1 / 2) (by decide)
    (generatedSharpAPeriodProgram_initialRealLower token)
    (by
      rw [generatedSharpAPeriodProgram_errorScale]
      exact generatedSharpSourceErrorScale_le_quarter)
    index

/-- The public coherent sampler selects some later model of the same sharp
program, so the uniform finite-model bound transfers without evaluating the
selected refinement index. -/
theorem generatedSharpAPeriodProgram_sampleRealLower (token : Unit)
    (sampleIndex : Nat) :
    generatedSharpUniformRealLower <=
      ((CCL.ProgressiveSampling.approximation
        (generatedSharpAPeriodProgram token).output.name).sample
          sampleIndex).re := by
  let program := generatedSharpAPeriodProgram token
  change generatedSharpUniformRealLower <=
    (program.integral.model
      (CCL.ProgressiveSampling.stateAt program.integral.approximation.toProcess
        (show program.integral.approximation.toProcess.State from (0 : Nat))
        sampleIndex)).integralSample.re
  exact generatedSharpAPeriodProgram_modelRealLower token _

end CCL.Riemann.ExplicitLegendreGeneratedCertificate
