import CCL.Transcendental.LogBranchGeometry

/-!
# Exact finite seeds for anchored logarithm transport

The retryable logarithm layer needs at least one completely explicit source
anchor.  The exact rational input `1` uses the existing unit complex-log chart,
the exact-zero correction, and the proved operational identity `exp 0 = 1`.
This is local finite branch data, not a global logarithm convention.
-/

namespace CCL.LogAnchorSeeds

abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev AnchoredChart := CCL.LogBranchCalculus.AnchoredChart

/-- The exact coherent input at the rational unit. -/
def exactOneInput : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.exact 1

/-- A completely explicit anchored chart at `1`.  Its branch correction is
exact zero, whose finite automatic exponential is operationally exact one. -/
def exactOneAnchor : AnchoredChart exactOneInput where
  chart := CCL.ComplexLogChart.unitChart
  certificate :=
    { factor_ne_zero := by
        change (1 : RFAP.ConstructiveGaussian.Gaussian) ≠ 0
        decide
      correction_exponential := by
        change CCL.OperationalEquivalence.NamedEquivalent
          (CCL.ProgressiveExpRange.named
            (CCL.ProgressiveTransducer.Named.exact 0))
          (CCL.ProgressiveTransducer.Named.exact 1)
        exact CCL.TranscendentalCoherence.automaticExp_zero }
  correctionCoherent := by
    change CCL.ProgressiveCoherence.Coherent
      (CCL.ProgressiveTransducer.Named.exact 0).process
    exact CCL.ProgressiveCoherence.Coherent.exact 0

/-- The exact seed is immediately an ordinary productive logarithm output. -/
theorem exactOneAnchor_productive (count : Nat) :
    exactOneAnchor.output.name.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          exactOneAnchor.output.name.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        exactOneAnchor.output.name.machine count).emitted.length = count :=
  exactOneAnchor.output.name.productive count

end CCL.LogAnchorSeeds
