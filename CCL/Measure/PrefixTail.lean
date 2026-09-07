import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixDeviation

/-!
# Finite tail bounds from CCL prefix moments

A CCL-derived enclosure of a natural-powered probe moment gives an explicit
Markov bound for the finite probability that the probe magnitude crosses a
positive rational threshold.  Progressive requests additionally make the
displayed moment upper endpoint arbitrarily close to every explicitly
supplied realization family's exact powered moment.
-/

namespace CCL.FiniteMeasure

private theorem tailProbability_le_upper_div_of_poweredLpDistance_mem
    {α : Type} (distribution : _root_.FiniteMeasure.Distribution α)
    (bound : _root_.FiniteMeasure.Bound)
    (exponent : Nat) (threshold : Coordinate)
    (thresholdPositive : 0 < threshold) (left right : α → Coordinate)
    (inside : bound.Contains
      (distribution.poweredLpDistance exponent left right)) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold left right) ≤
      bound.upper / threshold ^ exponent := by
  have markov :=
    distribution.probability_separationAtLeast_le_poweredLpDistance
      exponent threshold thresholdPositive left right
  have denominatorPositive : 0 < threshold ^ exponent :=
    RFAP.ConstructiveFraction.pow_pos_direct thresholdPositive exponent
  have divided : distribution.poweredLpDistance exponent left right /
        threshold ^ exponent ≤
      bound.upper / threshold ^ exponent := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
    calc
      distribution.poweredLpDistance exponent left right ≤ bound.upper :=
        inside.2
      _ = (bound.upper / threshold ^ exponent) * threshold ^ exponent :=
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne bound.upper
          (threshold ^ exponent) denominatorPositive.ne').symm
  exact markov.trans divided

private theorem tailProbability_le_upper_div_of_poweredLp_mem
    {α : Type} (distribution : _root_.FiniteMeasure.Distribution α)
    (bound : _root_.FiniteMeasure.Bound)
    (exponent : Nat) (threshold : Coordinate)
    (thresholdPositive : 0 < threshold) (value : α → Coordinate)
    (inside : bound.Contains (distribution.poweredLp exponent value)) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold value
          (fun _ => 0)) ≤
      bound.upper / threshold ^ exponent := by
  have markov :=
    distribution.probability_separationAtLeast_le_poweredLpDistance
      exponent threshold thresholdPositive value (fun _ => 0)
  have poweredDistance :
      distribution.poweredLpDistance exponent value (fun _ => 0) =
        distribution.poweredLp exponent value := rfl
  rw [poweredDistance] at markov
  have denominatorPositive : 0 < threshold ^ exponent :=
    RFAP.ConstructiveFraction.pow_pos_direct thresholdPositive exponent
  have divided : distribution.poweredLp exponent value /
        threshold ^ exponent ≤
      bound.upper / threshold ^ exponent := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos denominatorPositive).2
    calc
      distribution.poweredLp exponent value ≤ bound.upper := inside.2
      _ = (bound.upper / threshold ^ exponent) * threshold ^ exponent :=
        (RFAP.ConstructiveFraction.div_mul_cancel_of_ne bound.upper
          (threshold ^ exponent) denominatorPositive.ne').symm
  exact markov.trans divided

/-- A static family of finite CCL prefixes gives a certified powered-Markov
upper bound for every explicitly supplied realization family. -/
theorem prefixFamilyProbe_tailProbability_le_upper_div
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredProbe probe exponent left)
          (poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun certificate => probe (points certificate))
          (fun _ => 0)) ≤
      (prefixFamilyProbePoweredLpBound distribution probe exponent factor
        factorNonnegative sensitive).upper / threshold ^ exponent := by
  exact tailProbability_le_upper_div_of_poweredLp_mem distribution
    (prefixFamilyProbePoweredLpBound distribution probe exponent factor
      factorNonnegative sensitive)
    exponent threshold thresholdPositive
    (fun certificate => probe (points certificate))
    (prefixFamilyProbePoweredLpBound_contains distribution probe exponent
      factor factorNonnegative sensitive points pointsRealize)

/-- Centered form: finite CCL prefixes certify the probability that a probe
deviates from a displayed rational center by at least the threshold. -/
theorem prefixFamilyProbe_deviationProbability_le_upper_div
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate) (center : Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe center exponent left)
          (poweredDeviationProbe probe center exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun certificate => probe (points certificate))
          (fun _ => center)) ≤
      (prefixFamilyProbePoweredDeviationBound distribution probe center
        exponent factor factorNonnegative sensitive).upper /
          threshold ^ exponent := by
  exact tailProbability_le_upper_div_of_poweredLpDistance_mem distribution
    (prefixFamilyProbePoweredDeviationBound distribution probe center exponent
      factor factorNonnegative sensitive)
    exponent threshold thresholdPositive
    (fun certificate => probe (points certificate)) (fun _ => center)
    (prefixFamilyProbePoweredDeviationBound_contains distribution probe center
      exponent factor factorNonnegative sensitive points pointsRealize)

namespace PrefixFamilyProcess

/-- At every finite process state, the current powered-moment upper endpoint
gives a certified Markov tail bound for every realization family admitted at
that state. -/
theorem probe_tailProbability_le_currentPoweredLpUpper_div {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredProbe probe exponent left)
          (poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (state : process.State) (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => 0)) ≤
      ((process.toProbePoweredLpProcess distribution probe exponent factor
        factorPositive sensitive).bound state).upper /
        threshold ^ exponent := by
  exact tailProbability_le_upper_div_of_poweredLp_mem distribution
    ((process.toProbePoweredLpProcess distribution probe exponent factor
      factorPositive sensitive).bound state)
    exponent threshold thresholdPositive (fun item => probe (points item))
    (process.poweredLp_mem_toProbePoweredLpProcess_bound distribution
      probe exponent factor factorPositive sensitive state points
      pointsRealize)

/-- At every finite state, a centered powered-deviation enclosure supplies
the corresponding finite large-deviation probability bound. -/
theorem probe_deviationProbability_le_currentPoweredDeviationUpper_div
    {ι : Type} (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (center : Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe center exponent left)
          (poweredDeviationProbe probe center exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (state : process.State) (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => center)) ≤
      ((process.toProbePoweredDeviationProcess distribution probe center
        exponent factor factorPositive sensitive).bound state).upper /
          threshold ^ exponent := by
  exact tailProbability_le_upper_div_of_poweredLpDistance_mem distribution
    ((process.toProbePoweredDeviationProcess distribution probe center
      exponent factor factorPositive sensitive).bound state)
    exponent threshold thresholdPositive (fun item => probe (points item))
    (fun _ => center)
    (process.poweredLpDistanceConstant_mem_toProbePoweredDeviationProcess_bound
      distribution probe center exponent factor factorPositive sensitive state
      points pointsRealize)

/-- After one finite accuracy request, the CCL-powered Markov bound is sound
and its displayed moment numerator exceeds the exact realized powered moment
by less than the requested rational tolerance. -/
theorem request_probeTail_bound_and_numerator_close {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredProbe probe exponent left)
          (poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon)
    (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          ((process.toProbePoweredLpProcess distribution probe exponent factor
            factorPositive sensitive).request state epsilon positive)
          atom.item)
        (points atom.item)) :
    let poweredProcess := process.toProbePoweredLpProcess distribution probe
      exponent factor factorPositive sensitive
    let requested := poweredProcess.request state epsilon positive
    distribution.probability
        (_root_.FiniteMeasure.separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => 0)) ≤
        (poweredProcess.bound requested).upper / threshold ^ exponent ∧
      (poweredProcess.bound requested).upper -
          distribution.poweredLp exponent (fun item => probe (points item)) <
        epsilon := by
  dsimp only
  let poweredProcess := process.toProbePoweredLpProcess distribution probe
    exponent factor factorPositive sensitive
  let requested := poweredProcess.request state epsilon positive
  have actualInside : (poweredProcess.bound requested).Contains
      (distribution.poweredLp exponent fun item => probe (points item)) := by
    exact process.poweredLp_mem_toProbePoweredLpProcess_bound distribution
      probe exponent factor factorPositive sensitive requested points
      pointsRealize
  constructor
  · exact tailProbability_le_upper_div_of_poweredLp_mem distribution
      (poweredProcess.bound requested) exponent threshold thresholdPositive
      (fun item => probe (points item)) actualInside
  · have upperInside : (poweredProcess.bound requested).Contains
        (poweredProcess.bound requested).upper :=
      ⟨(poweredProcess.bound requested).valid, le_rfl⟩
    exact (poweredProcess.request_pairwise_difference_lt state epsilon positive
      upperInside actualInside).1

end PrefixFamilyProcess

end CCL.FiniteMeasure
