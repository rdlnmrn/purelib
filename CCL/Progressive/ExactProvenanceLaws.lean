import CCL.Progressive.ExactProvenance
import CCL.Arithmetic.OperationalFieldLaws

/-! # Transporting exact rational provenance through finite arithmetic -/

namespace CCL.ProgressiveExactProvenance

def exact_add (first second : Gaussian) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.exact first)
        (CCL.ProgressiveCoherence.CoherentNamed.exact second)).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact (first + second)).name :=
  CCL.OperationalEquivalence.Equivalent.of_constant_samples _ _ (first + second)
    (fun _ => rfl) (fun _ => rfl)

def exact_mul (first second : Gaussian) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (CCL.ProgressiveCoherence.CoherentNamed.exact first)
        (CCL.ProgressiveCoherence.CoherentNamed.exact second)).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact (first * second)).name :=
  CCL.OperationalEquivalence.Equivalent.of_constant_samples _ _ (first * second)
    (fun _ => rfl) (fun _ => rfl)

def RationalSidecar.add {first second : CoherentNamed}
    (left : RationalSidecar first) (right : RationalSidecar second) :
    RationalSidecar (CCL.ProgressiveCoherence.CoherentNamed.add first second) :=
  { value := left.value + right.value
    equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentAdd_respects first
        (CCL.ProgressiveCoherence.CoherentNamed.exact left.value) second
        (CCL.ProgressiveCoherence.CoherentNamed.exact right.value)
        left.equivalent right.equivalent)
      (exact_add left.value right.value) }

def RationalSidecar.mul {first second : CoherentNamed}
    (left : RationalSidecar first) (right : RationalSidecar second) :
    RationalSidecar (CCL.ProgressiveCoherence.CoherentNamed.mul first second) :=
  { value := left.value * right.value
    equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_respects first
        (CCL.ProgressiveCoherence.CoherentNamed.exact left.value) second
        (CCL.ProgressiveCoherence.CoherentNamed.exact right.value)
        left.equivalent right.equivalent)
      (exact_mul left.value right.value) }

/-- Symbolic cancellation supplies exact-zero provenance for any coherent
input, without requiring exact rational provenance for that input. -/
def RationalSidecar.addNeg (input : CoherentNamed) :
    RationalSidecar (CCL.ProgressiveCoherence.CoherentNamed.add input
      (CCL.ProgressiveCoherence.CoherentNamed.neg input)) :=
  ⟨0, CCL.OperationalFieldLaws.coherentAdd_neg_right input⟩

theorem addNeg_excludes_every_budget (input numerator : CoherentNamed)
    (state : State (CCL.ProgressiveCoherence.CoherentNamed.add input
      (CCL.ProgressiveCoherence.CoherentNamed.neg input))) (fuel : Nat) :
    ∃ final reachable, CCL.ProgressivePartialDivision.attempt numerator
      (CCL.ProgressiveCoherence.CoherentNamed.add input
        (CCL.ProgressiveCoherence.CoherentNamed.neg input)) state fuel =
      .exhausted final reachable :=
  ZeroIdentity.attempt_exhausts
    (channel := CCL.ProgressiveCoherence.CoherentNamed.add input
      (CCL.ProgressiveCoherence.CoherentNamed.neg input))
    (CCL.OperationalFieldLaws.coherentAdd_neg_right input)
    numerator state fuel

end CCL.ProgressiveExactProvenance
