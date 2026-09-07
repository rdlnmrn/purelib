import CCL.Progressive.ExactProvenance

/-!
# Semantic completeness and invariance of exact division decisions

Exact zero means an executable operational comparison with zero exists;
preparability means an equivalent whole-ball-apart presentation exists.
Neither predicate demands pointwise equality of approximate candidates.
The converse completeness laws require a computed exact decision, supplied
below by rational provenance and by the separate algebraic client. They are
not equality decisions for arbitrary opaque channels.
-/

namespace CCL.ProgressiveExactProvenance

def IsZero (channel : CoherentNamed) : Prop := Nonempty (ZeroIdentity channel)
def IsPrepared (channel : CoherentNamed) : Prop := Nonempty (Prepared channel)

def ZeroIdentity.transport {first second : CoherentNamed} (zero : ZeroIdentity first)
    (equivalent : NamedEquivalent first.name second.name) : ZeroIdentity second :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalEquivalence.NamedEquivalent.symm equivalent) zero

/-- Retain the already computed denominator and its apartness. Only its
comparison to the new input presentation changes. -/
def Prepared.transport {first second : CoherentNamed} (prepared : Prepared first)
    (equivalent : NamedEquivalent first.name second.name) : Prepared second :=
  { denominator := prepared.denominator
    apart := prepared.apart
    equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm equivalent) prepared.equivalent }

theorem isZero_respects {first second : CoherentNamed}
    (equivalent : NamedEquivalent first.name second.name) : IsZero first ↔ IsZero second :=
  ⟨fun ⟨zero⟩ => ⟨zero.transport equivalent⟩,
    fun ⟨zero⟩ => ⟨zero.transport (CCL.OperationalEquivalence.NamedEquivalent.symm equivalent)⟩⟩

theorem isPrepared_respects {first second : CoherentNamed}
    (equivalent : NamedEquivalent first.name second.name) : IsPrepared first ↔ IsPrepared second :=
  ⟨fun ⟨prepared⟩ => ⟨prepared.transport equivalent⟩,
    fun ⟨prepared⟩ => ⟨prepared.transport (CCL.OperationalEquivalence.NamedEquivalent.symm equivalent)⟩⟩

namespace Decision

def isPrepared {channel : CoherentNamed} : Decision channel → Bool
  | .prepared _ => true
  | .excluded _ => false

theorem zero_iff_unpreparable {channel : CoherentNamed} (decision : Decision channel) :
    IsZero channel ↔ ¬ IsPrepared channel := by
  constructor
  · rintro ⟨zero⟩ ⟨prepared⟩
    exact zero.incompatible_prepared prepared
  · intro unavailable
    cases decision with
    | prepared prepared => exact False.elim (unavailable ⟨prepared⟩)
    | excluded zero => exact ⟨zero⟩

theorem prepared_iff_nonzero {channel : CoherentNamed} (decision : Decision channel) :
    IsPrepared channel ↔ ¬ IsZero channel := by
  constructor
  · rintro ⟨prepared⟩ ⟨zero⟩
    exact zero.incompatible_prepared prepared
  · intro nonzero
    cases decision with
    | prepared prepared => exact ⟨prepared⟩
    | excluded zero => exact False.elim (nonzero ⟨zero⟩)

theorem isPrepared_eq_true_iff {channel : CoherentNamed} (decision : Decision channel) :
    decision.isPrepared = true ↔ IsPrepared channel := by
  cases decision with
  | prepared prepared => exact ⟨fun _ => ⟨prepared⟩, fun _ => rfl⟩
  | excluded zero =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨prepared⟩
        exact False.elim (zero.incompatible_prepared prepared)

theorem isPrepared_eq_false_iff {channel : CoherentNamed} (decision : Decision channel) :
    decision.isPrepared = false ↔ IsZero channel := by
  cases decision with
  | prepared prepared =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨zero⟩
        exact False.elim (zero.incompatible_prepared prepared)
  | excluded zero => exact ⟨fun _ => ⟨zero⟩, fun _ => rfl⟩

/-- Independently derived exact verdicts cannot disagree on equivalent
inputs. Returned certificate data need not be equal. This law deliberately
does not cover the overlapping numerical small/apart classification. -/
theorem respects {first second : CoherentNamed} (left : Decision first) (right : Decision second)
    (equivalent : NamedEquivalent first.name second.name) : left.isPrepared = right.isPrepared := by
  cases left with
  | prepared prepared =>
      cases right with
      | prepared _ => rfl
      | excluded zero => exact False.elim (zero.incompatible_prepared (prepared.transport equivalent))
  | excluded zero =>
      cases right with
      | prepared prepared => exact False.elim ((zero.transport equivalent).incompatible_prepared prepared)
      | excluded _ => rfl

end Decision

/-- Successful outputs respect changes to both input presentations, not
just independently chosen preparations of the same syntactic channel. -/
def Prepared.quotient_respects_equivalent {first second firstNumerator secondNumerator : CoherentNamed}
    (left : Prepared first) (right : Prepared second)
    (denominators : NamedEquivalent first.name second.name)
    (numerators : NamedEquivalent firstNumerator.name secondNumerator.name) :
    NamedEquivalent (left.quotient firstNumerator).name (right.quotient secondNumerator).name :=
  CCL.ProgressiveDivisionCongruence.coherentDiv_respects firstNumerator secondNumerator
    left.denominator right.denominator left.apart right.apart numerators
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm left.equivalent)
      (CCL.OperationalEquivalence.NamedEquivalent.trans denominators right.equivalent))

theorem RationalSidecar.zero_iff_unpreparable {channel : CoherentNamed}
    (sidecar : RationalSidecar channel) : IsZero channel ↔ ¬ IsPrepared channel :=
  sidecar.decide.zero_iff_unpreparable

theorem RationalSidecar.prepared_iff_nonzero {channel : CoherentNamed}
    (sidecar : RationalSidecar channel) : IsPrepared channel ↔ ¬ IsZero channel :=
  sidecar.decide.prepared_iff_nonzero

theorem RationalSidecar.decide_respects {first second : CoherentNamed}
    (left : RationalSidecar first) (right : RationalSidecar second)
    (equivalent : NamedEquivalent first.name second.name) :
    left.decide.isPrepared = right.decide.isPrepared := left.decide.respects right.decide equivalent

end CCL.ProgressiveExactProvenance
