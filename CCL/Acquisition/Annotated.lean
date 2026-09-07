import CCL.Acquisition

/-!
# Numerical channels with automatically propagated finite provenance

Arithmetic constructors keep the actual numerical program. Their sidecars
are derived by operational laws, never by treating approximate samples as
exact values. Unsupported combinations lose only the sidecar. This is a
small supported rule set, not general algebraic-number normalization.
-/

namespace CCL.AcquisitionAutomation

open CCL.FiniteAcquisition (Q Gaussian CoherentNamed Provenance)
open CCL.ProgressiveExactProvenance (RationalSidecar NamedEquivalent)

def transportProvenance {first second : CoherentNamed} (provenance : Provenance first)
    (equivalent : NamedEquivalent second.name first.name) : Provenance second :=
  match provenance with
  | .inl rational => .inl ⟨rational.value,
      CCL.OperationalEquivalence.NamedEquivalent.trans equivalent rational.equivalent⟩
  | .inr root => .inr (root.transport equivalent)

structure Annotated where
  channel : CoherentNamed
  provenance : Option (Provenance channel)

def Annotated.opaque (channel : CoherentNamed) : Annotated := ⟨channel, none⟩

def Annotated.rational (value : Gaussian) : Annotated :=
  ⟨CCL.ProgressiveCoherence.CoherentNamed.exact value, some (.inl (RationalSidecar.exact value))⟩

def Annotated.root (parameter : Gaussian) (sheet : Fin 2) : Annotated :=
  let isolated := CCL.Riemann.SquareRootProvenance.isolated parameter sheet
  ⟨isolated.1, some (.inr isolated.2)⟩

def Annotated.forget (input : Annotated) : Annotated := ⟨input.channel, none⟩

@[simp] theorem Annotated.forget_channel (input : Annotated) : input.forget.channel = input.channel := rfl

def exactNeg (value : Gaussian) : NamedEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.neg (CCL.ProgressiveCoherence.CoherentNamed.exact value)).name
    (CCL.ProgressiveCoherence.CoherentNamed.exact (-value)).name :=
  CCL.OperationalEquivalence.Equivalent.of_constant_samples _ _ (-value) (fun _ => rfl) (fun _ => rfl)

def negateRational {channel : CoherentNamed} (rational : RationalSidecar channel) :
    RationalSidecar (CCL.ProgressiveCoherence.CoherentNamed.neg channel) :=
  ⟨-rational.value, CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.Riemann.FiniteBilinear.coherentNeg_respects channel
      (CCL.ProgressiveCoherence.CoherentNamed.exact rational.value) rational.equivalent)
    (exactNeg rational.value)⟩

def Annotated.neg (input : Annotated) : Annotated :=
  { channel := CCL.ProgressiveCoherence.CoherentNamed.neg input.channel
    provenance := match input.provenance with
      | some (.inl rational) => some (.inl (negateRational rational))
      | _ => none }

def addRightZero (left right : CoherentNamed) (zero : CCL.ProgressiveExactProvenance.ZeroIdentity right) :
    NamedEquivalent (CCL.ProgressiveCoherence.CoherentNamed.add left right).name left.name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.TranscendentalCoherence.coherentAdd_respects left left right
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0)
      (CCL.OperationalEquivalence.NamedEquivalent.refl _) zero)
    (CCL.OperationalFieldLaws.coherentAdd_zero_right left)

def addLeftZero (left right : CoherentNamed) (zero : CCL.ProgressiveExactProvenance.ZeroIdentity left) :
    NamedEquivalent (CCL.ProgressiveCoherence.CoherentNamed.add left right).name right.name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.TranscendentalCoherence.coherentAdd_respects left
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0) right right zero
      (CCL.OperationalEquivalence.NamedEquivalent.refl _))
    (CCL.OperationalFieldLaws.coherentAdd_zero_left right)

def rationalZero {channel : CoherentNamed} (rational : RationalSidecar channel) (zero : rational.value = 0) :
    CCL.ProgressiveExactProvenance.ZeroIdentity channel := by
  unfold CCL.ProgressiveExactProvenance.ZeroIdentity
  simpa only [zero] using rational.equivalent

def Annotated.add (left right : Annotated) : Annotated :=
  { channel := CCL.ProgressiveCoherence.CoherentNamed.add left.channel right.channel
    provenance := match left.provenance, right.provenance with
      | some (.inl first), some (.inl second) => some (.inl (first.add second))
      | some (.inl first), other =>
          if zero : first.value = 0 then other.map fun p =>
            transportProvenance p (addLeftZero _ _ (rationalZero first zero)) else none
      | other, some (.inl second) =>
          if zero : second.value = 0 then other.map fun p =>
            transportProvenance p (addRightZero _ _ (rationalZero second zero)) else none
      | _, _ => none }

def mulRightConstant (left right : CoherentNamed) (rational : RationalSidecar right) :
    NamedEquivalent (CCL.ProgressiveCoherence.CoherentNamed.mul left right).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul left
        (CCL.ProgressiveCoherence.CoherentNamed.exact rational.value)).name :=
  CCL.TranscendentalCoherence.coherentMul_respects left left right
    (CCL.ProgressiveCoherence.CoherentNamed.exact rational.value)
    (CCL.OperationalEquivalence.NamedEquivalent.refl _) rational.equivalent

def mulLeftConstant (left right : CoherentNamed) (rational : RationalSidecar left) :
    NamedEquivalent (CCL.ProgressiveCoherence.CoherentNamed.mul left right).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (CCL.ProgressiveCoherence.CoherentNamed.exact rational.value) right).name :=
  CCL.TranscendentalCoherence.coherentMul_respects left
    (CCL.ProgressiveCoherence.CoherentNamed.exact rational.value) right right rational.equivalent
    (CCL.OperationalEquivalence.NamedEquivalent.refl _)

def Annotated.mul (left right : Annotated) : Annotated :=
  { channel := CCL.ProgressiveCoherence.CoherentNamed.mul left.channel right.channel
    provenance := match left.provenance, right.provenance with
      | some (.inl first), some (.inl second) => some (.inl (first.mul second))
      | some (.inl first), other =>
          if zero : first.value = 0 then some (.inl (RationalSidecar.zero
            (CCL.OperationalEquivalence.NamedEquivalent.trans
              (by simpa only [zero, CCL.ProgressiveCoherence.CoherentNamed.mul,
                CCL.ProgressiveCoherence.CoherentNamed.exact] using mulLeftConstant left.channel right.channel first)
              (CCL.OperationalFieldLaws.coherentMul_zero_left right.channel))))
          else if one : first.value = 1 then other.map fun p => transportProvenance p
            (CCL.OperationalEquivalence.NamedEquivalent.trans
              (by simpa only [one, CCL.ProgressiveCoherence.CoherentNamed.mul,
                CCL.ProgressiveCoherence.CoherentNamed.exact] using mulLeftConstant left.channel right.channel first)
              (CCL.OperationalFieldLaws.coherentMul_one_left right.channel))
          else none
      | other, some (.inl second) =>
          if zero : second.value = 0 then some (.inl (RationalSidecar.zero
            (CCL.OperationalEquivalence.NamedEquivalent.trans
              (by simpa only [zero, CCL.ProgressiveCoherence.CoherentNamed.mul,
                CCL.ProgressiveCoherence.CoherentNamed.exact] using mulRightConstant left.channel right.channel second)
              (CCL.OperationalFieldLaws.coherentMul_zero_right left.channel))))
          else if one : second.value = 1 then other.map fun p => transportProvenance p
            (CCL.OperationalEquivalence.NamedEquivalent.trans
              (by simpa only [one, CCL.ProgressiveCoherence.CoherentNamed.mul,
                CCL.ProgressiveCoherence.CoherentNamed.exact] using mulRightConstant left.channel right.channel second)
              (CCL.OperationalFieldLaws.coherentMul_one_right left.channel))
          else none
      | _, _ => none }

/-- The same compiled channel is shared by both occurrences. -/
def Annotated.cancel (input : Annotated) : Annotated :=
  ⟨CCL.ProgressiveCoherence.CoherentNamed.add input.channel
      (CCL.ProgressiveCoherence.CoherentNamed.neg input.channel),
    some (.inl (RationalSidecar.addNeg input.channel))⟩

/-- A retained square equation recovers exact rational provenance for the
square, even when no rational reading is itself an exact root. -/
def Annotated.square (input : Annotated) : Annotated :=
  { channel := CCL.ProgressiveCoherence.CoherentNamed.mul input.channel input.channel
    provenance := match input.provenance with
      | some (.inl rational) => some (.inl (rational.mul rational))
      | some (.inr root) => some (.inl ⟨root.parameter, root.square⟩)
      | none => none }

def Annotated.rationalValue (input : Annotated) : Option Gaussian :=
  match input.provenance with
  | some (.inl rational) => some rational.value
  | _ => none

end CCL.AcquisitionAutomation
