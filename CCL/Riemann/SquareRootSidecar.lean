import CCL.Riemann.SquareRootProvenance

/-!
# Isolated square-root sidecars

This is one concrete algebraic client, for the finite polynomial `Z² - w`.
The sidecar retains the chosen winding-one track, its ambient rational box,
and an operational link to the unchanged numerical channel. Every nested
track state retains winding one. Exact decisions and residual observation
bounds are derived from the actual coefficient `w`, not from an assumed
zero-or-apart answer or a pointwise root law for approximate readings.

The zero coefficient is handled separately: its root is exactly zero and
has multiplicity two, so no fictitious winding-one owner is attached.
This does not claim a general degree/height bound for arbitrary polynomials.
-/

namespace CCL.Riemann.SquareRootProvenance

open CCL.ProgressiveExactProvenance (Gaussian CoherentNamed NamedEquivalent)

/-- A selected finite root occurrence and its relation to the numerical
channel. Keeping the track as data avoids rerunning root isolation. -/
structure Owner (parameter : Gaussian) (channel : CoherentNamed) where
  ambient : RFAP.Boxes.Box
  track : RFAP.ShrinkingTrack.WindingOneTrack
    (CCL.PowerMonodromy.polynomial parameter CCL.Riemann.SquareRootSheets.degreeTwo) ambient
  equivalent : NamedEquivalent channel.name (CCL.Riemann.CertifiedSquareRoot.rawRoot track).name

def Owner.square {parameter : Gaussian} {channel : CoherentNamed}
    (owner : Owner parameter channel) : SquareIdentity channel parameter :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.TranscendentalCoherence.coherentMul_respects channel
      (CCL.Riemann.CertifiedSquareRoot.rawRoot owner.track) channel
      (CCL.Riemann.CertifiedSquareRoot.rawRoot owner.track)
      owner.equivalent owner.equivalent)
    (CCL.Riemann.CertifiedSquareRoot.rawRoot_square owner.track)

theorem Owner.winding {parameter : Gaussian} {channel : CoherentNamed}
    (owner : Owner parameter channel) (index : Nat) :
    RFAP.Winding.quadrupledBoxWinding
      (CCL.PowerMonodromy.polynomial parameter CCL.Riemann.SquareRootSheets.degreeTwo)
      (CCL.Riemann.CoherentRoot.state owner.track index).box = 4 :=
  CCL.Riemann.CoherentRoot.state_winding owner.track index

theorem Owner.persistent {parameter : Gaussian} {channel : CoherentNamed}
    (owner : Owner parameter channel) {earlier later : Nat} (order : earlier ≤ later) :
    (CCL.Riemann.CoherentRoot.state owner.track later).box.Refines
      (CCL.Riemann.CoherentRoot.state owner.track earlier).box :=
  CCL.Riemann.CoherentRoot.state_refines_of_le owner.track order

structure Sidecar (channel : CoherentNamed) where
  parameter : Gaussian
  square : SquareIdentity channel parameter
  owner : Option (Owner parameter channel)

def Sidecar.ofOwner {parameter : Gaussian} {channel : CoherentNamed}
    (owner : Owner parameter channel) : Sidecar channel :=
  ⟨parameter, owner.square, some owner⟩

/-- Attach provenance to an already retained numerical channel without
replacing its process or output cursor. -/
def Sidecar.transport {first second : CoherentNamed} (sidecar : Sidecar first)
    (equivalent : NamedEquivalent second.name first.name) : Sidecar second :=
  { parameter := sidecar.parameter
    square := CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentMul_respects second first second first
        equivalent equivalent) sidecar.square
    owner := sidecar.owner.map fun owner =>
      { ambient := owner.ambient
        track := owner.track
        equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans
          equivalent owner.equivalent } }

def Sidecar.observe {channel : CoherentNamed} (sidecar : Sidecar channel) :
    Observation channel sidecar.parameter := CCL.Riemann.SquareRootProvenance.observe sidecar.square

/-- The answer is selected by exact rational coefficient arithmetic. In the
nonzero case, the cached square-equation comparison provides the required
precision and prepared equivalent denominator. -/
def Sidecar.decide {channel : CoherentNamed} (sidecar : Sidecar channel) :
    CCL.ProgressiveExactProvenance.Decision channel :=
  CCL.Riemann.SquareRootProvenance.decide sidecar.square

/-- The exact-zero repeated root, with no false claim of simple ownership. -/
def zeroSidecar : Sidecar (CCL.ProgressiveCoherence.CoherentNamed.exact 0) :=
  { parameter := 0
    square := by
      unfold SquareIdentity
      simpa only [RFAP.ConstructiveGaussian.Gaussian.zero_mul] using
        CCL.ProgressiveExactProvenance.exact_mul 0 0
    owner := none }

/-- Reuse a supplied finite isolation track; no selected decision is input. -/
def tracked {parameter : Gaussian} {ambient : RFAP.Boxes.Box}
    (track : RFAP.ShrinkingTrack.WindingOneTrack
      (CCL.PowerMonodromy.polynomial parameter CCL.Riemann.SquareRootSheets.degreeTwo) ambient) :
    Sidecar (CCL.Riemann.CertifiedSquareRoot.rawRoot track) :=
  Sidecar.ofOwner
    { ambient := ambient
      track := track
      equivalent := CCL.OperationalEquivalence.NamedEquivalent.refl _ }

/-- Automatic isolated-root client: only a rational coefficient and one of
two finite labels are supplied. The nonzero track is computed once and
retained. In the repeated-zero case both labels yield the same exact root. -/
def isolated (parameter : Gaussian) (sheet : Fin 2) :
    (channel : CoherentNamed) × Sidecar channel :=
  if nonzero : parameter ≠ 0 then
    let track := CCL.Riemann.SquareRootSheets.track nonzero sheet
    ⟨CCL.Riemann.CertifiedSquareRoot.rawRoot track, tracked track⟩
  else ⟨CCL.ProgressiveCoherence.CoherentNamed.exact 0, zeroSidecar⟩

@[simp] theorem isolated_parameter (parameter : Gaussian) (sheet : Fin 2) :
    (isolated parameter sheet).2.parameter = parameter := by
  unfold isolated
  by_cases nonzero : parameter ≠ 0
  · rw [dif_pos nonzero]
    rfl
  · rw [dif_neg nonzero]
    exact (Decidable.of_not_not nonzero).symm

/-- Optional algebraic data can be forgotten; this operation changes neither
the channel nor any raw finite output. It fabricates no exact decision. -/
structure WithSidecar where
  channel : CoherentNamed
  sidecar : Option (Sidecar channel)

def WithSidecar.forget (input : WithSidecar) : WithSidecar :=
  { channel := input.channel, sidecar := none }

@[simp] theorem WithSidecar.forget_channel (input : WithSidecar) :
    input.forget.channel = input.channel := rfl

end CCL.Riemann.SquareRootProvenance
