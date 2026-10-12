module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Power.Gaussian
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Gaussian.Division.Prepared.Decision
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
public import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Riemann.Branches.SquareRootSheets
import Purelib.RootIsolation.Track.Basic

public import Purelib.Riemann.RootContinuation.SquareRootProvenance

@[expose] public section

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

namespace Purelib.Riemann.RootContinuation.SquareRootSidecar

open Purelib.Riemann.RootContinuation.SquareRootProvenance (SquareIdentity Observation)

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

-- The coherent root is an already certified executable channel.  Keep this
-- type boundary opaque while elaborating the dependent owner record; its
-- finite internal sample cache is not part of the sidecar's type-level work.
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- Retain one finite square-root occurrence linked to an existing numerical channel.

The original ambient box and winding-one track are executable data, and operational equivalence connects the unchanged
channel to that selected track. -/
structure Owner (parameter : Gaussian.Basic.Canonical) (channel : Gaussian.Name.Coherent.CoherentNamed) where
  /-- The retained rational ambient box of the selected root track. -/ ambient : Rational.Box
  /-- The original winding-one track for the parameter's square-root polynomial. -/ track : Track.Basic.WindingOneTrack
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter RootContinuation.SquareRootDegree.degreeTwo) ambient
  /-- The supplied channel is operationally equivalent to the raw root channel of this exact track. -/ equivalent :
    Gaussian.Equivalence.NamedEquivalent channel.name (RootContinuation.CertifiedSquareRoot.rawRoot track).name

constructive_injectivity Owner

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Transport the retained track's square equation to the original numerical channel. -/
def Owner.square {parameter : Gaussian.Basic.Canonical} {channel : Gaussian.Name.Coherent.CoherentNamed}
    (owner : Owner parameter channel) : SquareIdentity channel parameter :=
  Gaussian.Equivalence.NamedEquivalent.trans
    (Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects channel
      (RootContinuation.CertifiedSquareRoot.rawRoot owner.track) channel
      (RootContinuation.CertifiedSquareRoot.rawRoot owner.track)
      owner.equivalent owner.equivalent)
    (RootContinuation.CertifiedSquareRoot.rawRoot_square owner.track)

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
/-- Every actual nested state of the retained track has quadrupled winding four. -/
theorem Owner.winding {parameter : Gaussian.Basic.Canonical} {channel : Gaussian.Name.Coherent.CoherentNamed}
    (owner : Owner parameter channel) (index : Nat) :
    Winding.Box.Basic.quadrupledBoxWinding
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter RootContinuation.SquareRootDegree.degreeTwo)
      (RootContinuation.CoherentRoot.state owner.track index).box = 4 :=
  RootContinuation.CoherentRoot.state_winding owner.track index

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Every later retained track box refines its earlier box. -/
theorem Owner.persistent {parameter : Gaussian.Basic.Canonical} {channel : Gaussian.Name.Coherent.CoherentNamed}
    (owner : Owner parameter channel) {earlier later : Nat} (order : earlier ≤ later) :
    (RootContinuation.CoherentRoot.state owner.track later).box.Refines
      (RootContinuation.CoherentRoot.state owner.track earlier).box :=
  RootContinuation.CoherentRoot.state_refines_of_le owner.track order

open Purelib.Approximation in
open Purelib.Data in
set_option genInjectivity false in
/-- Attach an exact square equation and optional finite root owner to a retained numerical channel.

The original Gaussian coefficient is explicit, and the optional owner preserves its track and operational channel link
when present. -/
structure Sidecar (channel : Gaussian.Name.Coherent.CoherentNamed) where
  /-- The exact Gaussian coefficient in the retained square equation. -/ parameter : Gaussian.Basic.Canonical
  /-- The original channel squares operationally to the exact retained coefficient. -/ square : SquareIdentity channel
    parameter
  /-- An optional retained simple-root track with its original channel link. -/ owner : Option (Owner parameter channel)

constructive_injectivity Sidecar

open Purelib.Approximation in
open Purelib.Data in
/-- Attach the supplied finite owner and its derived square equation to the same channel. -/
def Sidecar.ofOwner {parameter : Gaussian.Basic.Canonical} {channel : Gaussian.Name.Coherent.CoherentNamed}
    (owner : Owner parameter channel) : Sidecar channel :=
  ⟨parameter, owner.square, some owner⟩

open Purelib.Approximation in
/-- Transport algebraic provenance to a supplied operationally equivalent channel.

The original coefficient and optional isolation track are retained while their operational links are composed. -/
def Sidecar.transport {first second : Gaussian.Name.Coherent.CoherentNamed} (sidecar : Sidecar first)
    (equivalent : Gaussian.Equivalence.NamedEquivalent second.name first.name) : Sidecar second :=
  { parameter := sidecar.parameter
    square := Gaussian.Equivalence.NamedEquivalent.trans
      (Gaussian.Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects second first second first
        equivalent equivalent) sidecar.square
    owner := sidecar.owner.map fun owner =>
      { ambient := owner.ambient
        track := owner.track
        equivalent := Gaussian.Equivalence.NamedEquivalent.trans
          equivalent owner.equivalent } }

section
open Purelib.Riemann
open Purelib.Approximation
/-- Derive the residual observation bounds from the retained exact square equation. -/
def Sidecar.observe {channel : Gaussian.Name.Coherent.CoherentNamed} (sidecar : Sidecar channel) :
    Observation channel sidecar.parameter := RootContinuation.SquareRootProvenance.observe sidecar.square

/-- Decide exact zero or apartness using the actual rational coefficient.

For a nonzero coefficient, the cached square-equation comparison supplies the precision and prepared equivalent
denominator. -/
def Sidecar.decide {channel : Gaussian.Name.Coherent.CoherentNamed} (sidecar : Sidecar channel) :
    Approximation.Gaussian.Division.Prepared.Decision channel :=
  RootContinuation.SquareRootProvenance.decide sidecar.square

end

open Purelib.Approximation in
open Purelib.Data in
/-- The exact-zero square-root channel with coefficient zero and no simple-root owner. -/
def zeroSidecar : Sidecar (Gaussian.Name.Coherent.CoherentNamed.Coherence.exact 0) :=
  { parameter := 0
    square := by
      unfold SquareIdentity
      simpa only [Gaussian.Basic.zero_mul] using
        Gaussian.Name.Coherent.Exact.Arithmetic.exact_mul 0 0
    owner := none }

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
open Purelib.RootIsolation in
/-- Attach the supplied winding-one isolation track to its own retained raw root channel. -/
def tracked {parameter : Gaussian.Basic.Canonical} {ambient : Rational.Box}
    (track : Track.Basic.WindingOneTrack
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter RootContinuation.SquareRootDegree.degreeTwo) ambient)
        :
    Sidecar (RootContinuation.CertifiedSquareRoot.rawRoot track) :=
  Sidecar.ofOwner
    { ambient := ambient
      track := track
      equivalent := Gaussian.Equivalence.NamedEquivalent.refl _ }

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Compute and retain a square-root channel and provenance from a coefficient and finite sheet label.

A nonzero coefficient acquires its selected track once; the repeated-zero case returns the exact zero channel for either
label. -/
def isolated (parameter : Gaussian.Basic.Canonical) (sheet : Fin 2) :
    (channel : Gaussian.Name.Coherent.CoherentNamed) × Sidecar channel :=
  if nonzero : parameter ≠ 0 then
    let track := Branches.SquareRootSheets.track nonzero sheet
    ⟨RootContinuation.CertifiedSquareRoot.rawRoot track, tracked track⟩
  else ⟨Gaussian.Name.Coherent.CoherentNamed.Coherence.exact 0, zeroSidecar⟩

open Purelib.Data in
/-- The automatically isolated sidecar retains exactly the supplied coefficient. -/
@[simp] theorem isolated_parameter (parameter : Gaussian.Basic.Canonical) (sheet : Fin 2) :
    (isolated parameter sheet).2.parameter = parameter := by
  unfold isolated
  by_cases nonzero : parameter ≠ 0
  · rw [dif_pos nonzero]
    rfl
  · rw [dif_neg nonzero]
    exact (Decidable.of_not_not nonzero).symm

open Purelib.Approximation in
set_option genInjectivity false in
/-- Retain a coherent numerical channel with optional algebraic provenance.

The optional sidecar is indexed by that exact channel and can be discarded while preserving its process and output. -/
structure WithSidecar where
  /-- The original coherent numerical channel. -/ channel : Gaussian.Name.Coherent.CoherentNamed
  /-- Optional algebraic provenance for this exact channel. -/ sidecar : Option (Sidecar channel)

constructive_injectivity WithSidecar

/-- Discard optional algebraic provenance while retaining the exact original channel. -/
def WithSidecar.forget (input : WithSidecar) : WithSidecar :=
  { channel := input.channel, sidecar := none }

/-- Forgetting provenance preserves the channel definitionally. -/
@[simp] theorem WithSidecar.forget_channel (input : WithSidecar) :
    input.forget.channel = input.channel := rfl

end Purelib.Riemann.RootContinuation.SquareRootSidecar
