module

public import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Admission
public import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Sidecar
public import Purelib.Algebra.Quadratic.Pair.Gaussian.Rational
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Admitted rational quadratic evidence at an unchanged numerical channel

The generic realization sidecar supplies coordinate completeness and finite
preparation. The positive rational admission retains its entire original root
owner and square inspection, so attaching field evidence preserves both the
source channel and the selected generator's nominal origin.
-/

public section

namespace Purelib.Approximation.Gaussian.Provenance.Quadratic

open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Algebra.Quadratic (Pair)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Division
open Purelib.Riemann.RootContinuation

set_option genInjectivity false in
/-- Admitted quadratic coordinates retaining the actual numerical channel and original supplied root owner. -/
structure Sidecar (channel : CoherentNamed) where
  /-- The actual original coherent generator. -/
  generator : CoherentNamed
  /-- The actual original root sidecar, including its retained isolation owner. -/
  origin : SquareRootSidecar.Sidecar generator
  /-- The complete positive nonsquare admission at that same original owner. -/
  admission : Realization.Admission generator origin
  /-- Generic admitted coordinate evidence at the unchanged original channel. -/
  evidence : Realization.Sidecar admission.realization channel

constructive_injectivity Sidecar

/-- Read the original rational pair coordinates using the retained admission's exact parameter identity. -/
@[expose] def Sidecar.coordinates {channel : CoherentNamed} (sidecar : Sidecar channel) :
    Pair Rational (-sidecar.admission.parameter) := by
  exact sidecar.admission.realization_parameter ▸ sidecar.evidence.value

/-- Attach admitted evidence using the exact existing pair, interpreted channel and original-source comparison. -/
@[noinline, nospecialize] def Sidecar.ofAdmission {generator channel : CoherentNamed}
    {origin : SquareRootSidecar.Sidecar generator} (admission : Realization.Admission generator origin)
    (value : Pair Rational (-admission.parameter)) (reading : CoherentNamed)
    (reading_eq : reading = Purelib.Algebra.Quadratic.Pair.Gaussian.denoteRational generator value)
    (equivalent : NamedEquivalent channel.name reading.name) : Sidecar channel := by
  let owner := Realization.rational admission.parameter generator
    (Realization.rootEquation origin admission.parameter admission.parameter_eq) admission.inspection admission.missing
  let retained : Realization.Denotation owner value :=
    ⟨admission.realization, admission.realization_eq, value, rfl, reading, reading_eq⟩
  let evidence : Realization.Sidecar owner channel :=
    ⟨channel, rfl, admission.realization, admission.realization_eq, value, retained, equivalent⟩
  exact ⟨generator, origin, admission, admission.realization_eq.symm ▸ evidence⟩

/-- Attach source evidence at the same original admitted generator, root owner and retained realization. -/
@[noinline, nospecialize] def Sidecar.withEvidence {source target : CoherentNamed} (basis : Sidecar source)
    (evidence : Realization.Sidecar basis.admission.realization target) : Sidecar target :=
  ⟨basis.generator, basis.origin, basis.admission, evidence⟩

/-- Transport admitted evidence to an explicitly compared channel while reusing the entire original admission. -/
@[noinline, nospecialize] def Sidecar.transport {first second : CoherentNamed} (sidecar : Sidecar first)
    (equivalent : NamedEquivalent second.name first.name) : Sidecar second :=
  sidecar.withEvidence (sidecar.evidence.transport equivalent)

/-- Decide exact zero or finite preparation at the original channel using its same admitted coordinate cache. -/
@[noinline, nospecialize] def Sidecar.decide {channel : CoherentNamed} (sidecar : Sidecar channel) :
    Prepared.Decision channel := sidecar.evidence.decide

/-- Recover exact scalar provenance at the unchanged source when its admitted generator coefficient is zero. -/
@[noinline, nospecialize] def Sidecar.scalarReading {channel : CoherentNamed} (sidecar : Sidecar channel)
    (zero : sidecar.evidence.value.im = 0) : RationalSidecar channel := sidecar.evidence.scalarReading zero

/-- Negate the actual channel while retaining the same original generator and admission cache. -/
@[noinline, nospecialize] def Sidecar.neg {channel : CoherentNamed} (sidecar : Sidecar channel) :
    Sidecar (CoherentNamed.neg channel) :=
  sidecar.withEvidence sidecar.evidence.neg

/-- Square the actual channel using its same admitted coordinate cache and original generator. -/
@[noinline, nospecialize] def Sidecar.square {channel : CoherentNamed} (sidecar : Sidecar channel) :
    Sidecar (CoherentNamed.mul channel channel) :=
  sidecar.withEvidence (sidecar.evidence.mul sidecar.evidence)

/-- Attach an original rational channel as a scalar in the same retained admitted realization. -/
private def scalarEvidence {channel scalarChannel : CoherentNamed} (sidecar : Sidecar channel)
    (scalar : RationalSidecar scalarChannel) (value : Rational)
    (same : scalar.value = Cast.CoordinateTaylor.ofCoordinate value) :
    Realization.Sidecar sidecar.admission.realization scalarChannel := by
  have equivalent := scalar.equivalent
  rewrite [same] at equivalent
  have compared : NamedEquivalent scalarChannel.name
      (CoherentNamed.Coherence.exact (sidecar.admission.realization.coefficient value)).name := by
    rewrite [sidecar.admission.coefficient_eq value]
    exact equivalent
  exact Realization.Sidecar.scalar sidecar.admission.realization value scalarChannel compared

/-- Add an original exact real rational channel on the left using the same admitted owner and coordinate cache. -/
@[noinline, nospecialize] def Sidecar.addScalarLeft {channel scalarChannel : CoherentNamed}
    (sidecar : Sidecar channel) (scalar : RationalSidecar scalarChannel) (value : Rational)
    (same : scalar.value = Cast.CoordinateTaylor.ofCoordinate value) :
    Sidecar (CoherentNamed.add scalarChannel channel) :=
  sidecar.withEvidence ((scalarEvidence sidecar scalar value same).add sidecar.evidence)

/-- Add an original exact real rational channel on the right using the same admitted owner and coordinate cache. -/
@[noinline, nospecialize] def Sidecar.addScalarRight {channel scalarChannel : CoherentNamed}
    (sidecar : Sidecar channel) (scalar : RationalSidecar scalarChannel) (value : Rational)
    (same : scalar.value = Cast.CoordinateTaylor.ofCoordinate value) :
    Sidecar (CoherentNamed.add channel scalarChannel) :=
  sidecar.withEvidence (sidecar.evidence.add (scalarEvidence sidecar scalar value same))

/-- Multiply an original exact real rational channel on the left using the same admitted owner and coordinate cache. -/
@[noinline, nospecialize] def Sidecar.mulScalarLeft {channel scalarChannel : CoherentNamed}
    (sidecar : Sidecar channel) (scalar : RationalSidecar scalarChannel) (value : Rational)
    (same : scalar.value = Cast.CoordinateTaylor.ofCoordinate value) :
    Sidecar (CoherentNamed.mul scalarChannel channel) :=
  sidecar.withEvidence ((scalarEvidence sidecar scalar value same).mul sidecar.evidence)

/-- Multiply an original exact real rational channel on the right using the same admitted owner and coordinate cache. -/
@[noinline, nospecialize] def Sidecar.mulScalarRight {channel scalarChannel : CoherentNamed}
    (sidecar : Sidecar channel) (scalar : RationalSidecar scalarChannel) (value : Rational)
    (same : scalar.value = Cast.CoordinateTaylor.ofCoordinate value) :
    Sidecar (CoherentNamed.mul channel scalarChannel) :=
  sidecar.withEvidence (sidecar.evidence.mul (scalarEvidence sidecar scalar value same))

end Purelib.Approximation.Gaussian.Provenance.Quadratic

end
