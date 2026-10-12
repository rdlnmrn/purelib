module

import Purelib.Approximation.Gaussian.Logarithm.Local.Horner.Sample
import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel
import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel.Arithmetic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Arithmetic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel
import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Calculus.Jet.Quadratic.Exact
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Channel
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Channel
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

namespace Purelib

section Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

section
open Purelib.Data
namespace CCL.Progressive.AutomaticQuadraticTrace.Trace

/-- The Gaussian rational obtained by embedding the rational scalar two. -/
private def reducedLogSlope : Canonical :=
  Gaussian.RationalEmbedding.ComplexLog.scalar 2

end CCL.Progressive.AutomaticQuadraticTrace.Trace

namespace Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog.AutomaticQuadraticTrace

/-- The Gaussian rational obtained by embedding the rational scalar two. -/
def
  reducedLogSlopePublic
  : Canonical :=
  Gaussian.RationalEmbedding.ComplexLog.scalar 2

end Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog.AutomaticQuadraticTrace

end

namespace Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

open Purelib.Approximation in
open Purelib.Data in
/-- Every finite reduced-logarithm sample at zero is zero. -/
private theorem reducedLogSample_zero
  (index : Nat) :
    Gaussian.Logarithm.Local.Horner.Sample.sample 0 index = 0 := by
  rw [Gaussian.Logarithm.Local.Horner.Sample.sample_eq,
    Gaussian.Logarithm.Local.Horner.Sample.outputFactor_eq]
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.RationalEmbedding.ComplexLog.scalar,
      Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] <;> ring1

end Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

namespace Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
/-- Build an exact quadratic certificate for one finite reduced-logarithm sample.

The certificate has zero base, slope two and sample depth index plus one. Its remainder is the exact output minus the
linear term; the displayed disk premise bounds increment quadrance by one ninth. -/
def reducedLogCertificate (increment
  : Canonical)
    (_disk : Data.Gaussian.Norm.Basic.normSq increment ≤ 1 / 9) (index : Nat) :
    Certificate increment :=
  Certificate.ofExpansion
    increment 0 AutomaticQuadraticTrace.reducedLogSlopePublic
    (Gaussian.Logarithm.Local.Horner.Sample.sample increment (index + 1))
    (Gaussian.Logarithm.Local.Horner.Sample.sample increment (index + 1) -
      0 - increment * AutomaticQuadraticTrace.reducedLogSlopePublic)
    rfl (by
      intro zero
      subst increment
      rw [reducedLogSample_zero, _root_.sub_self,
        Gaussian.Basic.zero_mul,
        Gaussian.Basic.zero_sub]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.neg_re, Gaussian.Basic.neg_im, Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] <;>
          ring1)

end Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

namespace Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

open Purelib.Approximation.Gaussian.Sequence.Geometric in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Data in
/-- Build the reduced-logarithm trace of a geometrically controlled input channel.

Every input has quadrance at most one ninth. The zero base, constant slope, sampled output and exact residual channels
yield common transport for the indexed finite certificates. -/
def reducedLogOuterTrace {source :
  Nat → Canonical}
    (sourceChannel : Approximation.Gaussian.Sequence.Geometric.Channel source)
    (disk : ∀ index, Data.Gaussian.Norm.Basic.normSq (source index) ≤ 1 / 9) : Trace source := by
  let certificates := fun index =>
    reducedLogCertificate (source index) (disk index) index
  let baseChannel := Approximation.Gaussian.Sequence.Geometric.Channel.exact 0
  let slopeChannel := Approximation.Gaussian.Sequence.Geometric.Channel.exact
      AutomaticQuadraticTrace.reducedLogSlopePublic
  let outputChannel := sourceChannel.reducedLogSample disk
  let remainderChannel :=
    (outputChannel.sub baseChannel).sub (sourceChannel.mul slopeChannel)
  have baseChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).base) :=
    baseChannel.map (by intro index; rfl)
  have outputChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).output) :=
    outputChannel.map (by intro index; rfl)
  have slopeChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).slope) :=
    slopeChannel.map (by intro index; rfl)
  have remainderChannel' :
      Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).remainder) :=
    remainderChannel.map (by intro index; rfl)
  exact Trace.ofTransport
    (Transport.Channel.transportOfChannels sourceChannel baseChannel' outputChannel'
      slopeChannel' remainderChannel')

end Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

namespace Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

open Purelib.Approximation.Gaussian.Sequence.Geometric in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Data in
/-- Each outer reduced-logarithm trace certificate is the finite certificate at that input and index. -/
@[simp] theorem
  reducedLogOuterTrace_certificate
    {source : Nat → Canonical} (sourceChannel : Approximation.Gaussian.Sequence.Geometric.Channel source)
    (disk : ∀ index, Data.Gaussian.Norm.Basic.normSq (source index) ≤ 1 / 9) (index : Nat) :
    (reducedLogOuterTrace sourceChannel disk).certificate index =
      reducedLogCertificate (source index) (disk index) index := rfl

end Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

namespace Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Data in
/-- Compose an inner trace with the finite reduced logarithm of its output displacement.

Displacement quadrance is at most one ninth and original increment quadrance is at most one at every index. The
displacement channel determines the outer trace and its automatic transport. -/
def reducedLogAutomatic {increment :
  Nat → Canonical}
    (inner : Trace increment)
    (movementDisk : ∀ index,
      Data.Gaussian.Norm.Basic.normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1 / 9)
    (incrementUnit : ∀ index, Data.Gaussian.Norm.Basic.normSq (increment index) ≤ 1) :
    Trace increment :=
  let movementChannel := (Channel.outputField inner).sub (Channel.baseField inner)
  Arithmetic.composeAutomatic inner
    (reducedLogOuterTrace movementChannel movementDisk) (fun index => by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using incrementUnit index)

end Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

namespace Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Data in
/-- Each automatic reduced-logarithm certificate is the inner certificate composed with its indexed local certificate.
-/
@[simp] theorem
  reducedLogAutomatic_certificate
    {increment : Nat → Canonical} (inner : Trace increment)
    (movementDisk : ∀ index,
      Data.Gaussian.Norm.Basic.normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1 / 9)
    (incrementUnit : ∀ index, Data.Gaussian.Norm.Basic.normSq (increment index) ≤ 1)
    (index : Nat) :
    Trace.certificate
        (reducedLogAutomatic inner movementDisk incrementUnit) index =
      (inner.certificate index).compose
        (reducedLogCertificate
          ((inner.certificate index).output -
            (inner.certificate index).base)
          (movementDisk index) index)
        (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using incrementUnit index) := rfl

end Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

end Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

end Purelib

end
