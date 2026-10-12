module
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
import Purelib.Approximation.Gaussian.Process.Apart.Based
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Gamma.Downscale
public import Purelib.Approximation.Gaussian.Process.Gamma.Inverse.Scale
public import Purelib.Approximation.Gaussian.Process.Gamma.Upscale
import Purelib.Approximation.Gaussian.Process.Recipe.Cursor
public import Purelib.Approximation.Gaussian.Process.Recipe.Inverse
public import Purelib.Approximation.Gaussian.Process.Sector.Residual
import Purelib.Data.CCL.Transducer.Replay.Check
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Power
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observe
public import Purelib.Integration.Program.Gaussian.Query.Representation

import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Computation.Query.Computation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Computation.Query.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Approximation.Gaussian.Process.Recipe.Basic
import Purelib.Data.CCL.Transducer.Replay.Failure

/-!
# Projection from the finite replay controller to certified execution

The relation is proof-facing only.  Its process and source-index map never
enter the executable replay state.  Chart constructors derive the relation
from the original cached program; clients do not supply a simulation oracle.
-/

namespace Purelib.Integration.Program.Gaussian.Query.CursorRepresentation

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- A retained recipe representation whose exact process state maps to the original cursor index.

The witness is an exact representation over the same cached program,
recipe and certified process. Its state-index equality identifies the
original cursor index without adding a process callback to cursor data. -/
@[expose] public def CursorRep (program : Basic.CachedProgram) (cursor : Approximation.Gaussian.Process.Recipe.Cursor)
    (process :
  Approximation.Gaussian.Process)
    (state : process.State) : Prop :=
  ∃ representation : Representation.Represents program cursor.recipe process,
    representation.index state = cursor.index

namespace CursorRep

open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- The original source cursor represents the exact program process at the same retained index.

The source recipe and identity stage-index map represent the original
program approximation at its supplied natural stage index. -/
public theorem source (program : Basic.CachedProgram) (index : Nat) :
    CursorRep program ⟨.source, index⟩ program.approximation.toProcess index :=
  ⟨Representation.Represents.source program, rfl⟩

section
open Purelib.Approximation.Gaussian
open Purelib.CCL.Progressive
open Purelib.Data.Rat in
open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- Refining the original cursor for a positive target represents the exact corresponding process refinement.

The positive target refines the same certified process state and
retained cursor. The representation refinement equation identifies their
original recipe-selected source stage. -/
public theorem refined {program : Basic.CachedProgram} {cursor : Approximation.Gaussian.Process.Recipe.Cursor} {process
    :
  Approximation.Gaussian.Process}
    {state : process.State} (represented : CursorRep program cursor process state)
    (target : Fraction.Rational) (positive : 0 < target) :
    CursorRep program (cursor.refined (IntegrationReplay.control program) target)
      process (process.refine state target positive) := by
  obtain ⟨representation, indexEqual⟩ := represented
  refine ⟨representation, ?_⟩
  rw [representation.refine_eq, indexEqual]
  rfl

open Purelib.Computation.Query in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- The represented cursor observation returns its exact refined cursor and original refined process ball.

The original recipe runs against the retained program stage procedure.
Its checked successful reply contains the same refined cursor and
certified process ball, preserving the original accuracy evidence. -/
public theorem observe {program : Basic.CachedProgram} {cursor : Approximation.Gaussian.Process.Recipe.Cursor} {process
    :
  Approximation.Gaussian.Process}
    {state : process.State} (represented : CursorRep program cursor process state)
    (target : Fraction.Rational) (positive : 0 < target) :
    ((cursor.observe (IntegrationReplay.control program) target).run program.stage).value =
      .ok (cursor.refined (IntegrationReplay.control program) target,
        Enclosure.Ball.Data.BallData.ofBall (process.ball (process.refine state target positive))) := by
  obtain ⟨representation, indexEqual⟩ := represented.refined target positive
  have observed := representation.ball_run (process.refine state target positive)
  rw [indexEqual] at observed
  unfold Approximation.Gaussian.Process.Recipe.Cursor.observe
  rw [Computation.Query.Protocol.map_run_value, observed]
  change (Replay.Check.checkedBall _ target (Enclosure.Ball.Data.BallData.ofBall (process.ball (process.refine state
    target positive)))).map _ = _
  rw [Replay.Check.checkedBall, dif_pos ⟨(process.ball _).radiusSq_nonneg, process.accurate state target positive⟩]
  rfl

open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- Unary downscaling retains representation by the exact inverse-gamma-scaled cursor.

The same original process state is retained as the base of the unary
scaled process. Multiplication by inverse gamma matches the retained
recipe scaling and preserves its original source index. -/
public theorem unary {program : Basic.CachedProgram} {cursor : Approximation.Gaussian.Process.Recipe.Cursor} {process :
  Approximation.Gaussian.Process}
    {state : process.State} (represented : CursorRep program cursor process state) :
    CursorRep program (cursor.scaled (IntegrationReplay.control program) gamma⁻¹)
      (Process.Gamma.Downscale.unaryScaledProcess process state)
      (Process.Gamma.Downscale.unaryScaledInitial process state) := by
  obtain ⟨representation, indexEqual⟩ := represented
  exact ⟨(representation.based state).scaled gamma⁻¹, indexEqual⟩

open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- Subtracting the original sector representative retains the exact translated cursor representation.

The same original state is based and translated by the supplied sector
representative. The retained cursor recipe and process therefore share
that exact Gaussian shift and source index. -/
public theorem residual {program : Basic.CachedProgram} {cursor : Approximation.Gaussian.Process.Recipe.Cursor} {process
    :
  Approximation.Gaussian.Process}
    {state : process.State} (represented : CursorRep program cursor process state)
    (sector : Data.ComplexContinuedFraction.Encoding.Sector) :
    CursorRep program (cursor.translated (IntegrationReplay.control program) sector.rep)
      (Process.Sector.Residual.residualProcess process state sector)
      (Process.Sector.Residual.residualInitial process state sector) := by
  obtain ⟨representation, indexEqual⟩ := represented
  exact ⟨(representation.based state).translated sector.rep, indexEqual⟩

open Purelib.Data.Gaussian
open Purelib.Integration.Program.Gaussian.Cached
open Purelib.Integration.Program.Gaussian.Query
/-- Gamma-power upscaling retains representation by the corresponding exact scaled cursor.

The supplied natural exponent determines the original retained gamma
power. Both the based process and cursor recipe use that same factor
and retain the original process-state index. -/
public theorem upscaled {program : Basic.CachedProgram} {cursor : Approximation.Gaussian.Process.Recipe.Cursor} {process
    :
  Approximation.Gaussian.Process}
    {state : process.State} (represented : CursorRep program cursor process state) (exponent : Nat) :
    CursorRep program (cursor.scaled (IntegrationReplay.control program) (Power.natPow Basic.Canonical.gamma exponent))
      (Process.Gamma.Upscale.upscaledProcess process state exponent)
      (Process.Gamma.Upscale.upscaledInitial process state exponent) := by
  obtain ⟨representation, indexEqual⟩ := represented
  exact ⟨(representation.based state).scaled (Power.natPow Basic.Canonical.gamma exponent), indexEqual⟩

/-- Normalized inversion retains the exact inverse cursor representation using the original ball nonzero certificate and
count.

The preparation index is the original recipe refinement at one twelfth
of the certificate's lower squared bound. The same based state,
apartness certificate, gamma factor and natural count determine every
subsequent division and scaling operation. -/
public theorem inverse {program : Basic.CachedProgram} {cursor : Approximation.Gaussian.Process.Recipe.Cursor} {process
    :
  Approximation.Gaussian.Process}
    {state : process.State} (represented : CursorRep program cursor process state)
    (certificate : Approximation.Gaussian.Enclosure.Ball.Apart (process.ball state)) (count : Nat) :
    CursorRep program (Process.Recipe.Inverse.inverseCursor (IntegrationReplay.control program) cursor
      certificate.lowerSq count)
      (Process.Gamma.Inverse.Scale.normalizedInverseProcess process state certificate count)
      (Process.Gamma.Inverse.Scale.normalizedInverseInitial process state certificate count) := by
  obtain ⟨representation, indexEqual⟩ := represented
  let candidate := Process.Apart.Based.possibleApartOfBall process state certificate
  refine ⟨(((representation.based state).apartified candidate).divided gamma⁻¹
    (Process.Apart.Preparation.apartifyApart candidate)).scaled (Power.natPow Basic.Canonical.gamma count)⁻¹, ?_⟩
  change representation.index (process.refine state (certificate.lowerSq / 12) _) = _
  rw [representation.refine_eq, indexEqual]
  rfl

end

end CursorRep
end Purelib.Integration.Program.Gaussian.Query.CursorRepresentation
