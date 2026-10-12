module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Topology.Polygon.Stokes

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.DyadicConjugateIncrementComparison
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Tactic.Ring

public section

/-! Identify conjugate paired paths with the literal scalar energy path. -/
namespace Purelib.Integration.Path.ConjugatePathReadback
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Data.Gaussian.Basic (conj)

open Purelib.Data.Gaussian in
/-- Pair the original Gaussian value with its conjugate as the first coordinate. -/
@[expose] def conjugateDiagonal (value : Basic.Canonical) : PrimitivePoint := ⟨conj value, value⟩

section
open Purelib.Data.Gaussian
open Purelib.Integration.Path
open Purelib.Topology.Polygon
/-- The conjugate-diagonal embedding preserves addition of the original Gaussian values. -/
private theorem diagonal_add (first last : Basic.Canonical) :
    conjugateDiagonal (first + last) = (conjugateDiagonal first).add
      (conjugateDiagonal last) := by
  apply congrArg₂ Stokes.PrimitivePoint.mk
  · exact Basic.conj_add first last
  · rfl

/-- The conjugate-diagonal embedding preserves their exact directed difference. -/
theorem conjugateDiagonal_sub (first last : Basic.Canonical) :
    conjugateDiagonal (first - last) =
      Stokes.PrimitivePoint.sub
        (conjugateDiagonal first) (conjugateDiagonal last) := by
  apply congrArg₂ Stokes.PrimitivePoint.mk
  · apply Basic.ext
    · rfl
    · simp only [-eq_self, -iff_self, conjugateDiagonal, Data.Gaussian.Basic.conj, Basic.sub_im];
        ring1
  · rfl

end

section
open Purelib.Data.Gaussian
open Purelib.Integration.Path
/-- Tracing the conjugate-diagonal primitive increments recovers the original Gaussian increment trace. -/
private theorem diagonal_trace (start : Basic.Canonical) (values : List Basic.Canonical) :
    PairedIncrementArea.traceArea (conjugateDiagonal start) (values.map
      conjugateDiagonal) = IncrementArea.traceArea start values := by
  induction values generalizing start with
  | nil => rfl
  | cons value tail ih =>
      rw [List.map_cons, PairedIncrementArea.traceArea, ← diagonal_add, ih]
      rfl

/-- The paired area of the original conjugate-diagonal increments is their Gaussian path area. -/
theorem conjugateDiagonal_area (values : List Basic.Canonical) :
    PairedIncrementArea.area (values.map conjugateDiagonal) = IncrementArea.pathArea values := by
  rw [PairedIncrementArea.area_eq_trace]
  exact diagonal_trace 0 values

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
/-- Paired subdivision of conjugate-diagonal values equals embedding the original Gaussian dyadic increments. -/
theorem conjugateDiagonal_dyadic (value : Fraction.Rational → Basic.Canonical) (depth : Nat) (first last :
  Fraction.Rational) :
    DyadicPairedPrimitivePaths.increments
      (fun t => conjugateDiagonal (value t)) depth first last =
      (DyadicPrimitivePaths.dyadicIncrements value depth first last).map conjugateDiagonal := by
  induction depth generalizing first last with
  | zero => exact congrArg (fun point => [point]) (conjugateDiagonal_sub _ _).symm
  | succ depth ih =>
      simp only [-eq_self, -iff_self, DyadicPairedPrimitivePaths.increments,
        DyadicPrimitivePaths.dyadicIncrements,
        Purelib.Data.List.Map.map_append, ih]
      rfl

end Purelib.Integration.Path.ConjugatePathReadback
