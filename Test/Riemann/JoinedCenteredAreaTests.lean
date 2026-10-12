module
import Purelib.Data.Gaussian.Basic

import Purelib.Integration.Path.JoinedTrace
public import Purelib.Integration.Path.JoinedCenteredArea
import Purelib.Data.Fin
import Init.Data.Fin.Lemmas
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Integration.Path

open Purelib.Integration.Path.JoinedTrace

@[expose] public section

/-! A closed conjugate-energy triangle_public has zero centered area on each
individual chord but nonzero centered area after concatenation. The endpoint
polygon is therefore essential even with exact coincident owner readings. -/
namespace Test.Riemann.JoinedCenteredAreaTests

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Integration.Path.JoinedTrace (VertexTrace)
open Purelib.Integration.Path.JoinedTrace.VertexTrace (concatenate)
open Purelib.Integration.Path.JoinedCenteredArea (endpointPolygon)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)

/-- The three original single-edge traces forming a closed conjugate-energy triangle. -/
public def triangle : Fin 3 → JoinedTrace.VertexTrace PrimitivePoint :=
  Data.Fin.casesByRecursion ⟨⟨0, 0⟩, [⟨1, 1⟩]⟩
    (Data.Fin.casesByRecursion ⟨⟨1, 1⟩, [⟨⟨0, -1⟩, ⟨0, 1⟩⟩]⟩
      (fun _ => ⟨⟨⟨0, -1⟩, ⟨0, 1⟩⟩, [⟨0, 0⟩]⟩))

/-- Concatenating the original three traces returns to the exact starting point. -/
theorem closed : (VertexTrace.concatenate triangle).first = (VertexTrace.concatenate triangle).last := rfl

/-- Every individual retained chord has zero centered area. -/
theorem piece_centered_zero : ∀ index : Fin 3,
    (Sample.build (fun vertex => (triangle index).indexed vertex)).centeredArea = 0 := by decide

/-- The concatenated original triangle has nonzero centered area twice the imaginary unit. -/
theorem whole_centered_nonzero :
    (Sample.build (fun vertex => (VertexTrace.concatenate triangle).indexed vertex)).centeredArea = (⟨0, 2⟩ :
      Data.Gaussian.Basic.Canonical) := by decide

/-- The retained endpoint polygon recovers the exact nonzero centered area of the whole triangle. -/
theorem retained_polygon_nonzero :
    (Sample.build (fun vertex => (JoinedCenteredArea.endpointPolygon triangle).indexed vertex)).centeredArea =
      (⟨0, 2⟩ : Data.Gaussian.Basic.Canonical) := by decide

end Test.Riemann.JoinedCenteredAreaTests
