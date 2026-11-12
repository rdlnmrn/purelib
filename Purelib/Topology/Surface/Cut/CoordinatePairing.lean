module
import Purelib.Algebra.FiniteSum.Gaussian
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
public import Purelib.Integration.Energy.Polygon

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Word.Pairing
public import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Cast

open Purelib.Integration.Energy

public section

/-!
# Area-level Stokes identification for cut coordinates

The ordered A/B words are integer combinations of the retained cut generators
(`Pair.CutCoordinates.value_eq`). This module is the missing area-level
bridge: the Gaussian area pairing of two such combinations is exactly the
integer wedge contraction of their coefficient vectors against the energy
primitives of the generator values. That is the finite identity that carries
the ordered A/B pairing to the cut-word crossing/period layers already
controlled by `FiniteCutIntersection` and `GridNormalFormPeriodArea`.
-/

namespace Purelib.Topology.Surface.Cut.CoordinatePairing

open Purelib

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_succ)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)

/-- The conjugate/value energy pair turns the Gaussian area form into the ordered primitive edge determinant. -/
theorem edgeArea_energyPrimitivePoint (first last : Canonical) :
    edgeArea (Polygon.energyPrimitivePoint first)
      (Polygon.energyPrimitivePoint last) =
      Integration.Path.BoundaryRibbon.area first last := by
  unfold edgeArea Polygon.energyPrimitivePoint
    Integration.Path.BoundaryRibbon.area
  ring1

open Purelib
/-- An integer linear combination of energy points is the energy point of the integer combination of the underlying
Gaussian values. -/
theorem linear_energyPrimitivePoint {count : Nat} (coefficients : Fin count → Int)
    (values : Fin count → Canonical) :
    Word.Pairing.linear coefficients
        (fun index => Polygon.energyPrimitivePoint (values index)) =
      Polygon.energyPrimitivePoint
        (WordCoordinates.combine coefficients values) := by
  change PrimitivePoint.mk
      (sumFin (fun index => (coefficients index : Canonical) *
        Data.Gaussian.Basic.conj (values index)))
      (sumFin (fun index => (coefficients index : Canonical) * values index))
        =
    PrimitivePoint.mk
      (Data.Gaussian.Basic.conj (sumFin (fun index => (coefficients index :
        Canonical) * values index)))
      (sumFin (fun index => (coefficients index : Canonical) * values index))
  rw [Algebra.FiniteSum.Gaussian.conj_sumFin]
  congr 1
  apply sumFin_congr
  intro index
  rw [Data.Gaussian.Basic.conj_mul, Data.Gaussian.Cast.conj_intCast]

/-- The area-level Stokes identification: the Gaussian area pairing of two integer combinations of one generator-value
family equals the integer wedge contraction with the energy primitives. -/
theorem area_combine_eq_contract {count : Nat} (first last : Fin count → Int)
    (values : Fin count → Canonical) :
    Integration.Path.BoundaryRibbon.area (WordCoordinates.combine first
      values)
        (WordCoordinates.combine last values) =
      Word.Pairing.contract (fun row column => first row * last column - last row * first column)
        (fun index => Polygon.energyPrimitivePoint (values index)) := by
  rw [← edgeArea_energyPrimitivePoint, ←
    linear_energyPrimitivePoint first,
    ← linear_energyPrimitivePoint last, ←
      Word.Pairing.contract_wedge]

end Purelib.Topology.Surface.Cut.CoordinatePairing
