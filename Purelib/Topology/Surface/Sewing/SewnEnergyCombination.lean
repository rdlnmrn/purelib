module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Riemann.Periods.BilinearCombination
public import Purelib.Data.Vector.Dependent
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Vector

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnConjugateSamples

open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples

@[expose] public section

/-! Homogeneous energy combinations use the retained sewn basis samples.
The actual boundary word and every source triangle remain in the readback. -/
namespace Purelib.Topology.Surface.Sewing.SewnEnergyCombination

open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Riemann.Periods.BilinearCombination (edgeListArea_combination edgeArea_combination sumFin_combination
  combination_bound)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate)

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeArea edgeListArea
  triangleWedgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)

variable {vertexCount faceCount genus : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {patch : SewingTree.SewnPatch faces} {localValues : Fin genus → Fin faceCount → PrimitiveSewing.PrimitiveValues 3}

/-- A dependent cache of original sewn scalar samples indexed by the finite basis family. -/
def EnergySurfaces (patch : SewingTree.SewnPatch faces) (localValues : Fin genus → Fin faceCount →
  PrimitiveSewing.PrimitiveValues 3) :=
  Data.Vector.DependentVector (fun basis => SewnPrimitiveSamples.CachedSample patch (localValues basis))

/-- Materialize one original sewn sample for each retained basis primitive family. -/
def EnergySurfaces.build (patch : SewingTree.SewnPatch faces) (localValues : Fin genus → Fin faceCount →
  PrimitiveSewing.PrimitiveValues 3) :
    EnergySurfaces patch localValues := DependentVector.ofFn fun basis => CachedSample.build patch
      (localValues basis)

/-- A dependent cache of conjugate/value pair samples owned by the original sewn basis-sample bank. -/
def EnergyPairs (surfaces : EnergySurfaces patch localValues) :=
  Data.Vector.DependentVector (fun first => Data.Vector.DependentVector (fun second =>
    SewnConjugateSamples.ConjugatePair (surfaces.get first) (surfaces.get second)))

namespace EnergyPairs

/-- Cache every original basis pair using the same retained scalar surfaces. -/
def build (surfaces : EnergySurfaces patch localValues) : SewnEnergyCombination.EnergyPairs
  surfaces :=
  DependentVector.ofFn fun first => DependentVector.ofFn fun second =>
    ConjugatePair.build (surfaces.get first) (surfaces.get second)

end EnergyPairs

/-- Form the anchored homogeneous energy primitive from the original basis samples and supplied coefficients.

The left component conjugates both coefficient and original centered reading; the right uses their direct weighted sum.
-/
def combinedValues (surfaces : EnergySurfaces patch localValues) (coefficients : Fin genus →
  Gaussian.Basic.Canonical)
    (vertex : Fin patch.cut.count) : PrimitivePoint :=
  ⟨sumFin (fun basis => Data.Gaussian.Basic.conj (coefficients basis) * Data.Gaussian.Basic.conj
    ((surfaces.get basis).sewn.values vertex - (surfaces.get basis).sewn.values patch.cut.anchor)),
    FiniteSum.Fin.sumFin (fun basis => coefficients basis *
      ((surfaces.get basis).sewn.values vertex - (surfaces.get basis).sewn.values patch.cut.anchor))⟩

/-- Evaluate the complete original cut-boundary area of the homogeneous energy primitive. -/
def energyBoundary (surfaces : EnergySurfaces patch localValues) (coefficients : Fin genus →
  Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  Stokes.edgeListArea (combinedValues surfaces coefficients) patch.cut.boundary

/-- Form the conjugate and direct weighted primitive coordinates on one original source face. -/
def localEnergyValues (localValues : Fin genus → Fin faceCount → PrimitiveSewing.PrimitiveValues 3)
    (coefficients : Fin genus → Gaussian.Basic.Canonical) (source : Fin faceCount) (vertex : Fin 3) : PrimitivePoint :=
  ⟨sumFin (fun basis => Data.Gaussian.Basic.conj (coefficients basis) * Data.Gaussian.Basic.conj (localValues
    basis source vertex)),
    FiniteSum.Fin.sumFin (fun basis => coefficients basis * localValues basis source vertex)⟩

/-- Evaluate the homogeneous energy wedge area of one original source triangle. -/
def localEnergy (localValues : Fin genus → Fin faceCount → PrimitiveSewing.PrimitiveValues 3)
    (coefficients : Fin genus → Gaussian.Basic.Canonical) (source : Fin faceCount) : Gaussian.Basic.Canonical :=
  Stokes.triangleWedgeArea (localEnergyValues localValues coefficients source 0)
    (localEnergyValues localValues coefficients source 1) (localEnergyValues
      localValues coefficients source 2)

/-- Pointwise equal original primitive readings give equal areas on the retained edge word. -/
private theorem edgeList_congr {count : Nat} {first last : Fin count → Stokes.PrimitivePoint}
    (equal : ∀ vertex, first vertex = last vertex) (word : List (Stokes.OrientedEdge count)) :
    Stokes.edgeListArea first word = Stokes.edgeListArea last word := by
  induction word with
  | nil => rfl
  | cons edge rest ih => exact congrArg₂ (· + ·) (congrArg₂ Stokes.edgeArea (equal edge.start) (equal edge.finish)) ih

/-- Read the original homogeneous energy boundary as the coefficient-weighted sum of cached conjugate/value pair areas.
-/
theorem energyBoundary_pairs (surfaces : EnergySurfaces patch localValues) (pairs :
  SewnEnergyCombination.EnergyPairs surfaces)
    (coefficients : Fin genus → Gaussian.Basic.Canonical) :
    energyBoundary surfaces coefficients =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients
        first) * coefficients second *
        ((pairs.get first).get second).boundaryArea)) := by
  unfold energyBoundary combinedValues
  rw [BilinearCombination.edgeListArea_combination]
  apply FiniteSum.Fin.sumFin_congr
  intro first
  apply FiniteSum.Fin.sumFin_congr
  intro second
  apply congrArg (Data.Gaussian.Basic.conj (coefficients first) * coefficients second * ·)
  exact (edgeList_congr (fun vertex => (((pairs.get first).get second).values_eq vertex).symm)
    _).trans
    ((pairs.get first).get second).boundaryArea_eq.symm

/-- Express the original primitive triangle wedge as its three signed edge-area terms. -/
private theorem triangle_edges (a b c : Stokes.PrimitivePoint) :
    Stokes.triangleWedgeArea a b c = Stokes.edgeArea a b + Stokes.edgeArea b c - Stokes.edgeArea a c := by
  simp only [Stokes.triangleWedgeArea, Stokes.edgeArea]
  ring1

/-- Expand one original local energy triangle into its complete conjugate/value basis-pair areas. -/
theorem localEnergy_pairs (localValues : Fin genus → Fin faceCount → PrimitiveSewing.PrimitiveValues 3)
    (coefficients : Fin genus → Gaussian.Basic.Canonical) (source : Fin faceCount) :
    localEnergy localValues coefficients source = FiniteSum.Fin.sumFin (fun first =>
      FiniteSum.Fin.sumFin (fun second =>
      Data.Gaussian.Basic.conj (coefficients first) * coefficients second * Stokes.triangleWedgeArea
        ⟨conj (localValues first source 0), localValues second source 0⟩
        ⟨conj (localValues first source 1), localValues second source 1⟩
        ⟨conj (localValues first source 2), localValues second source 2⟩)) := by
  unfold localEnergy
  rw [triangle_edges]
  unfold localEnergyValues
  rw [BilinearCombination.edgeArea_combination, BilinearCombination.edgeArea_combination,
    BilinearCombination.edgeArea_combination]
  rw [← FiniteSum.Fin.sumFin_add, ← FiniteSum.Fin.sumFin_sub]
  apply FiniteSum.Fin.sumFin_congr
  intro first
  rw [← FiniteSum.Fin.sumFin_add, ← FiniteSum.Fin.sumFin_sub]
  apply FiniteSum.Fin.sumFin_congr
  intro second
  rw [triangle_edges]
  ring1

/-- Pairwise requests control the actual energy boundary for every coefficient vector, without choosing a new refinement
threshold for that vector. -/
theorem energy_error_bound (surfaces : EnergySurfaces patch localValues) (pairs :
  SewnEnergyCombination.EnergyPairs surfaces)
    (coefficients : Fin genus → Gaussian.Basic.Canonical) {target : SewnPrimitiveFaces.Coordinate}
    (bounded : ∀ first second, Data.Gaussian.Norm.Basic.normSq (((pairs.get first).get second).boundaryArea -
      FiniteSum.Fin.sumFin (fun source => Stokes.triangleWedgeArea
        ⟨conj (localValues first source 0), localValues second source 0⟩
        ⟨conj (localValues first source 1), localValues second source 1⟩
        ⟨conj (localValues first source 2), localValues second source 2⟩)) ≤ target) :
    Data.Gaussian.Norm.Basic.normSq (energyBoundary surfaces coefficients - FiniteSum.Fin.sumFin
      (localEnergy localValues coefficients)) ≤
      (genus : SewnPrimitiveFaces.Coordinate)^2 * (FiniteSum.Fin.sumFin (fun basis => Data.Gaussian.Norm.Basic.normSq
        (coefficients
        basis)))^2 * target := by
  rw [energyBoundary_pairs surfaces pairs coefficients, FiniteSum.Fin.sumFin_congr
    (localEnergy_pairs localValues coefficients),
    BilinearCombination.sumFin_combination, ← FiniteSum.Fin.sumFin_sub]
  have difference := FiniteSum.Fin.sumFin_congr fun first => show
      FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
        ((pairs.get first).get second).boundaryArea) -
      FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
        FiniteSum.Fin.sumFin (fun source => Stokes.triangleWedgeArea
        ⟨conj (localValues first source 0), localValues second source 0⟩
        ⟨conj (localValues first source 1), localValues second source 1⟩
        ⟨conj (localValues first source 2), localValues second source 2⟩)) =
      FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
        (((pairs.get first).get second).boundaryArea -
        FiniteSum.Fin.sumFin (fun source => Stokes.triangleWedgeArea
          ⟨conj (localValues first source 0), localValues second source 0⟩
          ⟨conj (localValues first source 1), localValues second source 1⟩
          ⟨conj (localValues first source 2), localValues second source 2⟩))) by
    rw [← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro second
    ring1
  rw [difference]
  have bound := BilinearCombination.combination_bound (fun basis => Data.Gaussian.Basic.conj (coefficients basis))
    coefficients _ bounded
  rw [FiniteSum.Fin.sumFin_congr (fun basis => Gaussian.Norm.Basic.normSq_conj (coefficients basis))] at bound
  exact bound.trans_eq (by ring1)

end Purelib.Topology.Surface.Sewing.SewnEnergyCombination
