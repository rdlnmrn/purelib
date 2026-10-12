module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Matrix.Basic

import Purelib.Data.Vector.Dependent
public import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Integration.Surface.Sewn.Selection.BilinearReadback
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.Bilinear.Errors
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
import Purelib.Integration.Surface.Sewn.Selection.ConjugateReadback
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Rat.Fraction
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Mathlib.Algebra.Group.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Vector

open Purelib.Integration.Surface.Sewn.Selection

open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces

open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.Bilinear

public section

/-! Cached conjugate areas on one retained source selection. Basis rows
share the selection mask; homogeneous combinations reuse the cached pair areas. -/

namespace Purelib.Topology.Surface.Sewing.SewnSelectedEnergy

open Purelib.Topology.Polygon.Stokes (OrientedTriangle edgeListArea triangleWedgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate)
open Purelib.Topology.Surface.Sewing.SewnEnergyCombination (EnergySurfaces EnergyPairs localEnergy localEnergy_pairs)
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample (FaceSelection)
open Purelib.Riemann.Periods.BilinearCombination (sumFin_combination combination_bound)

variable {vertexCount faceCount genus : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {patch : SewingTree.SewnPatch faces} {localValues : Fin genus → Fin faceCount → PrimitiveSewing.PrimitiveValues 3}

open Purelib.LinearAlgebra (Matrix)
open Purelib.LinearAlgebra.Matrix (matrixOfFn matrixOfFn_apply)

variable (surfaces : SewnEnergyCombination.EnergySurfaces patch localValues) (pairs : SewnEnergyCombination.EnergyPairs
  surfaces) (keep : Fin faceCount → Bool)

/-- A dependent bank of face selections sharing one original source mask across all basis surfaces. -/
@[expose] def EnergySelections := Data.Vector.DependentVector (fun basis : Fin genus => CachedSample.FaceSelection
  (surfaces.get basis) keep)

set_option genInjectivity false in
/-- Selected face banks with their cached pairwise conjugate areas.

Every matrix entry retains the area of the actual paired readings on the first basis row's selected cut triangles. -/
structure SelectedEnergySamples where
  /-- Retained face selections for all original basis surfaces under the common mask. -/ selections :
    EnergySelections surfaces keep
  /-- Cached Gaussian matrix of selected pairwise areas. -/ areas : LinearAlgebra.Matrix
    Gaussian.Basic.Canonical genus
  /-- Each cached entry reads the original pair's values on the retained selected triangle occurrences. -/ areas_eq : ∀
    first second, areas first second = Stokes.edgeListArea ((pairs.get first).get second).values
    ((selections.get first).triangles.flatMap OrientedTriangle.boundary)

constructive_injectivity SelectedEnergySamples

namespace SelectedEnergySamples

/-- Build the shared-mask selections and cache every pairwise selected area. -/
@[expose] def build : SelectedEnergySamples surfaces pairs keep :=
  let selections : EnergySelections surfaces keep :=
    DependentVector.ofFn fun basis => FaceSelection.build (surfaces.get basis) keep
  ⟨selections, LinearAlgebra.Matrix.matrixOfFn (fun first second => Stokes.edgeListArea
    ((pairs.get first).get second).values
    ((selections.get first).triangles.flatMap OrientedTriangle.boundary)), fun first second =>
      LinearAlgebra.Matrix.matrixOfFn_apply _ first second⟩

variable {surfaces pairs keep}

/-- Contract the cached area matrix against conjugate-left and ordinary-right coefficients. -/
@[expose] def energy (samples : SelectedEnergySamples surfaces pairs keep) (coefficients : Fin genus
  → Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin fun first => FiniteSum.Fin.sumFin fun second => Data.Gaussian.Basic.conj (coefficients first)
    * coefficients second * samples.areas first second

/-- Masked local energy expands into the same mask applied to every pairwise area term. -/
private theorem masked_localEnergy_pairs (coefficients : Fin genus → Gaussian.Basic.Canonical) (source : Fin faceCount)
  :
    (if keep source then SewnEnergyCombination.localEnergy localValues coefficients source else 0) =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients
        first) * coefficients second *
        (if keep source then Stokes.triangleWedgeArea
          ⟨conj (localValues first source 0), localValues second source 0⟩
          ⟨conj (localValues first source 1), localValues second source 1⟩
          ⟨conj (localValues first source 2), localValues second source 2⟩ else 0))) := by
  cases keep source with
  | true => exact SewnEnergyCombination.localEnergy_pairs localValues coefficients source
  | false =>
      change (0 : Gaussian.Basic.Canonical) = FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second =>
        Data.Gaussian.Basic.conj (coefficients first) * coefficients second * 0))
      rw [FiniteSum.Fin.sumFin_congr (fun first => (FiniteSum.Fin.sumFin_congr (fun second => mul_zero _)).trans
        FiniteSum.Fin.sumFin_zero),
        FiniteSum.Fin.sumFin_zero]

/-- Pairwise bounds pay the selected energy without discarding an omitted triangle's potentially negative approximation
error. -/
theorem error_bound (samples : SelectedEnergySamples surfaces pairs keep)
    (coefficients : Fin genus → Gaussian.Basic.Canonical) {target : SewnPrimitiveFaces.Coordinate}
    (bounded : ∀ first second, Data.Gaussian.Norm.Basic.normSq (samples.areas first second -
      FiniteSum.Fin.sumFin (fun source => if keep source then Stokes.triangleWedgeArea
        ⟨conj (localValues first source 0), localValues second source 0⟩
        ⟨conj (localValues first source 1), localValues second source 1⟩
        ⟨conj (localValues first source 2), localValues second source 2⟩ else 0)) ≤ target) :
    Data.Gaussian.Norm.Basic.normSq (samples.energy coefficients - FiniteSum.Fin.sumFin (fun source => if keep source
      then
      SewnEnergyCombination.localEnergy localValues coefficients source else 0)) ≤
      (genus : SewnPrimitiveFaces.Coordinate)^2 * (FiniteSum.Fin.sumFin (fun basis => Data.Gaussian.Norm.Basic.normSq
        (coefficients
        basis)))^2 * target := by
  unfold energy
  rw [FiniteSum.Fin.sumFin_congr (fun source => masked_localEnergy_pairs coefficients source),
    BilinearCombination.sumFin_combination, ← FiniteSum.Fin.sumFin_sub]
  have difference := FiniteSum.Fin.sumFin_congr fun first => show
      FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
        samples.areas first second) -
      FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
        FiniteSum.Fin.sumFin (fun source => if keep source then Stokes.triangleWedgeArea
        ⟨conj (localValues first source 0), localValues second source 0⟩
        ⟨conj (localValues first source 1), localValues second source 1⟩
        ⟨conj (localValues first source 2), localValues second source 2⟩ else 0)) =
      FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second *
        (samples.areas first second -
        FiniteSum.Fin.sumFin (fun source => if keep source then Stokes.triangleWedgeArea
          ⟨conj (localValues first source 0), localValues second source 0⟩
          ⟨conj (localValues first source 1), localValues second source 1⟩
          ⟨conj (localValues first source 2), localValues second source 2⟩ else 0))) by
    rw [← FiniteSum.Fin.sumFin_sub]
    apply FiniteSum.Fin.sumFin_congr
    intro second
    ring1
  rw [difference]
  have bound := BilinearCombination.combination_bound (fun basis => Data.Gaussian.Basic.conj (coefficients basis))
    coefficients _ bounded
  rw [FiniteSum.Fin.sumFin_congr (fun basis => Gaussian.Norm.Basic.normSq_conj (coefficients basis))] at bound
  exact bound.trans_eq (by ring1)

/-- A different retained scalar sample on the same cut patch selects the same cut triangles. This readback does not
recompute the pair areas. -/
theorem area_readback (samples : SelectedEnergySamples surfaces pairs keep) (first second : Fin
  genus)
    {otherLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3} {other : SewnPrimitiveSamples.CachedSample patch
      otherLocal}
    (selected : CachedSample.FaceSelection other keep) :
    samples.areas first second = Stokes.edgeListArea ((pairs.get first).get second).values
      (selected.triangles.flatMap OrientedTriangle.boundary) := by
  rw [samples.areas_eq, BilinearReadback.paired_area_eq_masked (samples.selections.get first),
    BilinearReadback.paired_area_eq_masked selected]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  rw [Errors.traceAt_source (surfaces.get first) other position]

end SelectedEnergySamples
end Purelib.Topology.Surface.Sewing.SewnSelectedEnergy
