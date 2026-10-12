module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut.PrimitiveJumps

@[expose] public section

/-!
# Readback of the actual endpoint-jump defects

The right component of a cached cut-pair defect is the negative sum of its
two oriented edge increments. This exact identity transfers the exposed-pair
bound to the defect retained by the existing global boundary decomposition.
-/

namespace Purelib.Topology.Surface.Boundary.BoundaryDefectReadings

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair (Sample)

open Purelib.Data.Gaussian.Basic.Canonical

variable {source target : Nat} {labels : Fin source → Fin target}
  {primitive : Fin source → Stokes.PrimitivePoint}

/-- The cached right defect has the squared norm of the sum of the two oriented edge increments. -/
theorem defect_right_normSq (sample : ProjectedEdgePair.Sample (labels := labels) primitive) (values : Fin source →
  Gaussian.Basic.Canonical)
    (values_eq : ∀ vertex, (primitive vertex).right = values vertex) :
    Gaussian.Norm.Basic.normSq sample.defect.right = Gaussian.Norm.Basic.normSq
      ((values sample.pair.first.finish - values sample.pair.first.start) +
        (values sample.pair.second.finish - values sample.pair.second.start)) := by
  rw [sample.defect_eq, sample.finishJump_eq, sample.startJump_eq]
  simp only [PrimitivePoint.sub, values_eq]
  have equal (a b c d : Gaussian.Basic.Canonical) : (c - b) - (d - a) = -((b - a) + (d - c)) := by ring1
  rw [equal, Gaussian.Norm.Basic.normSq_neg]

end Purelib.Topology.Surface.Boundary.BoundaryDefectReadings
