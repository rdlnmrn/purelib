module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry.Sources.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

/-! # The SAME six-channel bank as an actual global lifted source path

The retained global child list, cover and centered chain determine the
geometric path. The GIVEN whole source bank supplies all original source
cells. Concatenation transports no query, root, source model or observation
owner and derives the exact six literal model-list readbacks internally.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
variable {ambient : Purelib.Geometry.Rational.Box}

namespace Cache.Geometry.Sources

/-- Concatenate the SAME supplied complete-segment source products along the SAME global child covering spine. -/
@[expose] def preparations (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) → (factory : materialized = lineage.ownerPath) →
    (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory) →
    Sources (count := count) (floor := floor) (targets := targets)
      diameter positive lineage centers materialized factory geometry →
      PreparedParents (Geometry.covered diameter positive lineage centers materialized factory geometry) floor targets
  | _, _, _, _, _, .nil _ _, _, _, _, _, _ => PUnit.unit
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      centers, _materialized, _factory, geometry, sourceBank =>
      PreparedParents.append
        (Refinement.Cache.Geometry.covered diameter positive budget first.subdivision centers.1 fits
          geometry.1.val.front geometry.2.1.val)
        (Geometry.covered diameter positive remaining centers.2
          geometry.1.val.following geometry.1.val.following_eq geometry.2.2)
        (Refinement.Cache.Geometry.Sources.preparations (count := count) (floor := floor) (targets := targets)
          diameter positive budget first.subdivision centers.1 fits geometry.1.val.front geometry.2.1.val sourceBank.1)
        (preparations diameter positive remaining centers.2
          geometry.1.val.following geometry.1.val.following_eq geometry.2.2 sourceBank.2)
termination_by structural _ _ _ _ _ lineage _ _ _ _ _ => lineage

/-- The actual global preparation product reads exactly the supplied whole bank's six literal source-cell lists. -/
theorem cells_preparations (channel : Fin 6) (diameter : Rational) (positive : 0 < diameter) :
    {start finish : Canonical} → {path : ClearPath (Paths.polynomial parameter) ambient start finish} →
    {owner : Owner ((Paths.polynomial parameter).eval start)} → {prepared : PreparedPath path owner} →
    (lineage : TraceLineage prepared) →
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) → (factory : materialized = lineage.ownerPath) →
    (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory) →
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets)
      diameter positive lineage centers materialized factory geometry) →
      PreparedParents.cells
        (covered := Geometry.covered diameter positive lineage centers materialized factory geometry)
        (preparations diameter positive lineage centers materialized factory geometry sourceBank) channel =
      cells channel diameter positive lineage centers materialized factory geometry sourceBank
  | _, _, _, _, _, .nil _ _, _, _, _, _, _ => PreparedParents.cells_nil channel
  | _, _, _, _, _, .cons (first := first) budget fits _finishOwnerEq remaining,
      centers, _materialized, _factory, geometry, sourceBank =>
      (PreparedParents.cells_append channel
        (Refinement.Cache.Geometry.covered diameter positive budget first.subdivision centers.1 fits
          geometry.1.val.front geometry.2.1.val)
        (Geometry.covered diameter positive remaining centers.2
          geometry.1.val.following geometry.1.val.following_eq geometry.2.2)
        (Refinement.Cache.Geometry.Sources.preparations (count := count) (floor := floor) (targets := targets)
          diameter positive budget first.subdivision centers.1 fits geometry.1.val.front geometry.2.1.val sourceBank.1)
        (preparations diameter positive remaining centers.2
          geometry.1.val.following geometry.1.val.following_eq geometry.2.2 sourceBank.2)).trans
          (congrArg₂ List.append
            (Refinement.Cache.Geometry.Sources.cells_preparations (count := count) (floor := floor) (targets := targets)
              channel diameter positive budget first.subdivision centers.1 fits
              geometry.1.val.front geometry.2.1.val sourceBank.1)
            (cells_preparations channel diameter positive remaining centers.2
              geometry.1.val.following geometry.1.val.following_eq geometry.2.2 sourceBank.2))
termination_by structural _ _ _ _ _ lineage _ _ _ _ _ => lineage

end Cache.Geometry.Sources

variable {diameter : Rational} {positive : 0 < diameter}
variable {start finish : Canonical} {clearPath : ClearPath (Paths.polynomial parameter) ambient start finish}
variable {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath clearPath owner}
variable {lineage : TraceLineage prepared}
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) start owner finish
  (PreparedPathGluing.finishOwner prepared)} {factory : materialized = lineage.ownerPath}
variable (retained : Materialized.Geometry (count := count)
  diameter positive lineage inputCenters materialized factory)

namespace Geometry.Sources

/-- Read the actual concatenated whole source preparation on the SAME retained global child cover. -/
@[expose] def preparations
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained) :
    PreparedParents retained.covered floor targets :=
  Cache.Geometry.Sources.preparations (count := count) (floor := floor) (targets := targets)
    diameter positive lineage retained.centers retained.path (retained.path_eq.trans factory) retained.cache sourceBank

/-- The global covered preparation retains precisely the supplied whole bank's original ordered channel cells. -/
theorem cells_preparations
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained) (channel : Fin 6) :
    PreparedParents.cells (covered := retained.covered) (preparations retained sourceBank) channel =
      cells retained sourceBank channel :=
  Cache.Geometry.Sources.cells_preparations (count := count) (floor := floor) (targets := targets)
    channel diameter positive lineage retained.centers retained.path (retained.path_eq.trans factory)
      retained.cache sourceBank

/-- Join the SAME supplied six-channel source cells on the actual global refined chain.

The GIVEN actual chain is consumed as data, so a pre-target childChain is
not rebuilt. Its path and original cover index this source-chain assembly.
No RootOwner evidence is reconstructed from model or coordinate equalities.
-/
@[expose] def sources
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (childChain : CenteredPathChain retained.parents (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩)) :
    Path parameter childChain.path :=
  PreparedParents.sources retained.covered (preparations retained sourceBank) childChain

/-- The actual global lifted source path retains the SAME whole bank's literal six model lists. -/
theorem cells_sources
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (childChain : CenteredPathChain retained.parents (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩))
    (channel : Fin 6) :
    cells retained sourceBank channel = (sources retained sourceBank childChain).cells channel :=
  (cells_preparations retained sourceBank channel).symm.trans
    (PreparedParents.cells_eq_sources channel retained.covered (preparations retained sourceBank) childChain)

/-- Each supplied whole-bank polynomial model is the model on the SAME actual global source path and literal cells. -/
theorem model_eq_sources
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (childChain : CenteredPathChain retained.parents (start := ⟨start, sheet⟩) (finish := ⟨finish, sheet⟩))
    (channel : Fin 6) :
    model retained sourceBank channel = PathModel.mk ((sources retained sourceBank childChain).cells channel) :=
  congrArg PathModel.mk (cells_sources retained sourceBank childChain channel)

end Geometry.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
