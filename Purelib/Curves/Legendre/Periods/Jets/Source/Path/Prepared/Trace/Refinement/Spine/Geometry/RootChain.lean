module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Geometry.RootChain
public import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Polynomial.Geometry.Grid.ClearGrid

/-! # Genuine signed roots on the SAME global refined child list

The actual whole geometry supplies every retained raw Trace and unchanged
following path. Explicit original initial/terminal Owner caches prevent
dependent endpoint indices from becoming data producers. The genuine
RootClosedWalk return closes that same original endpoint comparison.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathTrace.PreparedPath (TraceLineage)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Cache.Geometry

/-- Append SAME retained raw child roots through genuine complete-segment Owner transports.

The two supplied whole Owner caches retain their original index factories.
Each head binds first.finishOwner once: this original operation only casts
the SAME stored subdivision terminal Owner to its displayed finish. The
actual sourceOwner_eq, ownerAtStart_name, finishOwner_name and stored
finishOwnerEq give exact NAME transports, not an inferred root agreement.
The SAME following Geometry is then consumed with that actual middle cache
and unchanged supplied outer terminal Owner. No View, query, movement,
root/source preparation, Head split or geometry constructor is executed.
-/
def roots (diameter : Rational) (positive : 0 < diameter)
    {start finish : Canonical} {path : ClearPath (Paths.polynomial parameter) ambient start finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath path owner}
    (lineage : TraceLineage prepared)
    (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage)
    (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)) (factory : materialized = lineage.ownerPath)
    (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory)
    (initial : {value : Owner ((Paths.polynomial parameter).eval start) // value = owner})
    (terminal : {value : Owner ((Paths.polynomial parameter).eval finish) //
      value = PreparedPathGluing.finishOwner prepared}) :
    RootChain (parents diameter positive lineage centers materialized factory geometry)
      (ownerName initial.val) (ownerName terminal.val) :=
  TraceLineage.casesOn
    (motive := fun {start finish _path owner} prepared lineage =>
      (centers : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage) →
      (materialized : OwnerPath (Paths.polynomial parameter) start owner finish
        (PreparedPathGluing.finishOwner prepared)) → (factory : materialized = lineage.ownerPath) →
      (geometry : Cache.Geometry (count := count) diameter positive lineage centers materialized factory) →
      (initial : {value : Owner ((Paths.polynomial parameter).eval start) // value = owner}) →
      (terminal : {value : Owner ((Paths.polynomial parameter).eval finish) //
        value = PreparedPathGluing.finishOwner prepared}) →
        RootChain (parents diameter positive lineage centers materialized factory geometry)
          (ownerName initial.val) (ownerName terminal.val))
    lineage
    (fun _ _ _centers _materialized _factory _geometry initial terminal =>
      .nil (NamedEquivalent.transport rfl
        (congrArg (fun value => ownerName value) (initial.property.trans terminal.property.symm))
        (NamedEquivalent.refl (ownerName initial.val))))
    (fun {_start middle _finish segment _tail owner _within first middleOwner rest}
        budget fits finishOwnerEq remaining centers _materialized _factory geometry initial terminal =>
      let raw := Refinement.Cache.Geometry.roots (frame := frame) (basis := basis) (sheet := sheet) (count := count)
        diameter positive budget first.subdivision centers.1 fits geometry.1.val.front geometry.2.1.val
      let middleCache : {value : Owner ((Paths.polynomial parameter).eval middle) // value = middleOwner} :=
        ⟨first.finishOwner, finishOwnerEq.symm⟩
      have startName : ownerName (PreparedClearPathModels.ownerAtStart segment owner) = ownerName owner :=
        (PreparedBankRootChains.ownerName_eq_certificate
          (PreparedClearPathModels.ownerAtStart segment owner)).symm.trans
          ((PreparedBankRootChains.ownerAtStart_name (curve := Fibre.frameCurve frame) segment owner).trans
            (PreparedBankRootChains.ownerName_eq_certificate owner))
      have firstName : ownerName first.subdivision.sourceOwner = ownerName initial.val :=
        (congrArg (fun value => ownerName value) first.subdivision.sourceOwner_eq).trans
          (startName.trans (congrArg (fun value => ownerName value) initial.property).symm)
      have middleName : ownerName first.subdivision.terminalOwner = ownerName middleCache.val :=
        (PreparedBankRootChains.ownerName_eq_certificate first.subdivision.terminalOwner).symm.trans
          ((PreparedBankRootChains.finishOwner_name (curve := Fibre.frameCurve frame) first).trans
            (PreparedBankRootChains.ownerName_eq_certificate first.finishOwner))
      let headRoots := PreparedBankRootChains.RootChain.castNames firstName middleName raw
      have terminalNext : terminal.val = PreparedPathGluing.finishOwner rest :=
        terminal.property.trans
          (PreparedPathTrace.PreparedPath.castOwner_finishOwner finishOwnerEq rest)
      let following := roots diameter positive remaining centers.2
        geometry.1.val.following geometry.1.val.following_eq geometry.2.2
        middleCache ⟨terminal.val, terminalNext⟩
      RootChain.append (first := ownerName initial.val) (middle := ownerName middleCache.val)
        (last := ownerName terminal.val) headRoots following)
    centers materialized factory geometry initial terminal
termination_by structural lineage

end Cache.Geometry

namespace Geometry

/-- Read genuine signed roots from SAME retained whole geometry and explicit original endpoint Owner caches. -/
def roots
    {start finish : Canonical} {clearPath : ClearPath (Paths.polynomial parameter) ambient start finish}
    {owner : Owner ((Paths.polynomial parameter).eval start)} {prepared : PreparedPath clearPath owner}
    {lineage : TraceLineage prepared}
    {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) lineage}
    {materialized : OwnerPath (Paths.polynomial parameter) start owner finish
      (PreparedPathGluing.finishOwner prepared)} {factory : materialized = lineage.ownerPath}
    {diameter : Rational} {positive : 0 < diameter}
    (retained : Materialized.Geometry (count := count)
      diameter positive lineage inputCenters materialized factory)
    (initial : {value : Owner ((Paths.polynomial parameter).eval start) // value = owner})
    (terminal : {value : Owner ((Paths.polynomial parameter).eval finish) //
      value = PreparedPathGluing.finishOwner prepared}) :
    RootChain retained.parents (ownerName initial.val) (ownerName terminal.val) :=
  Cache.Geometry.roots (frame := frame) (basis := basis) (sheet := sheet) (count := count)
    diameter positive lineage retained.centers retained.path (retained.path_eq.trans factory) retained.cache
    initial terminal

/-- Close the SAME global child root chain using the original retained RootClosedWalk return certificate.

The GIVEN initial Owner is explicit data. The actual cached final Owner is
closed.traced.finishOwner, with its whole original finishOwner_eq factory.
Both caches enter the SAME whole geometric fold, and actual rootReturn
supplies the sole closing comparison. Neither geometric coordinate/sheet
closure nor a numerical integral equality substitutes for that evidence.
-/
def closedRoots
    {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
    (owner : Owner ((Paths.polynomial parameter).eval base)) (closed : RootClosedWalk grid base owner)
    {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) closed.traced.lineage}
    {materialized : OwnerPath (Paths.polynomial parameter) base owner base
      (PreparedPathGluing.finishOwner closed.traced.prepared)}
    {factory : materialized = closed.traced.lineage.ownerPath} {diameter : Rational} {positive : 0 < diameter}
    (retained : Materialized.Geometry (count := count)
      diameter positive closed.traced.lineage inputCenters materialized factory) :
    RootChain retained.parents (ownerName owner) (ownerName owner) :=
  let initial : {value : Owner ((Paths.polynomial parameter).eval base) // value = owner} := ⟨owner, rfl⟩
  let terminal : {value : Owner ((Paths.polynomial parameter).eval base) //
    value = PreparedPathGluing.finishOwner closed.traced.prepared} :=
    ⟨closed.traced.finishOwner, closed.traced.finishOwner_eq⟩
  let opened := roots retained initial terminal
  PreparedBankRootChains.RootChain.changeFinish
    (first := ownerName owner) (middle := ownerName closed.traced.finishOwner) (last := ownerName owner)
    opened closed.rootReturn

end Geometry

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
