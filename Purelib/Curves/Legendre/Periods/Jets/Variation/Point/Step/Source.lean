module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point
import Purelib.Riemann.RootContinuation.RootContinuationCongruence
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Comparison
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field

/-! # Original source agreement for a retained zero-increment Step

The existing general common-source comparison consumes the actual stored
Step owner and its source-box refinement. Only the scalar radicand index
is transported; the Frame, curve, Point and Step remain their own owners.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_initial_box)

/-- A retained zero-increment Step agrees with its actual original source root.

Only its scalar radicand parameter is transported. The original owner is
compared with the SAME retained target owner through their source-box
refinements. The existing common-source/intersection construction supplies
operational agreement; neither the Step nor either owner is rebuilt.
-/
def sourceEquivalent {parameter point : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {source : ContinuedNeighborhood.Point patch point} (step : Step source 0) :
    NamedEquivalent step.root.value.name source.certificate.value.name := by
  let sameParameter : (Paths.polynomial (parameter + 0)).eval point =
      (Paths.polynomial parameter).eval point :=
    congrArg (fun value : Canonical => (Paths.polynomial value).eval point) (Basic.add_zero parameter)
  let targetOwner := castOwnerParameter sameParameter step.owner
  have boxEq := castOwnerParameter_initial_box sameParameter step.owner
  have targetRefines : targetOwner.track.initial.box.Refines source.owner.track.initial.box :=
    Eq.mpr (congrArg (fun box => box.Refines source.owner.track.initial.box) boxEq) step.refines
  have small : Canonical.normSq
      ((Paths.polynomial parameter).eval point - (Paths.polynomial parameter).eval point) <
        source.owner.track.initial.clearance.bound :=
    ((congrArg Canonical.normSq (Basic.sub_self ((Paths.polynomial parameter).eval point))).trans
      Canonical.normSq_zero).trans_lt source.owner.track.initial.clearance.positive
  let compared := RootContinuationCongruence.retainedOwnersEquivalent source.owner.parameterNonzero
    source.owner source.owner (NamedEquivalent.refl (ownerRootName source.owner.parameterNonzero source.owner))
    small small targetOwner source.owner targetRefines (Geometry.Rational.Box.refines_refl _)
  have targetName : ownerRootName targetOwner.parameterNonzero targetOwner = step.root.value.name :=
    (SquareRootTrackEquivalence.ownerRootName_castOwnerParameter sameParameter step.owner).trans
      (congrArg (fun root : CertifiedSquareRoot.Certificate
          ((Paths.polynomial (parameter + 0)).eval point) => root.value.name) step.root_eq).symm
  have sourceName : ownerRootName source.owner.parameterNonzero source.owner =
      source.certificate.value.name := rfl
  exact NamedEquivalent.transport targetName sourceName compared

/-- Reindex the SAME actual Step along exact whole source-Point and nominal count/patch/point identities.

All four equalities concern the original retained source data. Equality
elimination transports only indices; the target Owner, cached certificate,
refinement and original admission stay in the same completed Step.
-/
def castSource {parameter increment firstPoint lastPoint : Canonical} {firstCount lastCount : Nat}
    {firstPatch : ContinuedNeighborhood (Paths.polynomial parameter) firstCount}
    {lastPatch : ContinuedNeighborhood (Paths.polynomial parameter) lastCount}
    {firstSource : ContinuedNeighborhood.Point firstPatch firstPoint}
    {lastSource : ContinuedNeighborhood.Point lastPatch lastPoint}
    (sameCount : firstCount = lastCount) (samePatch : HEq firstPatch lastPatch)
    (samePoint : firstPoint = lastPoint) (sameSource : HEq firstSource lastSource)
    (step : Step firstSource increment) : Step lastSource increment := by
  cases sameCount
  cases (eq_of_heq samePatch)
  cases samePoint
  cases (eq_of_heq sameSource)
  exact step

/-- Exact source transport retains the entire original completed Step heterogeneously. -/
theorem castSource_heq {parameter increment firstPoint lastPoint : Canonical} {firstCount lastCount : Nat}
    {firstPatch : ContinuedNeighborhood (Paths.polynomial parameter) firstCount}
    {lastPatch : ContinuedNeighborhood (Paths.polynomial parameter) lastCount}
    {firstSource : ContinuedNeighborhood.Point firstPatch firstPoint}
    {lastSource : ContinuedNeighborhood.Point lastPatch lastPoint}
    (sameCount : firstCount = lastCount) (samePatch : HEq firstPatch lastPatch)
    (samePoint : firstPoint = lastPoint) (sameSource : HEq firstSource lastSource)
    (step : Step firstSource increment) :
    HEq (castSource sameCount samePatch samePoint sameSource step) step := by
  cases sameCount
  cases (eq_of_heq samePatch)
  cases samePoint
  cases (eq_of_heq sameSource)
  rfl

/-- The original target root name is unchanged by exact whole-source transport. -/
theorem castSource_name {parameter increment firstPoint lastPoint : Canonical} {firstCount lastCount : Nat}
    {firstPatch : ContinuedNeighborhood (Paths.polynomial parameter) firstCount}
    {lastPatch : ContinuedNeighborhood (Paths.polynomial parameter) lastCount}
    {firstSource : ContinuedNeighborhood.Point firstPatch firstPoint}
    {lastSource : ContinuedNeighborhood.Point lastPatch lastPoint}
    (sameCount : firstCount = lastCount) (samePatch : HEq firstPatch lastPatch)
    (samePoint : firstPoint = lastPoint) (sameSource : HEq firstSource lastSource)
    (step : Step firstSource increment) :
    (castSource sameCount samePatch samePoint sameSource step).root.value.name = step.root.value.name := by
  cases sameCount
  cases (eq_of_heq samePatch)
  cases samePoint
  cases (eq_of_heq sameSource)
  rfl

/-- Equal increment indices compare two actual Steps on the SAME retained source Point.

Only the scalar increment equality is eliminated. The original source
Point supplies its reflexive root relation, then the existing common-source
Step comparison consumes both unchanged target Owners and admissions.
No Step, source observation or preparation is constructed here.
-/
def equivalent_of_increment_eq {parameter point firstIncrement lastIncrement : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {source : ContinuedNeighborhood.Point patch point}
    (same : firstIncrement = lastIncrement)
    (first : Step source firstIncrement) (last : Step source lastIncrement) :
    NamedEquivalent first.root.value.name last.root.value.name := by
  cases same
  exact first.equivalent_of_source_eq last rfl (NamedEquivalent.refl source.certificate.value.name)

/-- A supplied exact zero-increment index derives agreement with the SAME original source root.

Only the scalar increment equality is eliminated before the original
sourceEquivalent operation is consumed. The supplied completed Step and
both original root Owners remain unchanged; no Frame equality is used.
-/
def sourceEquivalent_of_zero {parameter increment point : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {source : ContinuedNeighborhood.Point patch point} (step : Step source increment) (zero : increment = 0) :
    NamedEquivalent step.root.value.name source.certificate.value.name := by
  cases zero
  exact step.sourceEquivalent

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step

end
