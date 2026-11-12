module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Endpoint
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial
public import Purelib.Riemann.Branches.PreparedSheetContinuation.CachedSource.Observation
public import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Tactic.Ring

/-! # Retained factor-channel agreement at an actual prepared spatial entry

The original factor query at physical segment parameter zero agrees with
the independent original quarter Reading. The existing Source attachment
then supplies its genuine continuation Owner. Exact displayed-start index
transport and the actual CachedSource reconditioning compare the same full
product with the first prepared Certificate, preserving all original caches.
No target advance or Covered.finishOwner equivalence is an input or output.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (StepRequest CachedSource)
open Purelib.Riemann.Paths.PreparedClearPathModels (ownerAtStart zeroEndpoint)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor)
  (Spatial.coordinate site parameter 2 quarter positive first) finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {prepared : Division.Prepared source.lift.value}

/-- The exact original attached Owner, transported only to this physical segment's zero-parameter index. -/
@[expose] def InitialOwner (attachment : Spatial.Source source prepared) :=
  ownerAtStart segment attachment.attached.owner

/-- The original parameter-zero factor query agrees with the identical original quarter source Lift.value. -/
def agrees_source (reading : Reading completed 0 (by decide +kernel)) :
    NamedEquivalent reading.values.value.name source.lift.value.name := by
  have point_eq : segment.pointAt 0 =
      (Parameter.sourcePoint site parameter (Waist.direction quarter first)).base := by
    change segment.pointAt 0 = Spatial.coordinate site parameter 2 quarter positive first
    exact segment.pointAt_zero
  have paid : (first - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7 := by
    rewrite [show (first - first) ^ 2 = 0 by ring1]
    exact Approximation.Rational.Geometric.Basic.quarterRadius_nonneg
      (by decide +kernel : (0 : Fraction.Rational) ≤ 1) 7
  exact reading.agrees_target source point_eq paid

/-- Compose original factor-source agreement with a supplied nominal source Owner's operational relation.

The source Owner and its complete comparison remain inputs. Only the
original start-index cast is transported; no attachment, certificate or
factor observation is acquired by this operation.
-/
def agrees_owner (reading : Reading completed 0 (by decide +kernel))
    (owner : Owner ((Paths.polynomial parameter).eval
      (Spatial.coordinate site parameter 2 quarter positive first)))
    (agreement : NamedEquivalent source.lift.value.name (ownerRootName owner.parameterNonzero owner)) :
    NamedEquivalent reading.values.value.name
      (ownerRootName (ownerAtStart segment owner).parameterNonzero (ownerAtStart segment owner)) := by
  have original : ownerRootName (ownerAtStart segment owner).parameterNonzero (ownerAtStart segment owner) =
      ownerRootName owner.parameterNonzero owner := by
    unfold ownerAtStart
    exact SquareRootTrackEquivalence.ownerRootName_castOwnerParameter _ _
  exact NamedEquivalent.transport rfl original.symm (reading.agrees_source.trans agreement)

/-- The actual original attachment and exact index transport derive the initial factor-to-continuation agreement.

The independent full product, original source Lift, existing preparation and
already completed attachment remain retained inputs. Original source and
factor comparisons are composed, without another source attachment or root
certificate acquisition.
-/
def agrees_initial (reading : Reading completed 0 (by decide +kernel))
    (attachment : Spatial.Source source prepared) :
    NamedEquivalent reading.values.value.name
      ((InitialOwner (segment := segment) attachment).certificate
        (InitialOwner (segment := segment) attachment).parameterNonzero).value.name := by
  have original : ownerRootName (InitialOwner (segment := segment) attachment).parameterNonzero
      (InitialOwner (segment := segment) attachment) =
      ownerRootName attachment.attached.owner.parameterNonzero attachment.attached.owner := by
    unfold InitialOwner ownerAtStart
    exact SquareRootTrackEquivalence.ownerRootName_castOwnerParameter _ _
  exact NamedEquivalent.transport rfl original.symm (reading.agrees_source.trans attachment.agrees)

/-- Compare actual retained readings after the first spatial source's exact cached full-cubic preparation.

The original CachedSource contains the actual prepared Owner for the supplied
request. Its original reconditioning comparison consumes the internally
constructed entry agreement. Both original finite reading requests and their
paid operational comparison retain the supplied prepared Certificate cache;
no advanced target Owner or finished covered path is identified here.
-/
def compare_prepared (reading : Reading completed 0 (by decide +kernel))
    (attachment : Spatial.Source source prepared) (request : StepRequest)
    (cached : CachedSource segment zeroEndpoint (InitialOwner (segment := segment) attachment) request)
    (root : CertifiedSquareRoot.Certificate ((Paths.polynomial parameter).eval
      (segment.pointAt zeroEndpoint.parameter)))
    (root_eq : root = cached.preparedOwner.certificate cached.preparedOwner.parameterNonzero)
    (accuracy : Fraction.Rational) (accuracyPositive : 0 < accuracy) :
    CachedSource.PaidComparison cached root root_eq reading.values.value accuracy :=
  cached.compare root root_eq reading.values.value (reading.agrees_initial attachment) accuracy accuracyPositive

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading
