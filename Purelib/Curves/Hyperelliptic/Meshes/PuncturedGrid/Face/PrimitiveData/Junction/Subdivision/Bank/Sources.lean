module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Junction.Subdivision.Bank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Connections
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.Paths.OwnerTraceReadings

/-! # Initial common-domain banks from retained continued Points

The source Point and its face Entry are read from the complete original
TracedPoint cache. Two independently prepared primitive domains can use
that same face sheet without identifying their anchors, offsets or old
readings. A retained connection also supplies the literal Point-side tail
for the new initial join; no old Point, connection or tail is reacquired.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction.Subdivision

namespace Bank

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin ownerApproximation)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {face : RegularFace bank} {models : FaceModels frames face}
variable {sheet : Fin 2} {first last : Canonical} {inside : face.cell.box.Contains first}
variable {count : Nat} {targetFrame : OwnerFrame (curve.polynomial.eval first)}
variable (cached : Entry.TracedPoint models sheet first inside count targetFrame)

/-- Extract the whole retained Point, its actual neighborhood and its original local containment.

This is only the original PointData tuple packing. In particular it does
not execute Point.acquire or reconstruct the Point from its Owner.
-/
abbrev pointData : Entry.PointData (curve := curve) first :=
  ⟨count, cached.neighborhood.patch, cached.sample, ⟨(), cached.neighborhood.center_inside⟩⟩

/-- Use the original Entry with its proved old-sheet spelling and unchanged reachability witness. -/
abbrev sourceEntry : Entry models first (pointData cached).sample.owner :=
  cached.entry.withSheet sheet cached.entry_sheet

/-- PointData reads the SAME whole original Point, including its seed and root Owner. -/
theorem pointData_sample : (pointData cached).sample = cached.sample := by rfl

/-- The extracted Entry is whole-value equal to the original retained Entry. -/
theorem sourceEntry_eq : sourceEntry cached = cached.entry :=
  cached.entry.withSheet_eq sheet cached.entry_sheet

section Domains

variable {leftDomain rightDomain : PeriodDomain models sheet}
variable {differential : Differential genus} {leftIndex rightIndex : Nat}
variable {leftData : DomainPrimitives leftDomain differential leftIndex}
variable {rightData : DomainPrimitives rightDomain differential rightIndex}
variable {ambient : Box} {source : ClearSegment curve.polynomial ambient first last}
variable {leftSize rightSize : Nat} {leftPoints : Fin leftSize → Canonical} {rightPoints : Fin rightSize → Canonical}
variable {leftOld : PointReadings leftData.anchors leftData.offsets leftPoints}
variable {rightOld : PointReadings rightData.anchors rightData.offsets rightPoints}
variable {leftFirst leftLast : Fin leftSize} {rightFirst rightLast : Fin rightSize}
variable {leftFirst_eq : leftPoints leftFirst = first} {leftLast_eq : leftPoints leftLast = last}
variable {rightFirst_eq : rightPoints rightFirst = first} {rightLast_eq : rightPoints rightLast = last}
variable (retained : Subdivision leftData rightData source leftOld rightOld leftFirst leftLast rightFirst rightLast
  leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq)

/-- The exact original bank acquisition on the two SAME supplied source-Point roles.

Both primitive domains and reading banks remain separate nominal inputs.
The supplied join here is an index of the result type; the two producers
below construct it from actual retained data rather than ask for it.
-/
abbrev AtPoint (joined : OwnerJoin cached.sample.owner cached.sample.owner) (request : AccuracyRequest) :=
  Acquisition (leftPoint := pointData cached) (rightPoint := pointData cached)
    (leftEntry := sourceEntry cached) (rightEntry := sourceEntry cached)
    (sourceJoin := joined) (retained := retained) request

/-- A source bank retains the whole old Point cache and one genuinely new reflexive join.

The join has its own actual tail/comparison work. Its observation payment
is not inferred from the later primitive comparison's finite payment.
-/
abbrev TracedSource (request : AccuracyRequest) :=
  {value : Entry.TracedPoint models sheet first inside count targetFrame // value = cached} ×
  (Σ joined : {value : OwnerJoin cached.sample.owner cached.sample.owner //
      value = OwnerJoin.reflexive cached.sample.owner},
    {value : AtPoint cached retained joined.val request //
      value = acquire (leftPoint := pointData cached) (rightPoint := pointData cached)
        (leftEntry := sourceEntry cached) (rightEntry := sourceEntry cached)
        (sourceJoin := joined.val) (retained := retained) request})

/-- Construct the actual initial source join and consume the retained Point/Entry in the common-domain bank.

No Point or bare Entry is acquired here. The existing bank acquires its
two required complete face-acquisition caches and new common child data;
these are genuine additional preparations, not the old TracedPoint cache.
-/
def acquireTracedSource (request : AccuracyRequest) : TracedSource cached retained request :=
  let joined := OwnerJoin.reflexive cached.sample.owner
  let acquired := acquire (leftPoint := pointData cached) (rightPoint := pointData cached)
    (leftEntry := sourceEntry cached) (rightEntry := sourceEntry cached)
    (sourceJoin := joined) (retained := retained) request
  (⟨cached, rfl⟩, ⟨⟨joined, rfl⟩, ⟨acquired, rfl⟩⟩)

namespace TracedSource

variable {cached retained} {request : AccuracyRequest} (acquired : TracedSource cached retained request)

/-- Read the complete old source cache, retaining every original route, trace, Point and Entry factory. -/
abbrev original : Entry.TracedPoint models sheet first inside count targetFrame := acquired.1.val

/-- Read the whole new initial join of the SAME literal retained Point Owner with itself. -/
abbrev joined : OwnerJoin cached.sample.owner cached.sample.owner := acquired.2.1.val

/-- Read the actual common-child acquisition consuming that SAME join and the original independent domains. -/
abbrev acquisition : AtPoint cached retained acquired.joined request := acquired.2.2.val

/-- The retained source is whole-value equal to the supplied original cache. -/
theorem original_eq : acquired.original = cached := acquired.1.property

/-- The whole join retains its true new tail/comparison factory. -/
theorem joined_eq : acquired.joined = OwnerJoin.reflexive cached.sample.owner := acquired.2.1.property

/-- The complete child acquisition retains its factory using the cached join rather than running that factory again. -/
theorem acquisition_eq : acquired.acquisition = acquire (leftPoint := pointData cached) (rightPoint := pointData cached)
    (leftEntry := sourceEntry cached) (rightEntry := sourceEntry cached)
    (sourceJoin := acquired.joined) (retained := retained) request := acquired.2.2.property

end TracedSource

section Connection

variable {start : Canonical} {sourceFrame : OwnerFrame (curve.polynomial.eval start)} {index : Fin 2}
variable {entry : Entry models start (sourceFrame.owners index)}
variable {same : entry.sheet = sheet} {sourceInside : face.cell.box.Contains start}
variable (connected : cached.Connection entry same sourceInside)

/-- A connection-owned source bank reuses the literal old Point-side tail in both new source roles.

The complete connection, including its old join and observations, stays
retained. Only the new comparison of that shared tail with itself and the
common-domain bank acquisition are materialized; neither old tail is rerun.
-/
abbrev ConnectionSource (request : AccuracyRequest) :=
  {value : Entry.TracedPoint models sheet first inside count targetFrame × cached.Connection entry same sourceInside //
    value = (cached, connected)} ×
  (Σ joined : {value : OwnerJoin cached.sample.owner cached.sample.owner //
      value = OwnerJoin.ofApproximationTails connected.join.rightTail connected.join.rightTail
        (Equivalence.Equivalent.refl (ownerApproximation cached.sample.owner))},
    {value : AtPoint cached retained joined.val request //
      value = acquire (leftPoint := pointData cached) (rightPoint := pointData cached)
        (leftEntry := sourceEntry cached) (rightEntry := sourceEntry cached)
        (sourceJoin := joined.val) (retained := retained) request})

/-- Consume the existing connection's actual Point-side tail and acquire only the new source comparison and bank.

This is not OwnerJoin.reflexive's factory, which would acquire a fresh
tail. The original right tail is passed twice to ofApproximationTails;
both primitive domains keep their old independent offsets and readings.
-/
def acquireConnectionSource (request : AccuracyRequest) : ConnectionSource cached retained connected request :=
  let tail := connected.join.rightTail
  let joined := OwnerJoin.ofApproximationTails tail tail
    (Equivalence.Equivalent.refl (ownerApproximation cached.sample.owner))
  let acquired := acquire (leftPoint := pointData cached) (rightPoint := pointData cached)
    (leftEntry := sourceEntry cached) (rightEntry := sourceEntry cached)
    (sourceJoin := joined) (retained := retained) request
  (⟨(cached, connected), rfl⟩, ⟨⟨joined, rfl⟩, ⟨acquired, rfl⟩⟩)

namespace ConnectionSource

variable {cached retained connected} {request : AccuracyRequest}
variable (acquired : ConnectionSource cached retained connected request)

/-- Read the SAME full retained TracedPoint cache. -/
abbrev original : Entry.TracedPoint models sheet first inside count targetFrame := acquired.1.val.1

/-- Read the SAME complete old source connection and its original stationary join. -/
abbrev connection : cached.Connection entry same sourceInside := acquired.1.val.2

/-- Read the new comparison of the reused original Point-side tail. -/
abbrev joined : OwnerJoin cached.sample.owner cached.sample.owner := acquired.2.1.val

/-- Read the complete ordered child acquisition on the independent old domains. -/
abbrev acquisition : AtPoint cached retained acquired.joined request := acquired.2.2.val

/-- The whole Point/connection input pair is retained without rebuilding either cache. -/
theorem originals_eq : (acquired.original, acquired.connection) = (cached, connected) := acquired.1.property

/-- The new comparison retains the exact original tail twice, with its actual factory equation. -/
theorem joined_eq : acquired.joined =
    OwnerJoin.ofApproximationTails connected.join.rightTail connected.join.rightTail
      (Equivalence.Equivalent.refl (ownerApproximation cached.sample.owner)) := acquired.2.1.property

/-- The whole common-child acquisition consumes the retained new join exactly once. -/
theorem acquisition_eq : acquired.acquisition = acquire (leftPoint := pointData cached) (rightPoint := pointData cached)
    (leftEntry := sourceEntry cached) (rightEntry := sourceEntry cached)
    (sourceJoin := acquired.joined) (retained := retained) request := acquired.2.2.property

end ConnectionSource

end Connection

end Domains

end Bank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction.Subdivision

end
