module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.OwnerTrace.Move
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Geometry.Rational.Box.Hull
import Purelib.Geometry.Rational.Box.Point
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Paths.PreparedPathParentContainment
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Primitive
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Request
import Purelib.Polynomial.Dense.Power
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Membership
import Purelib.Data.List.DependentProduct
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Tactic.Ring

/-! # Paid original owner traces on retained parallel chart banks

One common numerical preparation frame and one original finite search pay
every actual affine chart chord. Original one-time preparations, actual
paid targets, signed residual comparisons and all-future OwnerLinks remain
cached beside the same original Reading, Geometry, Edge and Chain banks.
The final fold constructs only the original dependent OwnerPath.

This construction concerns the computed affine-chord path. Comparing it to
the independently prepared spatial L-route Blocks, cyclic seams, geometric
twist assembly and period transport remain separate mathematical operations.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Approximation.Rational
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds renaming Data → WaistBounds
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods.Bounds (PointRadius)

open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat.Fraction.Cast.Order (natCast_pos_direct natCast_le_direct)

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic.Canonical (normSq)
open Purelib.Data.Rat
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerTail OwnerJoin ownerApproximation)
open Purelib.Riemann.Branches.PreparedSheetContinuation (StepRequest CachedSource)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Approximation
open Purelib.RootIsolation.SquareRoot.Owner
open Purelib.Integration.Path.Dyadic
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells (Model)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}

variable {limit : Option AccuracyRequest}

namespace OwnerBudget

variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}

/-- The exact strict computed chart-time allowance at every bounded retained edge. -/
@[expose] def TimePaid (budget : OwnerBudget leg coarse limit) (first : Fraction.Rational)
    (times : List Fraction.Rational) : Prop :=
  ∀ edge : Fin times.length,
    (DyadicTrace.indexed first times edge.castSucc - DyadicTrace.indexed first times edge.succ) ^ 2 <
      (leg.source.residualTimeRequest (accuracy leg budget.floor limit).val (leg.traceMovement coarse.bounds)
        (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)).tolerance

/-- The actual retained EdgeData movement caches pay the common owner-reading margin at every bounded edge. -/
@[expose] def DataPaid (first : Fraction.Rational) (times : List Fraction.Rational)
    {inside : Inside (first :: times)} {readings : Readings leg.actual (first :: times) inside}
    {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)}
    (edges : Readings.Edges samples) : Prop :=
  ∀ edge : Fin times.length,
    (edges.get edge).data.movementBound ≤ Radial.Clearance.rootFloor site parameter ^ 2 / 1024

end OwnerBudget

/-- The finite sequential cache view of original chart moves on the same actual reading, sample and Edge banks.

Every nonempty entry is one exact OwnerMove cache. Its actual target and
computed signed comparison are the literal inputs of the retained tail.
Only existing Sigma/products store the production data; the constructed path
itself remains the original dependent OwnerPath.
-/
@[expose] def OwnerMoves {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}
    (budget : OwnerBudget leg coarse limit) (first : Fraction.Rational) (times : List Fraction.Rational) :
    (inside : Inside (first :: times)) → (readings : Readings leg.actual (first :: times) inside) →
    (samples : Readings.Samples readings (leg.source.traceRequest leg.regular)) → (edges : Readings.Edges samples) →
    (step : Fraction.Rational) → (steps : DyadicSteps.Steps first times step) →
    (payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7) →
    (geometries : Geometries readings leg.regular step steps payment) →
    (paid : OwnerBudget.TimePaid budget first times) → (dataPaid : OwnerBudget.DataPaid first times edges) →
    (source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))) →
    NamedEquivalent (source.certificate source.parameterNonzero).value.name
      readings.head.lift.value.name → Type :=
  match times with
  | [] => fun _ _ _ _ _ _ _ _ _ _ _ _ => PUnit
  | next :: times =>
    fun inside readings samples edges step steps payment geometries paid dataPaid source sourceAgreement =>
      Σ move : OwnerMove budget geometries.1 edges.1.data (paid 0) (dataPaid 0) source sourceAgreement,
        OwnerMoves budget next times (fun time member => inside time (List.Mem.tail first member)) readings.tail
          samples.tail edges.tail step steps.2 payment geometries.2
          (fun edge => paid edge.succ) (fun edge => dataPaid edge.succ) move.target move.agrees

namespace OwnerMoves

variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg} {budget : OwnerBudget leg coarse limit}

/-- The exact original source, signed source link and stored move at one bounded original chart edge.

This is an existing Sigma view of original ownership data. Its geometry,
product observation and both payments are the same bounded entries of the
retained original banks. No source, owner, path or preparation is replaced.
-/
@[expose] def Entry {first : Fraction.Rational} {times : List Fraction.Rational}
    {inside : Inside (first :: times)} {readings : Readings leg.actual (first :: times) inside}
    {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} {edges : Readings.Edges samples}
    {step : Fraction.Rational} {steps : DyadicSteps.Steps first times step}
    {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    {geometries : Geometries readings leg.regular step steps payment}
    {paid : OwnerBudget.TimePaid budget first times} {dataPaid : OwnerBudget.DataPaid first times edges}
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))}
    {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      readings.head.lift.value.name}
    (_moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries paid dataPaid
      source sourceAgreement) (edge : Fin times.length) : Type :=
  Σ actual : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) (DyadicTrace.indexed first times edge.castSucc))),
  Σ related : NamedEquivalent (actual.certificate actual.parameterNonzero).value.name
      (readings.get edge.castSucc).lift.value.name,
    OwnerMove budget (geometries.get edge) (edges.get edge).data (paid edge) (dataPaid edge) actual related

/-- The original dependent-product bank of actual sources, signed links and whole moves at their original indices.

Every entry has its same original geometry, observed product and payments.
The bank is a direct view of the existing dependent container, with no new
nominal owner, comparison, trace or parent family.
-/
@[expose] def Entries {first : Fraction.Rational} {times : List Fraction.Rational}
    {inside : Inside (first :: times)} {readings : Readings leg.actual (first :: times) inside}
    {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} {edges : Readings.Edges samples}
    {step : Fraction.Rational} {steps : DyadicSteps.Steps first times step}
    {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    {geometries : Geometries readings leg.regular step steps payment}
    {paid : OwnerBudget.TimePaid budget first times} {dataPaid : OwnerBudget.DataPaid first times edges}
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))}
    {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      readings.head.lift.value.name}
    (moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries paid dataPaid
      source sourceAgreement) : Type :=
  DependentProduct times (fun edge => Entry moves edge)

/-- Cache the actual original source, source agreement and move once for every retained edge in order.

One forward traversal follows the original nested move cache. Each head
retains the supplied whole Owner and agreement beside its literal stored
move; the next head uses that move's actual target and existing signed view.
No Reading, geometry, observation, preparation or source owner is rebuilt.
-/
def entries {first : Fraction.Rational} {times : List Fraction.Rational} :
    {inside : Inside (first :: times)} → {readings : Readings leg.actual (first :: times) inside} →
    {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} → {edges : Readings.Edges samples} →
    {step : Fraction.Rational} → {steps : DyadicSteps.Steps first times step} →
    {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7} →
    {geometries : Geometries readings leg.regular step steps payment} →
    {paid : OwnerBudget.TimePaid budget first times} → {dataPaid : OwnerBudget.DataPaid first times edges} →
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))} →
    {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      readings.head.lift.value.name} →
    (moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries paid dataPaid
      source sourceAgreement) → Entries moves :=
  @(match times with
  | [] => fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} _ => PUnit.unit
  | _ :: _ =>
      fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {source} {sourceAgreement} moves =>
        (⟨source, sourceAgreement, moves.1⟩, entries moves.2))

namespace Entries

variable {first : Fraction.Rational} {times : List Fraction.Rational}
variable {inside : Inside (first :: times)} {readings : Readings leg.actual (first :: times) inside}
variable {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} {edges : Readings.Edges samples}
variable {step : Fraction.Rational} {steps : DyadicSteps.Steps first times step}
variable {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {geometries : Geometries readings leg.regular step steps payment}
variable {paid : OwnerBudget.TimePaid budget first times} {dataPaid : OwnerBudget.DataPaid first times edges}
variable {source : Owner ((Paths.polynomial parameter).eval
  (coordinate site parameter 2 quarter (by decide +kernel) first))}
variable {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
  readings.head.lift.value.name}
variable {moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries
  paid dataPaid source sourceAgreement}

/-- Read the exact stored original source, signed agreement and move at its unchanged bounded edge.

The existing dependent-product readback consumes the completed bank and
original ordinal directly. It does not traverse a move prefix, recompute a
source agreement or materialize a path or numerical preparation.
-/
@[expose] def get (bank : Entries moves) (edge : Fin times.length) : Entry moves edge :=
  DependentProduct.get times bank edge

end Entries

section ConsEntries

variable {first next : Fraction.Rational} {times : List Fraction.Rational}
variable {inside : Inside (first :: next :: times)} {readings : Readings leg.actual (first :: next :: times) inside}
variable {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} {edges : Readings.Edges samples}
variable {step : Fraction.Rational} {steps : DyadicSteps.Steps first (next :: times) step}
variable {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {geometries : Geometries readings leg.regular step steps payment}
variable {paid : OwnerBudget.TimePaid budget first (next :: times)}
variable {dataPaid : OwnerBudget.DataPaid first (next :: times) edges}
variable {source : Owner ((Paths.polynomial parameter).eval
  (coordinate site parameter 2 quarter (by decide +kernel) first))}
variable {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
  readings.head.lift.value.name}
variable (moves : OwnerMoves budget first (next :: times) inside readings samples edges step steps payment geometries
  paid dataPaid source sourceAgreement)

/-- The whole cached tail uses the original tail move cache with the preceding actual target and stored signed link. -/
theorem entries_tail : (entries moves).2 = entries moves.2 := (rfl)

/-- Reading the first original cached entry returns its complete stored source, agreement and move. -/
theorem entries_get_zero : Entries.get (entries moves) 0 = ⟨source, sourceAgreement, moves.1⟩ := (rfl)

/-- Reading a successor cached entry consumes the same original entry-bank tail at the original bounded coordinate. -/
theorem entries_get_succ (edge : Fin times.length) :
    Entries.get (entries moves) edge.succ = Entries.get (entries moves.2) edge := (rfl)

end ConsEntries

section PrimitiveEntries

variable {clearance : OwnerBudget.SourceClearance leg}
variable (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
variable {budget : OwnerBudget leg coarse (some bounds.timeRequest)}
variable {first : Fraction.Rational} {times : List Fraction.Rational}
variable {inside : Inside (first :: times)} {readings : Readings leg.actual (first :: times) inside}
variable {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} {edges : Readings.Edges samples}
variable {step : Fraction.Rational} {steps : DyadicSteps.Steps first times step}
variable {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {geometries : Geometries readings leg.regular step steps payment}
variable {paid : OwnerBudget.TimePaid budget first times} {dataPaid : OwnerBudget.DataPaid first times edges}
variable {source : Owner ((Paths.polynomial parameter).eval
  (coordinate site parameter 2 quarter (by decide +kernel) first))}
variable {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
  readings.head.lift.value.name}
variable {moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries
  paid dataPaid source sourceAgreement}

namespace Entries

/-- The exact original geometry type at the supplied bank's bounded occurrence. -/
private def GeometryAt (edge : Fin times.length) : Type 1 :=
  Geometry (readings.get edge.castSucc) (readings.get edge.succ) leg.regular (by
    change (DyadicTrace.indexed first times edge.succ - DyadicTrace.indexed first times edge.castSucc) ^ 2 ≤ _
    rewrite [steps.indexed edge]
    exact payment)

/-- The original dependent bank of whole primitive/source/reference caches on the supplied actual moves.

Each entry retains its original move, source owner and signed link by the
same bounded occurrence. Its target, source Point and fixed reference are
complete original factory values with exact equations, rather than copied
fields or a replacement root or programme owner.
-/
@[expose] def Primitives (bank : Entries moves) (count : Nat) : Type :=
  DependentProduct times (fun edge => OwnerMove.PrimitiveTarget.Anchored bounds (bank.get edge).2.2 count)

/-- Build a whole primitive cache using the supplied geometry entry and retain its original bounded index.

Only erased equalities transport the original move to its actual geometry.
The executable factory consumes that same stored geometry directly, outside
all equality elimination, so no geometry-prefix lookup is repeated.
-/
private def prepareEntry (edge : Fin times.length) (entry : Entry moves edge)
    (actualGeometry : GeometryAt (readings := readings) (step := step) (steps := steps)
      (payment := payment) edge) (sameGeometry : actualGeometry = geometries.get edge) (count : Nat) :
    OwnerMove.PrimitiveTarget.Anchored bounds entry.2.2 count :=
  let move : OwnerMove budget actualGeometry (edges.get edge).data (paid edge) (dataPaid edge) entry.1 entry.2.1 :=
    Eq.mp (congrArg (fun selected =>
      OwnerMove budget selected (edges.get edge).data (paid edge) (dataPaid edge) entry.1 entry.2.1)
        sameGeometry.symm) entry.2.2
  let retained := OwnerMove.PrimitiveTarget.anchor bounds move count
  have sameType : OwnerMove.PrimitiveTarget.Anchored bounds move count =
      OwnerMove.PrimitiveTarget.Anchored bounds entry.2.2 count := by
    cases sameGeometry
    dsimp only [move]
    rfl
  Eq.mp sameType retained

/-- Prepare one whole original primitive/source/reference cache per retained edge in a paired structural traversal.

The supplied move-entry and geometry banks are traversed once together. Each
factory consumes both actual stored heads, and literal tails are passed to
the next occurrence. No Reading, geometry, source owner or trace is rebuilt;
all ownership/index transports are erased proofs.
-/
def primitives (bank : Entries moves) (count : Nat) : Primitives bounds bank count :=
  DependentProduct.zipWith times bank geometries
    (fun edge => OwnerMove.PrimitiveTarget.Anchored bounds (bank.get edge).2.2 count)
    (fun edge entry actualGeometry sameEntry sameGeometry =>
      let retained := prepareEntry bounds edge entry actualGeometry sameGeometry count
      Eq.mp (congrArg (fun selected : Entry moves edge =>
        OwnerMove.PrimitiveTarget.Anchored bounds selected.2.2 count) sameEntry) retained)

namespace Primitives

/-- Read the actual complete primitive/source/reference entry at its unchanged original bounded occurrence. -/
@[expose] def get {bank : Entries moves} {count : Nat} (retained : Primitives bounds bank count)
    (edge : Fin times.length) : OwnerMove.PrimitiveTarget.Anchored bounds (bank.get edge).2.2 count :=
  DependentProduct.get times retained edge

end Primitives

/-- The paired bank retains exactly the whole original primitive factory result on the same supplied move.

Both original parents and all cached Points, references and payments are
identified as complete values. The equation does not replace the supplied
bank in execution or reconstruct its geometry by readback.
-/
theorem primitives_get (bank : Entries moves) (count : Nat) (edge : Fin times.length) :
    (primitives bounds bank count).get bounds edge =
      OwnerMove.PrimitiveTarget.anchor bounds (bank.get edge).2.2 count := by
  unfold Primitives.get primitives
  rewrite [DependentProduct.get_zipWith]
  rfl

end Entries

end PrimitiveEntries

/-- Construct every actual paid move in order, passing its target directly into the next original preparation cache.

The inherited source comparison is supplied once at the initial owner. Every
later comparison is constructed from the preceding actual moved owner and
the original retained product channels. No future-owner payment, successful
target comparison or OwnerPath is an input.
-/
@[expose] def build (budget : OwnerBudget leg coarse limit) (first : Fraction.Rational)
    (times : List Fraction.Rational) :
    (inside : Inside (first :: times)) → (readings : Readings leg.actual (first :: times) inside) →
    (samples : Readings.Samples readings (leg.source.traceRequest leg.regular)) → (edges : Readings.Edges samples) →
    (step : Fraction.Rational) → (steps : DyadicSteps.Steps first times step) →
    (payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7) →
    (geometries : Geometries readings leg.regular step steps payment) →
    (paid : OwnerBudget.TimePaid budget first times) → (dataPaid : OwnerBudget.DataPaid first times edges) →
    (source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))) →
    (sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      readings.head.lift.value.name) →
    OwnerMoves budget first times inside readings samples edges step steps payment geometries paid dataPaid
      source sourceAgreement :=
  match times with
  | [] => fun _ _ _ _ _ _ _ _ _ _ _ _ => PUnit.unit
  | next :: times =>
    fun inside readings samples edges step steps payment geometries paid dataPaid source sourceAgreement =>
      (fun move : OwnerMove budget geometries.1 edges.1.data (paid 0) (dataPaid 0) source sourceAgreement =>
        ⟨move, build budget next times (fun time member => inside time (List.Mem.tail first member))
          readings.tail samples.tail edges.tail step steps.2 payment geometries.2
          (fun edge => paid edge.succ) (fun edge => dataPaid edge.succ) move.target move.agrees⟩)
        (OwnerMove.build budget geometries.1 edges.1.data (paid 0) (dataPaid 0) source sourceAgreement)

/-- Read the actual final owner from the retained sequential caches without preparing or moving another owner. -/
@[expose] def finish {first : Fraction.Rational} {times : List Fraction.Rational} :
    {inside : Inside (first :: times)} → {readings : Readings leg.actual (first :: times) inside} →
    {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} → {edges : Readings.Edges samples} →
    {step : Fraction.Rational} → {steps : DyadicSteps.Steps first times step} →
    {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7} →
    {geometries : Geometries readings leg.regular step steps payment} →
    {paid : OwnerBudget.TimePaid budget first times} → {dataPaid : OwnerBudget.DataPaid first times edges} →
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))} →
    {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      readings.head.lift.value.name} →
    OwnerMoves budget first times inside readings samples edges step steps payment geometries paid dataPaid
      source sourceAgreement →
    Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) (DyadicTrace.terminal first times)))
  := @(match times with
  | [] => fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {source} {_} _ => source
  | next :: times => fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} moves =>
      finish (first := next) (times := times) moves.2)

/-- Fold the actual same retained source joins and paid links into the original dependent OwnerPath.

The target of each retained move is the literal source of the next cache.
This projection never invokes a preparation, movement, observation or sample
producer. Stationary preparation joins remain explicit original path links.
-/
@[expose] def path {first : Fraction.Rational} {times : List Fraction.Rational} :
    {inside : Inside (first :: times)} → {readings : Readings leg.actual (first :: times) inside} →
    {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} → {edges : Readings.Edges samples} →
    {step : Fraction.Rational} → {steps : DyadicSteps.Steps first times step} →
    {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7} →
    {geometries : Geometries readings leg.regular step steps payment} →
    {paid : OwnerBudget.TimePaid budget first times} → {dataPaid : OwnerBudget.DataPaid first times edges} →
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))} →
    {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      readings.head.lift.value.name} →
    (moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries paid dataPaid
      source sourceAgreement) →
    OwnerPath (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) first) source
      (coordinate site parameter 2 quarter (by decide +kernel) (DyadicTrace.terminal first times)) moves.finish
  := @(match times with
  | [] => fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {source} {_} _ => .nil _ source
  | next :: times => fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} moves =>
      moves.1.path.append (path (first := next) (times := times) moves.2))

/-- Build original spatial blocks in the actual affine-owner order, constructing every handoff internally.

The unchanged Reading, Geometry, Edge, sample and OwnerMove banks are inputs.
Every completed spatial finish is kept beside its computed original join;
the following block starts on the literal preceding affine target. No
reading bank, source attachment or affine movement is constructed again.
-/
@[expose] def spatialBlocks {first : Fraction.Rational} {times : List Fraction.Rational} :
    {inside : Inside (first :: times)} → {readings : Readings leg.actual (first :: times) inside} →
    {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} → {edges : Readings.Edges samples} →
    {step : Fraction.Rational} → {steps : DyadicSteps.Steps first times step} →
    {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7} →
    {geometries : Geometries readings leg.regular step steps payment} →
    {paid : OwnerBudget.TimePaid budget first times} → {dataPaid : OwnerBudget.DataPaid first times edges} →
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))} →
    {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      readings.head.lift.value.name} →
    (moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries paid dataPaid
      source sourceAgreement) →
    CoveredTracedPath.Blocks (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) first) source
      (coordinate site parameter 2 quarter (by decide +kernel) (DyadicTrace.terminal first times)) moves.finish
  := @(match times with
  | [] => fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {source} {_} _ => .nil _ source
  | next :: times => fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} moves =>
      moves.1.prependSpatial (spatialBlocks (first := next) (times := times) moves.2))

/-- The compared spatial fold keeps one geometric block per chart edge, excluding stationary join payments. -/
theorem spatialBlocks_length {first : Fraction.Rational} {times : List Fraction.Rational} :
    {inside : Inside (first :: times)} → {readings : Readings leg.actual (first :: times) inside} →
    {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} → {edges : Readings.Edges samples} →
    {step : Fraction.Rational} → {steps : DyadicSteps.Steps first times step} →
    {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7} →
    {geometries : Geometries readings leg.regular step steps payment} →
    {paid : OwnerBudget.TimePaid budget first times} → {dataPaid : OwnerBudget.DataPaid first times edges} →
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))} →
    {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      readings.head.lift.value.name} →
    (moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries paid dataPaid
      source sourceAgreement) →
    moves.spatialBlocks.length = times.length
  := @(match times with
  | [] => fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {source} {_} _ =>
      CoveredTracedPath.Blocks.length_nil _ source
  | next :: times => fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} moves => by
      change (moves.1.prependSpatial (spatialBlocks (first := next) (times := times) moves.2)).length =
        times.length + 1
      exact (moves.1.prependSpatial_length (spatialBlocks (first := next) (times := times) moves.2)).trans
        (congrArg Nat.succ (spatialBlocks_length (first := next) (times := times) moves.2)))

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Curves.Legendre.Periods

section ParentCacheEntries

variable {first : Fraction.Rational} {times : List Fraction.Rational}
variable {inside : Inside (first :: times)} {readings : Readings leg.actual (first :: times) inside}
variable {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} {edges : Readings.Edges samples}
variable {step : Fraction.Rational} {steps : DyadicSteps.Steps first times step}
variable {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {geometries : Geometries readings leg.regular step steps payment}
variable {paid : OwnerBudget.TimePaid budget first times} {dataPaid : OwnerBudget.DataPaid first times edges}
variable {source : Owner ((Paths.polynomial parameter).eval
  (coordinate site parameter 2 quarter (by decide +kernel) first))}
variable {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
  readings.head.lift.value.name}
variable {moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries
  paid dataPaid source sourceAgreement}

namespace Entries

/-- The original whole parent-cache type at one supplied original move-entry occurrence.

The actual source, geometry, covered factory and frame curve remain nominal
indices. This exact type view does not construct a cover, owner or cache.
-/
@[expose] def ParentCacheAt (bank : Entries moves) (frame : Paths.Frame parameter)
    (differential : Differential 1) (sheet : Fin 2) (edge : Fin times.length) : Type :=
  ParentCache (curve := Fibre.frameCurve frame)
    (Covered.build (geometries.get edge) (Entries.get (moves := moves) bank edge).1).block differential sheet

end Entries

/-- Traverse the same spatial parent-cache spine at the original canonical move-entry types. -/
private def cacheEntries {first : Fraction.Rational} {times : List Fraction.Rational} :
    {inside : Inside (first :: times)} → {readings : Readings leg.actual (first :: times) inside} →
    {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} → {edges : Readings.Edges samples} →
    {step : Fraction.Rational} → {steps : DyadicSteps.Steps first times step} →
    {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7} →
    {geometries : Geometries readings leg.regular step steps payment} →
    {paid : OwnerBudget.TimePaid budget first times} → {dataPaid : OwnerBudget.DataPaid first times edges} →
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))} →
    {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      readings.head.lift.value.name} →
    (moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries paid dataPaid
      source sourceAgreement) → (frame : Paths.Frame parameter) → (differential : Differential 1) → (sheet : Fin 2) →
    CoveredTracedPath.Blocks.ParentCaches (curve := Fibre.frameCurve frame) differential sheet moves.spatialBlocks →
    DependentProduct times (fun edge => Entries.ParentCacheAt (entries moves) frame differential sheet edge)
  := @(match times with
  | [] => fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} _ _ _ _ _ => PUnit.unit
  | _ :: times =>
      fun {_} {_} {_} {_} {_} {_} {_} {geometries} {_} {_} {_} {_} moves frame differential sheet caches =>
        ⟨Eq.mpr (congrArg (fun selected : Entry moves 0 =>
          ParentCache (curve := Fibre.frameCurve frame) (Covered.build (geometries.get 0) selected.1).block
            differential sheet) (entries_get_zero moves)) caches.1,
          DependentProduct.transport times (fun edge =>
            (congrArg (fun selected : Entry moves edge.succ =>
              ParentCache (curve := Fibre.frameCurve frame) (Covered.build (geometries.get edge.succ) selected.1).block
                differential sheet) (entries_get_succ moves edge)).symm)
            (cacheEntries moves.2 frame differential sheet caches.2)⟩)

/-- Retain the supplied whole parent caches at their original bounded move occurrences.

Every moving block contributes its original complete ParentCache. Stationary
handoffs forward the same cache tail. The original high-universe empty bank
is lowered to the dependent product's unit by structural traversal; only the
small tuple spine is allocated, while each cache is passed unchanged.
-/
def parentCacheEntries (bank : {actual : Entries moves // actual = entries moves})
    (frame : Paths.Frame parameter) (differential : Differential 1) (sheet : Fin 2)
    (caches : CoveredTracedPath.Blocks.ParentCaches (curve := Fibre.frameCurve frame)
      differential sheet moves.spatialBlocks) :
    DependentProduct times (fun edge =>
      Entries.ParentCacheAt (moves := moves) bank.val frame differential sheet edge) := by
  rcases bank with ⟨bank, retained⟩
  subst bank
  exact cacheEntries moves frame differential sheet caches

end ParentCacheEntries

section ConsParentCacheEntries

variable {first next : Fraction.Rational} {times : List Fraction.Rational}
variable {inside : Inside (first :: next :: times)} {readings : Readings leg.actual (first :: next :: times) inside}
variable {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} {edges : Readings.Edges samples}
variable {step : Fraction.Rational} {steps : DyadicSteps.Steps first (next :: times) step}
variable {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {geometries : Geometries readings leg.regular step steps payment}
variable {paid : OwnerBudget.TimePaid budget first (next :: times)}
variable {dataPaid : OwnerBudget.DataPaid first (next :: times) edges}
variable {source : Owner ((Paths.polynomial parameter).eval
  (coordinate site parameter 2 quarter (by decide +kernel) first))}
variable {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
  readings.head.lift.value.name}
variable (moves : OwnerMoves budget first (next :: times) inside readings samples edges step steps payment geometries
  paid dataPaid source sourceAgreement)

/-- The first view lookup returns the identical complete original head parent cache. -/
theorem parentCacheEntries_get_zero (bank : {actual : Entries moves // actual = entries moves})
    (frame : Paths.Frame parameter) (differential : Differential 1) (sheet : Fin 2)
    (caches : CoveredTracedPath.Blocks.ParentCaches (curve := Fibre.frameCurve frame)
      differential sheet moves.spatialBlocks) :
    HEq (DependentProduct.get (next :: times)
      (parentCacheEntries bank frame differential sheet caches) 0) caches.1 := by
  rcases bank with ⟨bank, retained⟩
  subst bank
  exact cast_heq ((congrArg (fun selected : Entry moves 0 =>
    ParentCache (curve := Fibre.frameCurve frame) (Covered.build (geometries.get 0) selected.1).block
      differential sheet) (entries_get_zero moves)).symm) caches.1

/-- The whole remaining view is the exact original tail view under its bounded entry-type transport. -/
theorem parentCacheEntries_tail (bank : {actual : Entries moves // actual = entries moves})
    (frame : Paths.Frame parameter) (differential : Differential 1) (sheet : Fin 2)
    (caches : CoveredTracedPath.Blocks.ParentCaches (curve := Fibre.frameCurve frame)
      differential sheet moves.spatialBlocks) :
    HEq (parentCacheEntries bank frame differential sheet caches).2
      (parentCacheEntries ⟨entries moves.2, rfl⟩ frame differential sheet caches.2) := by
  rcases bank with ⟨bank, retained⟩
  subst bank
  exact cast_heq (DependentProduct.family_eq times (fun edge =>
    (congrArg (fun selected : Entry moves edge.succ =>
      ParentCache (curve := Fibre.frameCurve frame) (Covered.build (geometries.get edge.succ) selected.1).block
        differential sheet) (entries_get_succ moves edge)).symm))
    (parentCacheEntries ⟨entries moves.2, rfl⟩ frame differential sheet caches.2)

/-- Every successor lookup consumes the same complete original tail cache at its unchanged bounded index. -/
theorem parentCacheEntries_get_succ (bank : {actual : Entries moves // actual = entries moves})
    (frame : Paths.Frame parameter) (differential : Differential 1) (sheet : Fin 2)
    (caches : CoveredTracedPath.Blocks.ParentCaches (curve := Fibre.frameCurve frame)
      differential sheet moves.spatialBlocks) (edge : Fin times.length) :
    HEq (DependentProduct.get (next :: times)
      (parentCacheEntries bank frame differential sheet caches) edge.succ)
      (DependentProduct.get times
        (parentCacheEntries ⟨entries moves.2, rfl⟩ frame differential sheet caches.2) edge) := by
  rcases bank with ⟨bank, retained⟩
  subst bank
  exact DependentProduct.get_transport times (fun edge =>
    (congrArg (fun selected : Entry moves edge.succ =>
      ParentCache (curve := Fibre.frameCurve frame) (Covered.build (geometries.get edge.succ) selected.1).block
        differential sheet) (entries_get_succ moves edge)).symm)
    (parentCacheEntries ⟨entries moves.2, rfl⟩ frame differential sheet caches.2) edge

end ConsParentCacheEntries

section SourceRows

open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Blocks

variable {first : Fraction.Rational} {times : List Fraction.Rational}
variable {inside : Inside (first :: times)} {readings : Readings leg.actual (first :: times) inside}
variable {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} {edges : Readings.Edges samples}
variable {step : Fraction.Rational} {steps : DyadicSteps.Steps first times step}
variable {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {geometries : Geometries readings leg.regular step steps payment}
variable {paid : OwnerBudget.TimePaid budget first times} {dataPaid : OwnerBudget.DataPaid first times edges}
variable {source : Owner ((Paths.polynomial parameter).eval
  (coordinate site parameter 2 quarter (by decide +kernel) first))}
variable {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
  readings.head.lift.value.name}
variable {moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries
  paid dataPaid source sourceAgreement}

variable {Value : Type u}
variable (frame : Paths.Frame parameter) (differential : Differential 1) (sheet : Fin 2)
variable (family : (parents : List (CenteredEdge (Fibre.frameCurve frame) differential)) →
  CoveredParents 1 parents → Type v)
variable (divide : ∀ {first last : List (CenteredEdge (Fibre.frameCurve frame) differential)}
  (firstCover : CoveredParents 1 first) (lastCover : CoveredParents 1 last),
  family (first ++ last) (Riemann.Integration.PreparedCoveredParentLists.CoveredParents.append firstCover lastCover) →
    family first firstCover × family last lastCover)
variable (read : ∀ {start finish : Canonical} {ambient : Geometry.Rational.Box}
  {path : Polynomial.Geometry.ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
  {source : Owner ((Fibre.frameCurve frame).polynomial.eval start)} (covered : CoveredTracedPath path source)
  (cache : ParentCache (curve := Fibre.frameCurve frame) covered differential sheet),
  family cache.parents cache.covered → Value)
variable (predicate : (parents : List (CenteredEdge (Fibre.frameCurve frame) differential)) →
  CoveredParents 1 parents → Value → Prop)

/-- The read value at one bounded retained move has its original parent-cache predicate.

The supplied bank is split by the original interpreter. The proposition
uses the unchanged ordinal cache lookup, including its exact parent list
and covering patches, without constructing a second numerical family.
-/
@[expose] def MappedRow (bank : {actual : Entries moves // actual = entries moves})
    (caches : ParentCaches (curve := Fibre.frameCurve frame)
      differential sheet moves.spatialBlocks)
    (input : family caches.parents caches.covered) (edge : Fin times.length) : Prop :=
  ∃ inside : edge.val < (ParentCaches.mapBanks family divide read caches input).length,
    let cache := DependentProduct.get times
      (parentCacheEntries (moves := moves) bank frame differential sheet caches) edge
    predicate cache.parents cache.covered
      ((ParentCaches.mapBanks family divide read caches input)[edge.val]'inside)

/-- The original moving rows preserve their count and every actual ordinal parent-cache predicate. -/
@[expose] def MappedRows (bank : {actual : Entries moves // actual = entries moves})
    (caches : ParentCaches (curve := Fibre.frameCurve frame)
      differential sheet moves.spatialBlocks)
    (input : family caches.parents caches.covered) : Prop :=
  (ParentCaches.mapBanks family divide read caches input).length = times.length ∧
  ∀ edge : Fin times.length,
    MappedRow frame differential sheet family divide read predicate (moves := moves) bank caches input edge

/-- The retained block interpreter and ordinal cache view identify the same actual moving occurrences.

The sole branch condition certifies the supplied read operation on its
actual split prefix. Stationary handoffs forward the original bank;
recursion consumes the literal remaining caches and bank suffix.
-/
theorem mappedRows
    (good : ∀ {start finish : Canonical} {ambient : Geometry.Rational.Box}
      {path : Polynomial.Geometry.ClearPath (Fibre.frameCurve frame).polynomial ambient start finish}
      {source : Owner ((Fibre.frameCurve frame).polynomial.eval start)} (covered : CoveredTracedPath path source)
      (cache : ParentCache (curve := Fibre.frameCurve frame) covered differential sheet)
      (input : family cache.parents cache.covered),
      predicate cache.parents cache.covered (read covered cache input))
    {first : Fraction.Rational} {times : List Fraction.Rational} :
    {inside : Inside (first :: times)} → {readings : Readings leg.actual (first :: times) inside} →
    {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} → {edges : Readings.Edges samples} →
    {step : Fraction.Rational} → {steps : DyadicSteps.Steps first times step} →
    {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7} →
    {geometries : Geometries readings leg.regular step steps payment} →
    {paid : OwnerBudget.TimePaid budget first times} → {dataPaid : OwnerBudget.DataPaid first times edges} →
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))} →
    {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      readings.head.lift.value.name} →
    (moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries paid dataPaid
      source sourceAgreement) →
    (retained : {actual : Entries moves // actual = entries moves}) →
    (caches : ParentCaches (curve := Fibre.frameCurve frame)
      differential sheet moves.spatialBlocks) →
    (input : family caches.parents caches.covered) →
    MappedRows frame differential sheet family divide read predicate (moves := moves) retained caches input
  := @(match times with
  | [] => fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {source} {_} moves retained caches input => by
      rcases retained with ⟨bank, factory⟩
      subst bank
      refine ⟨?_, ?_⟩
      · erw [ParentCaches.mapBanks_nil]
        rfl
      · intro edge
        exact Fin.elim0 edge
  | next :: times =>
      fun {inside} {readings} {samples} {edges} {step} {steps} {payment} {geometries} {paid} {dataPaid}
        {source} {sourceAgreement} moves retained caches input => by
      rcases retained with ⟨bank, factory⟩
      subst bank
      let divided := divide caches.1.covered (ParentCaches.covered caches.2) input
      have branch := ParentCaches.mapBanks_cons family divide read
        (Covered.build geometries.1 source).block
        (.handoff ⟨moves.1.target, moves.1.spatialJoin (Covered.build geometries.1 source)⟩
          moves.2.spatialBlocks) caches input
      have joined := ParentCaches.mapBanks_handoff family divide read
        ⟨moves.1.target, moves.1.spatialJoin (Covered.build geometries.1 source)⟩
        moves.2.spatialBlocks caches.2 divided.2
      have branch := branch.trans (congrArg
        (List.cons (read (Covered.build geometries.1 source).block caches.1 divided.1)) joined)
      have remaining : MappedRows frame differential sheet family divide read predicate
          (first := next) (times := times) (budget := budget)
          (inside := fun time member => inside time (List.Mem.tail first member))
          (readings := readings.tail) (samples := samples.tail) (edges := edges.tail)
          (step := step) (steps := steps.2) (payment := payment) (geometries := geometries.2)
          (paid := fun edge => paid edge.succ) (dataPaid := fun edge => dataPaid edge.succ)
          (source := moves.1.target) (sourceAgreement := moves.1.agrees) (moves := moves.2)
          ⟨entries moves.2, rfl⟩ caches.2 divided.2 :=
        mappedRows good (first := next) (times := times)
          (inside := fun time member => inside time (List.Mem.tail first member))
          (readings := readings.tail) (samples := samples.tail) (edges := edges.tail)
          (step := step) (steps := steps.2) (payment := payment) (geometries := geometries.2)
          (paid := fun edge => paid edge.succ) (dataPaid := fun edge => dataPaid edge.succ)
          (source := moves.1.target) (sourceAgreement := moves.1.agrees)
          moves.2 ⟨entries moves.2, rfl⟩ caches.2 divided.2
      refine ⟨?_, ?_⟩
      · erw [branch]
        exact congrArg Nat.succ remaining.1
      · intro edge
        refine Fin.cases (motive := fun edge =>
          MappedRow frame differential sheet family divide read predicate
            (moves := moves) ⟨entries moves, rfl⟩ caches input edge) ?_ ?_ edge
        · unfold MappedRow
          have cacheSame : DependentProduct.get (next :: times)
              (parentCacheEntries (moves := moves) ⟨entries moves, rfl⟩ frame differential sheet caches) 0 = caches.1 :=
            eq_of_heq (parentCacheEntries_get_zero moves ⟨entries moves, rfl⟩ frame differential sheet caches)
          have bound : 0 <
              (ParentCaches.mapBanks family divide read caches input).length := by
            erw [branch]
            exact Nat.zero_lt_succ _
          let value := read (Covered.build geometries.1 source).block caches.1 divided.1
          have actual := good (Covered.build geometries.1 source).block caches.1 divided.1
          have propagated := Eq.mpr (congrArg
            (fun selected : ParentCache (curve := Fibre.frameCurve frame)
                (Covered.build geometries.1 source).block differential sheet =>
              predicate selected.parents selected.covered value) cacheSame) actual
          refine ⟨bound, ?_⟩
          exact Eq.mpr (congrArg (fun row =>
            let cache := DependentProduct.get (next :: times)
              (parentCacheEntries (moves := moves) ⟨entries moves, rfl⟩ frame differential sheet caches) 0
            predicate cache.parents cache.covered row) (getElem_congr branch rfl bound)) propagated
        · intro edge
          unfold MappedRow
          have tailRow : MappedRow frame differential sheet family divide read predicate
              (first := next) (times := times) (budget := budget)
              (inside := fun time member => inside time (List.Mem.tail first member))
              (readings := readings.tail) (samples := samples.tail) (edges := edges.tail)
              (step := step) (steps := steps.2) (payment := payment) (geometries := geometries.2)
              (paid := fun edge => paid edge.succ) (dataPaid := fun edge => dataPaid edge.succ)
              (source := moves.1.target) (sourceAgreement := moves.1.agrees) (moves := moves.2)
              ⟨entries moves.2, rfl⟩ caches.2 divided.2 edge := remaining.2 edge
          unfold MappedRow at tailRow
          rcases tailRow with ⟨inside, actual⟩
          have cacheSame : DependentProduct.get (next :: times)
              (parentCacheEntries (moves := moves) ⟨entries moves, rfl⟩ frame differential sheet caches) edge.succ =
              DependentProduct.get times
                (parentCacheEntries (moves := moves.2) ⟨entries moves.2, rfl⟩ frame differential sheet caches.2) edge :=
            eq_of_heq (parentCacheEntries_get_succ moves ⟨entries moves, rfl⟩ frame differential sheet caches edge)
          let value :=
            (ParentCaches.mapBanks family divide read (blocks := moves.2.spatialBlocks)
              caches.2 divided.2)[edge.val]'inside
          have propagated := Eq.mpr (congrArg
            (fun selected : Entries.ParentCacheAt (entries moves.2) frame differential sheet edge =>
              predicate selected.parents selected.covered value) cacheSame) actual
          have bound : edge.succ.val <
              (ParentCaches.mapBanks family divide read caches input).length := by
            erw [branch]
            exact Nat.succ_lt_succ inside
          refine ⟨bound, ?_⟩
          exact Eq.mpr (congrArg (fun row =>
            let cache := DependentProduct.get (next :: times)
              (parentCacheEntries (moves := moves) ⟨entries moves, rfl⟩ frame differential sheet caches) edge.succ
            predicate cache.parents cache.covered row) (getElem_congr branch rfl bound)) propagated)

/-- Every global source row has the complete six-channel cells at its original move's parent-cache occurrence.

This is the original block interpreter specialized to its supplied source
product. The count and bounded ordinal predicate retain the actual split
prefix, unchanged global Targets and same source floor.
-/
@[expose] def SourceRows (bank : {actual : Entries moves // actual = entries moves})
    (frame : Paths.Frame parameter) (differential : Differential 1) (sheet : Fin 2)
    (caches : ParentCaches (curve := Fibre.frameCurve frame) differential sheet moves.spatialBlocks)
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage floor : Nat} {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParents.OnBlocks (frame := frame) (basis := differential)
      (sheet := sheet) (floor := floor) (targets := targets) caches) : Prop :=
  MappedRows frame differential sheet
    (fun parents cover => PreparedParents (frame := frame) (basis := differential) (count := 1)
      (parents := parents) cover floor targets)
    (fun {first last} firstCover lastCover input =>
      PreparedParents.split (frame := frame) (basis := differential) (count := 1)
        (floor := floor) (targets := targets) (first := first) (last := last) firstCover lastCover input)
    (fun _ cache input => DependentVector.ofFn (fun channel : Fin 6 =>
      PreparedParents.cells (frame := frame) (basis := differential) (count := 1)
        (parents := cache.parents) (covered := cache.covered) (floor := floor) (targets := targets) input channel))
    (fun parents cover row => PreparedParents.CellRow (frame := frame) (basis := differential)
      (count := 1) (parents := parents) cover floor targets row)
    (moves := moves) bank caches prepared

/-- The actual global source bank supplies every same-occurrence six-cell row without another acquisition. -/
theorem sourceRows (bank : {actual : Entries moves // actual = entries moves})
    (frame : Paths.Frame parameter) (differential : Differential 1) (sheet : Fin 2)
    (caches : ParentCaches (curve := Fibre.frameCurve frame) differential sheet moves.spatialBlocks)
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage floor : Nat} {targets : CellEndpoints.Targets original stage}
    (prepared : PreparedParents.OnBlocks (frame := frame) (basis := differential)
      (sheet := sheet) (floor := floor) (targets := targets) caches) :
    SourceRows (moves := moves) bank frame differential sheet caches prepared := by
  unfold SourceRows
  apply mappedRows
  intro start finish ambient path source covered cache input
  exact ⟨input, rfl⟩

end SourceRows

section ParentPointEntries

variable {clearance : OwnerBudget.SourceClearance leg}
variable (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
variable {budget : OwnerBudget leg coarse (some bounds.timeRequest)}
variable {first : Fraction.Rational} {times : List Fraction.Rational}
variable {inside : Inside (first :: times)} {readings : Readings leg.actual (first :: times) inside}
variable {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} {edges : Readings.Edges samples}
variable {step : Fraction.Rational} {steps : DyadicSteps.Steps first times step}
variable {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {geometries : Geometries readings leg.regular step steps payment}
variable {paid : OwnerBudget.TimePaid budget first times} {dataPaid : OwnerBudget.DataPaid first times edges}
variable {source : Owner ((Paths.polynomial parameter).eval
  (coordinate site parameter 2 quarter (by decide +kernel) first))}
variable {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
  readings.head.lift.value.name}
variable {moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries
  paid dataPaid source sourceAgreement}

namespace Entries.Primitives

variable {bank : Entries moves} {count : Nat}

/-- The original parent-Point cache type at one retained primitive and parent-cache occurrence.

The actual original move, source owner, covered factory and whole parent
list are indices. Each result retains the same primitive's source Point and
fixed Reference, with the original signed per-parent comparisons.
-/
@[expose] def ParentPointsAt (retained : Primitives bounds bank count) (frame : Paths.Frame parameter)
    (differential : Differential 1) (sheet : Fin 2)
    (caches : DependentProduct times (fun edge => bank.ParentCacheAt frame differential sheet edge))
    (edge : Fin times.length) : Type :=
  OwnerMove.PrimitiveTarget.ParentPoints bounds (retained.get bounds edge).target
    (retained.get bounds edge).sourcePoint frame
    (Covered.build (geometries.get edge) (bank.get edge).1) (DependentProduct.get times caches edge)

/-- One cached finite view of the original parent bank and its actual shared-reference Point results.

The whole original cache entries remain literal inputs. Only the view's
small tuple spine is new, followed by one original per-parent construction
on each already retained primitive, source Point and fixed Reference.
-/
@[expose] def ParentPoints (retained : Primitives bounds bank count)
    (factory : bank = entries moves) (frame : Paths.Frame parameter)
    (differential : Differential 1) (sheet : Fin 2)
    (caches : CoveredTracedPath.Blocks.ParentCaches (curve := Fibre.frameCurve frame)
      differential sheet moves.spatialBlocks) : Type :=
  Σ cacheEntries : {actual : DependentProduct times (fun edge => bank.ParentCacheAt frame differential sheet edge) //
      actual = parentCacheEntries ⟨bank, factory⟩ frame differential sheet caches},
    DependentProduct times (fun edge => ParentPointsAt bounds retained frame differential sheet cacheEntries.val edge)

/-- Construct actual signed parent Points from the same retained primitive and whole original parent-cache heads.

The supplied primitive and cache banks are paired in one structural pass.
Each original Point producer receives its actual stored cache and the very
same source Point and Reference. Geometry and prefix provenance are used
only in erased types/proofs; no source preparation or prefix lookup runs.
-/
def parentPoints (retained : Primitives bounds bank count) (factory : bank = entries moves)
    (frame : Paths.Frame parameter) (differential : Differential 1) (sheet : Fin 2)
    (caches : CoveredTracedPath.Blocks.ParentCaches (curve := Fibre.frameCurve frame)
      differential sheet moves.spatialBlocks) : ParentPoints bounds retained factory frame differential sheet caches :=
  let cacheEntries := parentCacheEntries ⟨bank, factory⟩ frame differential sheet caches
  let points := DependentProduct.zipWith times retained cacheEntries
    (fun edge => ParentPointsAt bounds retained frame differential sheet cacheEntries edge)
    (fun edge actual cache sameActual sameCache =>
      let value := OwnerMove.PrimitiveTarget.parentPoints bounds actual.target actual.sourcePoint frame
        (Covered.build (geometries.get edge) (bank.get edge).1) cache
        ⟨actual.reference, actual.reference_eq⟩
      have sameType : OwnerMove.PrimitiveTarget.ParentPoints bounds actual.target actual.sourcePoint frame
          (Covered.build (geometries.get edge) (bank.get edge).1) cache =
            ParentPointsAt bounds retained frame differential sheet cacheEntries edge := by
        cases sameActual
        cases sameCache
        rfl
      Eq.mp sameType value)
  ⟨⟨cacheEntries, rfl⟩, points⟩

/-- Every retained row is the complete original parent-Point factory on its actual cached primitive and parent list. -/
theorem parentPoints_get (retained : Primitives bounds bank count) (factory : bank = entries moves)
    (frame : Paths.Frame parameter) (differential : Differential 1) (sheet : Fin 2)
    (caches : CoveredTracedPath.Blocks.ParentCaches (curve := Fibre.frameCurve frame)
      differential sheet moves.spatialBlocks) (edge : Fin times.length) :
    DependentProduct.get times (parentPoints bounds retained factory frame differential sheet caches).2 edge =
      OwnerMove.PrimitiveTarget.parentPoints bounds (retained.get bounds edge).target
        (retained.get bounds edge).sourcePoint frame
        (Covered.build (geometries.get edge) (bank.get edge).1)
        (DependentProduct.get times (parentPoints bounds retained factory frame differential sheet caches).1.val edge)
        ⟨(retained.get bounds edge).reference, (retained.get bounds edge).reference_eq⟩ := by
  unfold parentPoints
  rewrite [DependentProduct.get_zipWith]
  rfl

end Entries.Primitives

end ParentPointEntries

/-- Read the actual terminal signed comparison from the same sequential move caches.

The empty chain returns its supplied original source agreement. A nonempty
chain reads the already retained last agreement through its exact tail;
no owner, preparation, residual observation or comparison is produced here.
-/
@[expose] def agreement {first : Fraction.Rational} {times : List Fraction.Rational} :
    {inside : Inside (first :: times)} → {readings : Readings leg.actual (first :: times) inside} →
    {samples : Readings.Samples readings (leg.source.traceRequest leg.regular)} → {edges : Readings.Edges samples} →
    {step : Fraction.Rational} → {steps : DyadicSteps.Steps first times step} →
    {payment : step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7} →
    {geometries : Geometries readings leg.regular step steps payment} →
    {paid : OwnerBudget.TimePaid budget first times} → {dataPaid : OwnerBudget.DataPaid first times edges} →
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))} →
    {sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      readings.head.lift.value.name} →
    (moves : OwnerMoves budget first times inside readings samples edges step steps payment geometries paid dataPaid
      source sourceAgreement) →
    NamedEquivalent
      (moves.finish.certificate moves.finish.parameterNonzero).value.name
      (readings.get (Fin.last times.length)).lift.value.name
 := @(match times with
  | [] => fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {sourceAgreement} _ => sourceAgreement
  | next :: times => fun {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} moves =>
      agreement (first := next) (times := times) moves.2)

end OwnerMoves

namespace OwnerBudget

variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}

/-- The exact chart step selected by the actual retained finite owner-preparation search. -/
@[expose] def step (budget : OwnerBudget leg coarse limit) : Fraction.Rational :=
  (1 - 0) * (1 / 2) ^ budget.fine.selection.stage

/-- The actual selected mesh keeps its original exact adjacent-step equations. -/
theorem steps (budget : OwnerBudget leg coarse limit) :
    DyadicSteps.Steps 0 (DyadicTrace.tail budget.fine.selection.stage (0 : Fraction.Rational) 1) budget.step :=
  DyadicSteps.tail_steps budget.fine.selection.stage 0 1

/-- The actual stronger selection also pays every original sharp chart region. -/
theorem step_paid (budget : OwnerBudget leg coarse limit) :
    budget.step ^ 2 ≤ Geometric.Basic.quarterRadius 1 7 := by
  let edge : Fin (DyadicTrace.tail budget.fine.selection.stage (0 : Fraction.Rational) 1).length :=
    ⟨0, by rewrite [DyadicSteps.tail_length]; exact Nat.pow_pos (by decide +kernel)⟩
  have width := budget.steps.width_square edge
  rewrite [budget.steps.indexed edge] at width
  calc
    _ = Geometric.Basic.quarterRadius 1 budget.fine.selection.stage * ((1 : Fraction.Rational) - 0) ^ 2 :=
      width
    _ = Geometric.Basic.quarterRadius 1 budget.fine.selection.stage := by ring1
    _ ≤ _ := Geometric.Basic.quarterRadius_antitone (by decide +kernel) budget.fine.selection.lower

/-- Every original fine-mesh edge has the actual strict allowance consumed by sequential owner construction. -/
theorem time_paid (budget : OwnerBudget leg coarse limit) :
    TimePaid budget 0 (DyadicTrace.tail budget.fine.selection.stage (0 : Fraction.Rational) 1) := by
  intro edge
  have paid := budget.fine.edge_paid_lt edge
  have same := congrArg (fun bounds => min (1 / Fraction.Cast.fromInt 16384)
    ((accuracy leg budget.floor limit).val.tolerance / (1 + leg.traceMovement bounds))) budget.fine_bounds
  exact paid.trans_le same.le

/-- Every actual retained fine-mesh EdgeData cache pays the common owner-link margin. -/
theorem data_paid (budget : OwnerBudget leg coarse limit) (trace : RootTrace leg budget.fine) :
    DataPaid 0 (DyadicTrace.tail budget.fine.selection.stage (0 : Fraction.Rational) 1) trace.edges := by
  intro edge
  have same := congrArg (fun bounds => leg.traceMovement bounds *
    (DyadicTrace.indexed 0 (DyadicTrace.tail budget.fine.selection.stage 0 1) edge.castSucc -
      DyadicTrace.indexed 0 (DyadicTrace.tail budget.fine.selection.stage 0 1) edge.succ) ^ 2)
    budget.fine_bounds
  exact (trace.movement edge).le.trans (same.le.trans (budget.edge_movement_root edge))

/-- Return the retained actual source clearance at zero and construct each other original chart clearance once. -/
@[expose] def clearanceAt (budget : OwnerBudget leg coarse limit) (time : Fraction.Rational) :
    {retained : ClearanceType (quarter := quarter) (first := time) leg.regular //
      retained = Radial.Clearance.clearance site parameter (Waist.direction quarter time)
        leg.regular leg.actual.data.bound} := by
  if zero : time = 0 then
    cases zero
    exact budget.clearance
  else
    exact ⟨Radial.Clearance.clearance site parameter (Waist.direction quarter time)
      leg.regular leg.actual.data.bound, rfl⟩

/-- The first actual chord uses the identical complete source-clearance cache retained by the common frame. -/
theorem clearanceAt_zero (budget : OwnerBudget leg coarse limit) : budget.clearanceAt 0 = budget.clearance := by
  unfold clearanceAt
  rewrite [dif_pos rfl]
  rfl

/-- Materialize the actual sharp spatial geometry bank on the same retained fine Reading entries.

The first clearance is the common frame's identical original cache. Every
other edge builds its genuine original clearance once; each complete Route
is built once on that clearance. The whole Horner cache remains outside this
entry producer and is passed only to the later affine chord constructors.
-/
@[expose] def geometries (budget : OwnerBudget leg coarse limit) (trace : RootTrace leg budget.fine) :
    Geometries trace.readings leg.regular budget.step budget.steps budget.step_paid :=
  Geometries.build trace.readings leg.regular budget.step budget.steps budget.step_paid budget.clearanceAt

/-- The actual retained source attachment agrees with the first identical fine-bank product channel. -/
@[expose] def initialAgreement (budget : OwnerBudget leg coarse limit) (trace : RootTrace leg budget.fine)
    (source : Source leg.source leg.sourcePrepared) :
    NamedEquivalent
      (source.attached.owner.certificate source.attached.owner.parameterNonzero).value.name
      trace.readings.head.lift.value.name := by
  have retained : trace.readings.head = leg.source := trace.source
  exact NamedEquivalent.transport rfl
    (congrArg (fun reading : Reading leg.actual 0 (by decide +kernel) => reading.lift.value.name) retained).symm
    source.agrees.symm

end OwnerBudget

/-- The original finite spatial OwnerPath construction with every actual source, numerical and geometric cache retained.

One common owner-preparation budget is selected before materializing any fine
bank. The unchanged original Leg endpoints, retained whole Horner cache,
actual Source attachment, neighboring Reading/sample/product entries, whole
Edges and sampled Chain remain present. Every later target comparison and
move payment is computed internally from these original data.
-/
@[expose] def OwnerTrace (leg : Leg site parameter quarter) (coarse : Leg.TraceBudget leg)
    (originalSource : Source leg.source leg.sourcePrepared)
    (limit : optParam (Option AccuracyRequest) none) : Type 1 :=
  Σ source : {retained : Source leg.source leg.sourcePrepared // retained = originalSource},
  Σ budget : {retained : OwnerBudget leg coarse limit // retained = OwnerBudget.build leg coarse limit},
  Σ trace : {retained : RootTrace leg budget.val.fine // retained = RootTrace.build leg budget.val.fine},
  Σ geometries : {retained : Geometries trace.val.readings leg.regular
        budget.val.step budget.val.steps budget.val.step_paid //
      retained = budget.val.geometries trace.val},
    {retained : OwnerMoves budget.val 0
        (DyadicTrace.tail budget.val.fine.selection.stage (0 : Fraction.Rational) 1)
        (mesh_inside budget.val.fine.selection.stage) trace.val.readings trace.val.samples trace.val.edges
        budget.val.step budget.val.steps budget.val.step_paid geometries.val
        budget.val.time_paid (budget.val.data_paid trace.val) source.val.attached.owner
        (budget.val.initialAgreement trace.val source.val) //
      retained = OwnerMoves.build budget.val 0
        (DyadicTrace.tail budget.val.fine.selection.stage (0 : Fraction.Rational) 1)
        (mesh_inside budget.val.fine.selection.stage) trace.val.readings trace.val.samples trace.val.edges
        budget.val.step budget.val.steps budget.val.step_paid geometries.val
        budget.val.time_paid (budget.val.data_paid trace.val) source.val.attached.owner
        (budget.val.initialAgreement trace.val source.val)}

namespace OwnerTrace

variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}
variable {originalSource : Source leg.source leg.sourcePrepared}

/-- Build all actual finite spatial owner links from the original Leg and retained complete source attachment. -/
@[expose] def build (leg : Leg site parameter quarter) (coarse : Leg.TraceBudget leg)
    (source : Source leg.source leg.sourcePrepared := Source.build leg.source leg.sourcePrepared)
    (limit : Option AccuracyRequest := none) : OwnerTrace leg coarse source limit :=
  let budget := OwnerBudget.build leg coarse limit
  let trace := RootTrace.build leg budget.fine
  let geometries := budget.geometries trace
  let moves := OwnerMoves.build budget 0 (DyadicTrace.tail budget.fine.selection.stage (0 : Fraction.Rational) 1)
    (mesh_inside budget.fine.selection.stage) trace.readings trace.samples trace.edges
    budget.step budget.steps budget.step_paid geometries budget.time_paid (budget.data_paid trace)
    source.attached.owner (budget.initialAgreement trace source)
  ⟨⟨source, rfl⟩, ⟨budget, rfl⟩, ⟨trace, rfl⟩, ⟨geometries, rfl⟩, ⟨moves, rfl⟩⟩

/-- The omitted cap retains the complete original owner-trace factory and all ordered preparation/move caches. -/
theorem build_default (leg : Leg site parameter quarter) (coarse : Leg.TraceBudget leg)
    (source : Source leg.source leg.sourcePrepared) :
    build leg coarse source none = (
    let budget := OwnerBudget.build leg coarse
    let trace := RootTrace.build leg budget.fine
    let geometries := budget.geometries trace
    let moves := OwnerMoves.build budget 0 (DyadicTrace.tail budget.fine.selection.stage (0 : Fraction.Rational) 1)
      (mesh_inside budget.fine.selection.stage) trace.readings trace.samples trace.edges
      budget.step budget.steps budget.step_paid geometries budget.time_paid (budget.data_paid trace)
      source.attached.owner (budget.initialAgreement trace source)
    ⟨⟨source, rfl⟩, ⟨budget, rfl⟩, ⟨trace, rfl⟩, ⟨geometries, rfl⟩, ⟨moves, rfl⟩⟩
      : OwnerTrace leg coarse source) := rfl

/-- Read the complete original source attachment retained as actual runtime ownership data. -/
@[expose] def source (trace : OwnerTrace leg coarse originalSource limit) : Source leg.source leg.sourcePrepared :=
  trace.1.val

/-- The entire initial attachment remains the supplied original Source rather than a reconstructed owner. -/
theorem source_eq (trace : OwnerTrace leg coarse originalSource limit) : trace.source = originalSource :=
  trace.1.property

/-- Read the actual retained common-frame budget and its internally bounded stronger selection. -/
@[expose] def budget (trace : OwnerTrace leg coarse originalSource limit) : OwnerBudget leg coarse limit :=
  trace.2.1.val

/-- Read the whole original fine Reading/sample/Edge/Chain cache without rebuilding any bank. -/
@[expose] def sampled (trace : OwnerTrace leg coarse originalSource limit) : RootTrace leg trace.budget.fine :=
  trace.2.2.1.val

/-- Read the identical complete original geometry bank used by every actual paid move. -/
@[expose] def geometries (trace : OwnerTrace leg coarse originalSource limit) :
    Geometries trace.sampled.readings leg.regular trace.budget.step trace.budget.steps trace.budget.step_paid :=
  trace.2.2.2.1.val

/-- Read every retained actual preparation, paid move, residual comparison and link in its original order. -/
@[expose] def moves (trace : OwnerTrace leg coarse originalSource limit) :
    OwnerMoves trace.budget 0
      (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
      (mesh_inside trace.budget.fine.selection.stage) trace.sampled.readings trace.sampled.samples trace.sampled.edges
      trace.budget.step trace.budget.steps trace.budget.step_paid trace.geometries
      trace.budget.time_paid (trace.budget.data_paid trace.sampled) trace.source.attached.owner
      (trace.budget.initialAgreement trace.sampled trace.source) := trace.2.2.2.2.val

/-- The original sampled Chain keeps its exact finite number of selected chart edges. -/
theorem count (trace : OwnerTrace leg coarse originalSource limit) :
    trace.sampled.samples.tail.values.length = 2 ^ trace.budget.fine.selection.stage := trace.sampled.count

/-- Read the actual final spatial owner from the retained original moves, performing no additional continuation. -/
@[expose] def finish (trace : OwnerTrace leg coarse originalSource limit) :
    Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel)
        (DyadicTrace.terminal 0 (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)))) :=
  trace.moves.finish

/-- The same exact actual owners, cached joins and cached links produce the original all-future OwnerPath. -/
@[expose] def path (trace : OwnerTrace leg coarse originalSource limit) :
    OwnerPath (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) 0) trace.source.attached.owner
      (coordinate site parameter 2 quarter (by decide +kernel)
        (DyadicTrace.terminal 0 (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)))
      trace.finish := trace.moves.path

/-- Reindex the actual final owner at the original exact quarter target using only the computed terminal-time law. -/
@[expose] def finishAtTarget (trace : OwnerTrace leg coarse originalSource limit) :
    Owner ((Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) 1)) :=
  Transport.castOwnerParameter
    (congrArg (fun time => (Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) time))
      (DyadicTrace.tail_terminal trace.budget.fine.selection.stage 0 1)) trace.finish

/-- The exact target-index view retains the whole actual moved owner, including its original track and caches. -/
theorem finishAtTarget_heq (trace : OwnerTrace leg coarse originalSource limit) :
    HEq trace.finishAtTarget trace.finish := Transport.castOwnerParameter_heq _ _

/-- The original OwnerPath ends at the exact retained quarter target without constructing another owner or path. -/
@[expose] def pathAtTarget (trace : OwnerTrace leg coarse originalSource limit) :
    OwnerPath (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) 0) trace.source.attached.owner
      (coordinate site parameter 2 quarter (by decide +kernel) 1) trace.finishAtTarget :=
  OwnerPath.castEndpoints rfl
    (congrArg (coordinate site parameter 2 quarter (by decide +kernel))
      (DyadicTrace.tail_terminal trace.budget.fine.selection.stage 0 1))
    (HEq.refl _) trace.finishAtTarget_heq.symm trace.path

/-- The actual continued full-quarter finish agrees with the same original independently retained target Reading.

The comparison is read from the original sequential cache fold. Exact
terminal-time and complete target-Reading identities transport only its two
displayed names, retaining its actual comparison procedure, observations,
selected stages and request payments.
-/
@[expose] def targetAgreement (trace : OwnerTrace leg coarse originalSource limit) :
    NamedEquivalent
      (trace.finishAtTarget.certificate trace.finishAtTarget.parameterNonzero).value.name
      leg.target.lift.value.name :=
  NamedEquivalent.transport
    (SquareRootTrackEquivalence.ownerRootName_castOwnerParameter
      (congrArg (fun time => (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) time))
        (DyadicTrace.tail_terminal trace.budget.fine.selection.stage 0 1)) trace.finish).symm
    trace.sampled.target_name trace.moves.agreement

/-- The same original whole-quarter owner trace and its once-built compared spatial blocks.

The existing Sigma retains the complete supplied OwnerTrace literally,
including its original readings, geometries, sample bank, moves and signed
target comparisons. The existing subtype retains the entire original Blocks
result and its whole factory equation. The original affine builder and its
complete results are unchanged; this operation materializes spatial covers.
-/
@[expose] def Covered (original : OwnerTrace leg coarse originalSource limit) : Type 1 :=
  Σ trace : {retained : OwnerTrace leg coarse originalSource limit // retained = original},
    {blocks : CoveredTracedPath.Blocks (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) 0) trace.val.source.attached.owner
      (coordinate site parameter 2 quarter (by decide +kernel)
        (DyadicTrace.terminal 0 (DyadicTrace.tail trace.val.budget.fine.selection.stage (0 : Fraction.Rational) 1)))
      trace.val.finish // blocks = trace.val.moves.spatialBlocks}

/-- Materialize compared spatial covers once from the unchanged whole original owner-trace caches. -/
@[expose] def cover (original : OwnerTrace leg coarse originalSource limit) : Covered original :=
  let blocks := original.moves.spatialBlocks
  ⟨⟨original, rfl⟩, ⟨blocks, rfl⟩⟩

namespace Covered

variable {original : OwnerTrace leg coarse originalSource limit}

/-- Read the identical complete original owner trace retained beside the spatial cover. -/
@[expose] def trace (covered : Covered original) : OwnerTrace leg coarse originalSource limit := covered.1.val

/-- The retained owner trace is the whole supplied original value, including every numerical cache. -/
theorem trace_eq (covered : Covered original) : covered.trace = original := covered.1.property

/-- Read the complete original compared block cache, ending on the very same final affine owner. -/
@[expose] def blocks (covered : Covered original) : CoveredTracedPath.Blocks (Paths.polynomial parameter)
    (coordinate site parameter 2 quarter (by decide +kernel) 0) covered.trace.source.attached.owner
    (coordinate site parameter 2 quarter (by decide +kernel)
      (DyadicTrace.terminal 0 (DyadicTrace.tail covered.trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)))
    covered.trace.finish := covered.2.val

/-- The complete retained block cache is the original fold of the same actual affine moves. -/
theorem blocks_eq (covered : Covered original) : covered.blocks = covered.trace.moves.spatialBlocks :=
  covered.2.property

/-- The compared cover keeps one geometric block per selected edge and retains all actual stationary payments. -/
theorem count (covered : Covered original) : covered.blocks.length = 2 ^ covered.trace.budget.fine.selection.stage := by
  rewrite [covered.blocks_eq]
  exact covered.trace.moves.spatialBlocks_length.trans
    (DyadicSteps.tail_length covered.trace.budget.fine.selection.stage 0 1)

/-- Reindex the same compared spatial blocks at the original exact quarter target.

Only the computed terminal-time equality transports the existing indices.
The cached affine final owner is exactly the original finishAtTarget view;
no root name, target owner, covered preparation or handoff is reconstructed.
-/
@[expose] def blocksAtTarget (covered : Covered original) : CoveredTracedPath.Blocks (Paths.polynomial parameter)
    (coordinate site parameter 2 quarter (by decide +kernel) 0) covered.trace.source.attached.owner
    (coordinate site parameter 2 quarter (by decide +kernel) 1) covered.trace.finishAtTarget :=
  covered.blocks.castEndpoints rfl
    (congrArg (coordinate site parameter 2 quarter (by decide +kernel))
      (DyadicTrace.tail_terminal covered.trace.budget.fine.selection.stage 0 1))
    (HEq.refl _) covered.trace.finishAtTarget_heq.symm

/-- Exact quarter-target transport preserves the geometric block count and every separate comparison payment. -/
theorem blocksAtTarget_length (covered : Covered original) :
    covered.blocksAtTarget.length = 2 ^ covered.trace.budget.fine.selection.stage :=
  (CoveredTracedPath.Blocks.castEndpoints_length _ _ _ _ covered.blocks).trans covered.count

/-- The same whole fine OwnerTrace and Blocks, with their original requested spatial primitive bank on an actual curve.

The supplied original curve has the exact displayed defining polynomial.
Polynomial transport changes only dependent indices; the complete original
covered trace and actual owner joins remain retained runtime data.
-/
@[expose] def PrimitiveRequest (covered : Covered original) {genus : Nat} (curve : HyperellipticCurve genus)
    (presentation : curve.polynomial = Paths.polynomial parameter) (differential : Differential genus)
    (sheet : Fin 2) (accuracy : Fraction.Rational) : Type 2 :=
  Σ retained : {retained : Covered original // retained = covered},
    CoveredTracedPath.Blocks.PrimitiveRequest (retained.val.blocksAtTarget.castPolynomial presentation.symm)
      differential sheet accuracy

/-- Prepare actual spatial primitive requests while retaining this identical complete fine trace and its stored Blocks.

Original ParentCache coverage supplies every local domain and sheet condition;
the existing PrimitiveSumRequest computes and retains its actual finite
accuracy schedule, children, primitive values and numerical integral.
-/
@[expose] def primitiveRequest (covered : Covered original) {genus : Nat} (curve : HyperellipticCurve genus)
    (presentation : curve.polynomial = Paths.polynomial parameter) (differential : Differential genus)
    (sheet : Fin 2) (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    PrimitiveRequest covered curve presentation differential sheet accuracy :=
  let blocks := covered.blocksAtTarget.castPolynomial presentation.symm
  let request := blocks.primitiveRequest differential sheet accuracy positive
  ⟨⟨covered, rfl⟩, request⟩

namespace PrimitiveRequest

/-- The retained numerical primitive bank keeps the complete same original Blocks across exact polynomial reindexing. -/
theorem blocks_heq {covered : Covered original} {genus : Nat} {curve : HyperellipticCurve genus}
    {presentation : curve.polynomial = Paths.polynomial parameter} {differential : Differential genus}
    {sheet : Fin 2} {accuracy : Fraction.Rational}
    (request : Covered.PrimitiveRequest covered curve presentation differential sheet accuracy) :
    HEq request.2.1.val request.1.val.blocksAtTarget :=
  (heq_of_eq request.2.1.property).trans (request.1.val.blocksAtTarget.castPolynomial_heq presentation.symm)

end PrimitiveRequest

end Covered

section PrimitivePieces

open Purelib.Algebra.Quadratic (Pair)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Piece Layer)

variable {clearance : OwnerBudget.SourceClearance leg}
variable (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
variable {radicand : Pair.Polynomial.Coefficients} {differential : OddPowerDifferential radicand}
variable {data : WaistBounds site parameter differential} {accuracy : AccuracyRequest}
variable {initial : Piece data leg.actual accuracy} {count : Nat}

/-- A structural ordinal view of the same retained chart primitives and original scalar pieces.

The subtype retains the actual whole primitive and Piece at every bounded
occurrence. Its count follows from the supplied Layer and original dyadic
tail law. This view asserts no interval correspondence between those two
objects; that geometric statement requires their original span laws.
-/
@[expose] def PrimitivePieces
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves)
    (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) :=
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  let same : scalar.pieces.length = times.length :=
    scalar.count.trans (DyadicSteps.tail_length trace.budget.fine.selection.stage 0 1).symm
  {rows : DependentProduct times (fun edge =>
      OwnerMove.PrimitiveTarget.Anchored bounds (bank.get edge).2.2 count ×
        Piece data leg.actual scalar.accuracy) //
    ∀ edge : Fin times.length, DependentProduct.get times rows edge =
      (retained.get bounds edge, scalar.pieces[edge.val]'(same.symm ▸ edge.isLt))}

/-- Pair actual cached chart primitives and actual scalar pieces by one structural traversal of their supplied values.

The equal-count list view allocates one product spine, then the original
zipWith consumes both actual heads and literal tails. The paired view
allocates a second spine and forwards whole cached values. No primitive,
Point, Reading, source preparation, model or programme is recomputed.
-/
def primitivePieces
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves)
    (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) :
    PrimitivePieces bounds trace bank retained scalar := by
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  have same : scalar.pieces.length = times.length :=
    scalar.count.trans (DyadicSteps.tail_length trace.budget.fine.selection.stage 0 1).symm
  let pieces := DependentProduct.ofList times scalar.pieces same
  let rows := DependentProduct.zipWith times retained pieces
    (fun edge => OwnerMove.PrimitiveTarget.Anchored bounds (bank.get edge).2.2 count ×
      Piece data leg.actual scalar.accuracy)
    (fun _ primitive piece _ _ => (primitive, piece))
  refine ⟨rows, ?_⟩
  intro edge
  dsimp only [rows]
  rewrite [DependentProduct.get_zipWith]
  exact congrArg (fun piece => (retained.get bounds edge, piece))
    (DependentProduct.get_ofList times scalar.pieces same edge)

end PrimitivePieces

end OwnerTrace

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
