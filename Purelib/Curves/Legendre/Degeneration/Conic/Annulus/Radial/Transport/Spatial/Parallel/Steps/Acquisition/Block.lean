module
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Geometry.Rational.Box.Point
import Purelib.Geometry.Rational.Box.Hull

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison.Initial.Endpoint
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps
public import Purelib.Riemann.RootContinuation.ClearBoxRootTransport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Blocks
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Polynomial.Geometry.Grid.Winding
import Purelib.Tactic.QuotientFreeOmega

/-! # One paid spatial block on an unchanged original-quarter query pair

The exact original Geometry and target QueryCache are inputs. An original
Anchor, factor budgets, factor Route, paid Covered execution, comparison and
independent-target Endpoint are computed once and retained in order. The
next source agreement is stored once on that exact covered finishOwner.
Neither the original-quarter queries nor a Source attachment are rebuilt.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Riemann.Paths.PreparedPathWinding.PreparedClearPathModels
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison

namespace Steps.Acquisition

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 unitQuarter positive}
variable {regular : parameter ≠ criticalValue site}
/-- The exact initial compatibility type of a retained quarter Reading and one original full-cubic Owner.

The alias preserves both nominal inputs and the complete Type-valued
operational comparison; it introduces no replacement root certificate.
-/
@[expose] def InitialAgreement (current : Endpoint) (reading : ReadingAt actual current)
    (owner : OwnerAt site parameter unitQuarter positive current) :=
  NamedEquivalent reading.lift.value.name (ownerRootName owner.parameterNonzero owner)

variable {current target : Endpoint} {reading : ReadingAt actual current}
variable (queried : { retained : ReadingAt actual target // QueryCache actual target retained })
variable {payment : (target.parameter - current.parameter) ^ 2 ≤
  Approximation.Rational.Geometric.Basic.quarterRadius 1 7}
variable (geometry : Geometry reading queried.val regular payment)
variable (sourceOwner : OwnerAt site parameter unitQuarter positive current)
variable (sourceAgreement : InitialAgreement current reading sourceOwner)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The exact retained original source Anchor is constructed on the unchanged supplied Reading's Lift. -/
@[irreducible, expose] def AnchorCache (anchor : Parameter.Anchor reading.lift) : Prop :=
  anchor = Parameter.Anchor.build reading.lift regular actual.data.bound

/-- The whole original factor-budget cache is the once-computed factory on the identical retained Anchor. -/
@[irreducible, expose] def BudgetsCache (anchor : Parameter.Anchor reading.lift)
    (budgets : Factors.Budgets (source := reading) anchor) : Prop :=
  budgets = Factors.Budgets.build (source := reading) anchor

/-- The complete physical factor Route belongs to the original supplied Geometry without rebuilding its spatial path. -/
@[irreducible, expose] def FactorsCache {anchor : Parameter.Anchor reading.lift}
    (budgets : Factors.Budgets (source := reading) anchor) (factors : Factors.Route budgets geometry) : Prop :=
  factors = Factors.Route.build budgets geometry

/-- The paid Covered cache is the exact new route acquisition on the supplied nominal full-cubic source Owner. -/
@[irreducible, expose] def PaidCache {anchor : Parameter.Anchor reading.lift}
    {budgets : Factors.Budgets (source := reading) anchor}
    (factors : Factors.Route budgets geometry) (paid : Factors.Route.Acquisition factors sourceOwner) : Prop :=
  paid = Factors.Route.Acquisition.build factors sourceOwner

/-- The actual supplied-owner comparison consumes the identical original factor and paid-execution caches. -/
@[irreducible, expose] def ComparisonCache
    {anchor : Parameter.Anchor reading.lift} {budgets : Factors.Budgets (source := reading) anchor}
    {factors : Factors.Route budgets geometry} (paid : Factors.Route.Acquisition factors sourceOwner)
    (compared : Initial.Result (geometry := geometry)
      (Comparison.Initial.ofOwner (source := reading) sourceOwner sourceAgreement) paid) : Prop :=
  compared = Initial.Result.build (geometry := geometry)
    (Comparison.Initial.ofOwner (source := reading) sourceOwner sourceAgreement) paid

/-- The complete independent-target Endpoint retains its original comparison factory on the same actual paid Result. -/
@[irreducible, expose] def EndpointCache
    {anchor : Parameter.Anchor reading.lift} {budgets : Factors.Budgets (source := reading) anchor}
    {factors : Factors.Route budgets geometry} {paid : Factors.Route.Acquisition factors sourceOwner}
    (compared : Initial.Result (geometry := geometry)
      (Comparison.Initial.ofOwner (source := reading) sourceOwner sourceAgreement) paid)
    (endpoint : Initial.Result.Endpoint (geometry := geometry)
      (Comparison.Initial.ofOwner (source := reading) sourceOwner sourceAgreement) compared) : Prop :=
  endpoint = Initial.Result.Endpoint.build (geometry := geometry)
    (Comparison.Initial.ofOwner (source := reading) sourceOwner sourceAgreement) compared

/-- One actual paid block retains all complete original factories and its derived next-source agreement.

The target Reading and Geometry remain unchanged supplied objects. The
covered acquisition is new and indexed by the supplied actual sourceOwner.
Its exact stored finishOwner indexes both the retained Endpoint and the
next agreement, which stays Type-valued operational comparison data.
-/
@[expose] def Block :=
  Σ anchor : { retained : Parameter.Anchor reading.lift // AnchorCache (regular := regular) retained },
    Σ budgets : { retained : Factors.Budgets (source := reading) anchor.val // BudgetsCache anchor.val retained },
      Σ factors : { retained : Factors.Route budgets.val geometry //
          FactorsCache queried geometry budgets.val retained },
        Σ paid : { retained : Factors.Route.Acquisition factors.val sourceOwner //
            PaidCache queried geometry sourceOwner factors.val retained },
          Σ compared : { retained : Initial.Result (geometry := geometry)
                (Comparison.Initial.ofOwner (source := reading) sourceOwner sourceAgreement) paid.val //
              ComparisonCache queried geometry sourceOwner sourceAgreement paid.val retained },
            Σ endpoint : { retained : Initial.Result.Endpoint (geometry := geometry)
                  (Comparison.Initial.ofOwner (source := reading) sourceOwner sourceAgreement) compared.val //
                EndpointCache queried geometry sourceOwner sourceAgreement compared.val retained },
              { following : NamedEquivalent queried.val.lift.value.name
                  (ownerRootName paid.val.finishOwner.parameterNonzero paid.val.finishOwner) //
                following = endpoint.val.finish.symm }

namespace Block

/-- Retain completed original block caches and the exact next-source witness without replaying their factories. -/
@[expose] def ofCompleted
    (anchor : { retained : Parameter.Anchor reading.lift // AnchorCache (regular := regular) retained })
    (budgets : { retained : Factors.Budgets (source := reading) anchor.val // BudgetsCache anchor.val retained })
    (factors : { retained : Factors.Route budgets.val geometry // FactorsCache queried geometry budgets.val retained })
    (paid : { retained : Factors.Route.Acquisition factors.val sourceOwner //
      PaidCache queried geometry sourceOwner factors.val retained })
    (compared : { retained : Initial.Result (geometry := geometry)
        (Comparison.Initial.ofOwner (source := reading) sourceOwner sourceAgreement) paid.val //
      ComparisonCache queried geometry sourceOwner sourceAgreement paid.val retained })
    (endpoint : { retained : Initial.Result.Endpoint (geometry := geometry)
        (Comparison.Initial.ofOwner (source := reading) sourceOwner sourceAgreement) compared.val //
      EndpointCache queried geometry sourceOwner sourceAgreement compared.val retained })
    (following : { retained : InitialAgreement target queried.val paid.val.finishOwner //
      retained = endpoint.val.finish.symm }) : Block queried geometry sourceOwner sourceAgreement :=
  ⟨anchor, budgets, factors, paid, compared, endpoint, following⟩

/-- Construct one paid block from the original query pair and Geometry, retaining every complete factory result once. -/
def build : Block queried geometry sourceOwner sourceAgreement :=
  let anchor := Parameter.Anchor.build reading.lift regular actual.data.bound
  let budgets := Factors.Budgets.build (source := reading) anchor
  let factors := Factors.Route.build budgets geometry
  let paid := Factors.Route.Acquisition.build factors sourceOwner
  let initial := Comparison.Initial.ofOwner (source := reading) sourceOwner sourceAgreement
  let compared := Initial.Result.build (geometry := geometry) initial paid
  let endpoint := Initial.Result.Endpoint.build (geometry := geometry) initial compared
  let following := endpoint.finish.symm
  ofCompleted queried geometry sourceOwner sourceAgreement
    ⟨anchor, by unfold AnchorCache; rfl⟩ ⟨budgets, by unfold BudgetsCache; rfl⟩
    ⟨factors, by unfold FactorsCache; rfl⟩ ⟨paid, by unfold PaidCache; rfl⟩
    ⟨compared, by unfold ComparisonCache; rfl⟩ ⟨endpoint, by unfold EndpointCache; rfl⟩ ⟨following, rfl⟩

variable {queried : { retained : ReadingAt actual target // QueryCache actual target retained }}
variable {geometry : Geometry reading queried.val regular payment}
variable {sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {sourceAgreement : InitialAgreement current reading sourceOwner}
variable (block : Block queried geometry sourceOwner sourceAgreement)

/-- Read the identical complete original known-normalized-root Anchor cached for this source Reading. -/
@[expose] def anchor : Parameter.Anchor reading.lift := block.1.val

/-- Read the identical whole original factor budgets without acquiring them again. -/
@[expose] def budgets : Factors.Budgets (source := reading) block.anchor := block.2.1.val

/-- Read the unchanged complete physical factor Route on the supplied original Geometry. -/
@[expose] def factors : Factors.Route block.budgets geometry := block.2.2.1.val

/-- Read the complete actual new paid Covered acquisition on this block's unchanged supplied source Owner. -/
@[expose] def paid : Factors.Route.Acquisition block.factors sourceOwner := block.2.2.2.1.val

/-- Read the exact supplied-owner compatibility view over the unchanged source Owner and complete input comparison. -/
@[expose] def initial (_block : Block queried geometry sourceOwner sourceAgreement) : Comparison.Initial reading :=
  Comparison.Initial.ofOwner (source := reading) sourceOwner sourceAgreement

/-- Read the whole original actual paid comparison, including its complete factor observations and corner caches. -/
@[expose] def comparison : Initial.Result (geometry := geometry) block.initial block.paid :=
  block.2.2.2.2.1.val

/-- Read the retained independent-target Endpoint on that same actual paid comparison and original target Lift. -/
@[expose] def endpoint : Initial.Result.Endpoint (geometry := geometry) block.initial block.comparison :=
  block.2.2.2.2.2.1.val

/-- Read the identical stored actual finishOwner of this particular new paid Covered execution. -/
@[expose] def finishOwner : OwnerAt site parameter unitQuarter positive target := block.paid.finishOwner

/-- Read the once-computed next-source relation on the exact target Reading and this literal stored finishOwner. -/
@[expose] def nextAgreement : InitialAgreement target queried.val block.finishOwner := block.2.2.2.2.2.2.val

/-- The cached source Anchor is the original factory on the identical Lift and original quarter's radius admission. -/
theorem anchor_eq : block.anchor = Parameter.Anchor.build reading.lift regular actual.data.bound := by
  have retained := block.1.property
  unfold AnchorCache at retained
  exact retained

/-- The whole budget cache is the original once-computed factory on the same actual Anchor. -/
theorem budgets_eq : block.budgets = Factors.Budgets.build (source := reading) block.anchor := by
  have retained := block.2.1.property
  unfold BudgetsCache at retained
  exact retained

/-- The whole factor Route cache is the original factory on the unchanged actual Geometry and retained budgets. -/
theorem factors_eq : block.factors = Factors.Route.build block.budgets geometry := by
  have retained := block.2.2.1.property
  unfold FactorsCache at retained
  exact retained

/-- The whole paid Covered cache belongs to the original acquisition factory on the exact supplied source Owner. -/
theorem paid_eq : block.paid = Factors.Route.Acquisition.build block.factors sourceOwner := by
  have retained := block.2.2.2.1.property
  unfold PaidCache at retained
  exact retained

/-- The whole comparison cache is the original supplied-owner factory on the identical entry and paid execution. -/
theorem comparison_eq :
    block.comparison = Initial.Result.build (geometry := geometry) block.initial block.paid := by
  have retained := block.2.2.2.2.1.property
  unfold ComparisonCache at retained
  exact retained

/-- The complete Endpoint cache is the actual independent-target factory on the same retained Result. -/
theorem endpoint_eq :
    block.endpoint = Initial.Result.Endpoint.build (geometry := geometry)
      block.initial block.comparison := by
  have retained := block.2.2.2.2.2.1.property
  unfold EndpointCache at retained
  exact retained

/-- The stored next-source witness is exactly the original paid Endpoint's finishing comparison reversed. -/
theorem nextAgreement_eq : block.nextAgreement = block.endpoint.finish.symm := block.2.2.2.2.2.2.property

/-- The target is the unchanged complete original-quarter query authenticated by its supplied QueryCache. -/
theorem target_eq (_block : Block queried geometry sourceOwner sourceAgreement) :
    queried.val = Reading.build actual target.parameter target.inside :=
  QueryCache.readback queried.property

/-- The particular stored paid finishOwner agrees with the original independent target Lift. -/
def finishEquivalent : NamedEquivalent
    (ownerRootName block.finishOwner.parameterNonzero block.finishOwner) queried.val.lift.value.name :=
  block.endpoint.finish

section Detour

open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Winding.Polygon.Basic (chainRaw)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Riemann.Paths
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.ClearBoxPathWinding.ClearBoxPaths (windingPotential)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)

/-- An actual alternative initial Owner and its retained comparison to the original paid start.

The ordinary dependent pair keeps both original Owners and the same
Type-valued comparison supplied by the preceding retained execution.
It is not a new root owner or a successful final detour comparison.
-/
abbrev Start (original : OwnerAt site parameter unitQuarter positive current) :=
  Σ actual : OwnerAt site parameter unitQuarter positive current,
    NamedEquivalent (ownerName actual) (ownerName original)

namespace Start

/-- Read the actual supplied initial Owner, retaining the historical Owner when no alternative is supplied. -/
@[expose] def owner (original : OwnerAt site parameter unitQuarter positive current) :
    Option (Start original) → OwnerAt site parameter unitQuarter positive current
  | none => original
  | some supplied => supplied.1

/-- Read the same stored source relation, using reflexivity only for the historical default start. -/
def equivalent (original : OwnerAt site parameter unitQuarter positive current)
    (supplied : Option (Start original)) :
    NamedEquivalent (ownerName (owner original supplied)) (ownerName original) :=
  match supplied with
  | none => NamedEquivalent.refl _
  | some value => value.2

end Start

variable {degreeBound : Nat} {ambient : Box}
variable {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
variable {clearances : AxisClearances elimination}
variable {firstAmbient : (Geometry.neighborhood site parameter regular
  (coordinate site parameter 2 unitQuarter positive current.parameter)).Refines ambient}
variable {lastAmbient : (Geometry.neighborhood site parameter regular
  (coordinate site parameter 2 unitQuarter positive target.parameter)).Refines ambient}
variable (source : Geometry.Lines elimination clearances regular
  (coordinate site parameter 2 unitQuarter positive current.parameter) firstAmbient)
variable (targetLines : Geometry.Lines elimination clearances regular
  (coordinate site parameter 2 unitQuarter positive target.parameter) lastAmbient)
variable {grid : ClearGrid (Paths.polynomial parameter) ambient}
variable {sourceOn : FromStates.ContainsVertex grid source.point}
variable {targetOn : FromStates.ContainsVertex grid targetLines.point}

/-- Compare the actual connector-walk-connector finish with the original paid block finish.

The middle cover belongs to the literal retained numeric Walk, endpoint-cast
using its same paired-line readbacks. Both connector covers keep their actual
inherited root Owners. Potential differences on the original cleared square
telescope to the old route's winding, and its retained paid trace determines
the endpoint comparison. The reference is retained either at the unchanged
source or at the actual moved grid vertex. The latter branch derives its
reverse-entry handoff internally; no off-grid reference is assumed. This
does not identify the paths or their integrals. The actual supplied start
Owner remains separate from the old paid start; its stored comparison only
joins their original names in the endpoint proof.
-/
def detourEquivalent
    (reference : WindingOneLoop (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) ⊕
      WindingOneLoop (Paths.polynomial parameter) source.point)
    (sourceInside : (box site parameter unitQuarter current.parameter regular).Contains source.point)
    (targetInside : (box site parameter unitQuarter current.parameter regular).Contains targetLines.point)
    (walk : {value : Walks.Walk grid
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive target.parameter)) //
      value = geometry.detourWalk elimination clearances source targetLines grid sourceOn targetOn})
    (entry : ClearBoxPaths.Route (Paths.polynomial parameter)
      (box site parameter unitQuarter current.parameter regular)
      (coordinate site parameter 2 unitQuarter positive current.parameter) source.point)
    (returned : ClearBoxPaths.Route (Paths.polynomial parameter)
      (box site parameter unitQuarter current.parameter regular) targetLines.point
      (coordinate site parameter 2 unitQuarter positive target.parameter))
    {actualSource : OwnerAt site parameter unitQuarter positive current}
    (first : CoveredTracedPath entry.path actualSource)
    (middle : CoveredTracedPath
      (walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm).path first.traced.finishOwner)
    (last : CoveredTracedPath returned.path middle.traced.finishOwner)
    (sourceEquivalent : NamedEquivalent (ownerName actualSource) (ownerName sourceOwner)) :
    NamedEquivalent (ownerName last.traced.finishOwner) (ownerName block.finishOwner) := by
  cases reference with
  | inl reference =>
    let physical := block.paid.covered.traced
    let joined := (RootPathTransport.OwnerPath.join (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) sourceOwner actualSource
      sourceEquivalent.symm).append
      (first.traced.trace.get.append (middle.traced.trace.get.append last.traced.trace.get))
    have degreePositive : 0 < (Paths.polynomial parameter).natDegree := by
      rewrite [Paths.polynomial_natDegree]
      decide
    have initialInside : (box site parameter unitQuarter current.parameter regular).Contains
        (coordinate site parameter 2 unitQuarter positive current.parameter) :=
      source_inside (positive := positive) regular
    have firstWinding := ClearBoxPathWinding.Route.winding geometry.clearance degreePositive entry initialInside
    have lastWinding := ClearBoxPathWinding.Route.winding geometry.clearance degreePositive returned targetInside
    have oldWinding := ClearBoxPathWinding.Route.winding geometry.clearance degreePositive geometry.route
      initialInside
    have movedWinding := ClearBoxPathWinding.Route.winding geometry.clearance degreePositive
      (geometry.detour elimination clearances source targetLines) sourceInside
    have middleWinding : PreparedPathWinding.ClearPath.rawWinding
        (walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm).path =
        PreparedPathWinding.ClearPath.rawWinding
          (geometry.detour elimination clearances source targetLines).path := by
      rewrite [Winding.Walk.castEndpoints_winding, walk.property]
      exact geometry.detourWalk_winding elimination clearances source targetLines grid sourceOn targetOn
    have winding : PreparedPathWinding.ClearPath.rawWinding geometry.route.path =
        chainRaw (Paths.polynomial parameter)
          (coordinate site parameter 2 unitQuarter positive current.parameter) joined.vertices := by
      dsimp only [joined]
      rewrite [RootPathTransport.OwnerPath.append_winding, RootPathTransport.OwnerPath.join_winding,
        Data.Int.Arithmetic.zero_add, RootPathTransport.OwnerPath.append_winding,
        RootPathTransport.OwnerPath.append_winding,
        TracedPath.winding_original first.traced,
        TracedPath.winding_original middle.traced,
        TracedPath.winding_original last.traced,
        middleWinding, firstWinding, movedWinding, lastWinding, oldWinding]
      omega0
    let frame := OwnerFrame.build block.finishOwner.parameterNonzero
    exact (ClearBoxRootTransport.TracedPath.equivalentOfOwnerPathSelections reference geometry.route.within
      physical joined frame (frame.select physical.finishOwner) (frame.select last.traced.finishOwner) winding).symm
  | inr reference =>
    let physical := block.paid.covered.traced
    let frame := OwnerFrame.build block.finishOwner.parameterNonzero
    let left := frame.select physical.finishOwner
    let right := frame.select last.traced.finishOwner
    have same : left.index = right.index := by
      let back := PreparedPathTrace.TracedPath.build (BranchCutLifts.ClearPath.reverse entry.path)
        (BranchCutLifts.ClearPath.reverse_withinAmbient entry.path entry.within) first.traced.finishOwner
      let returnedOwner := (ClearBoxRootTransport.TracedPath.reverseEquivalentFromFinish
        reference entry.within first.traced back).trans sourceEquivalent
      let original := back.trace.get.append
        ((RootPathTransport.OwnerPath.join (Paths.polynomial parameter)
          (coordinate site parameter 2 unitQuarter positive current.parameter) back.finishOwner sourceOwner
          returnedOwner).append physical.trace.get)
      let moved := middle.traced.trace.get.append last.traced.trace.get
      have degreePositive : 0 < (Paths.polynomial parameter).natDegree := by
        rewrite [Paths.polynomial_natDegree]
        decide
      have initialInside : (box site parameter unitQuarter current.parameter regular).Contains
          (coordinate site parameter 2 unitQuarter positive current.parameter) :=
        source_inside (positive := positive) regular
      let comparisonRoute := ClearBoxPaths.Route.build geometry.clearance source.point
        (coordinate site parameter 2 unitQuarter positive target.parameter) sourceInside
        (target_inside (positive := positive) regular payment)
      let comparison := PreparedPathTrace.TracedPath.build comparisonRoute.path comparisonRoute.within
        first.traced.finishOwner
      let selected := frame.select comparison.finishOwner
      have firstWinding := ClearBoxPathWinding.Route.winding geometry.clearance degreePositive entry initialInside
      have lastWinding := ClearBoxPathWinding.Route.winding geometry.clearance degreePositive returned targetInside
      have oldWinding := ClearBoxPathWinding.Route.winding geometry.clearance degreePositive geometry.route
        initialInside
      have movedWinding := ClearBoxPathWinding.Route.winding geometry.clearance degreePositive
        (geometry.detour elimination clearances source targetLines) sourceInside
      have comparisonWinding := ClearBoxPathWinding.Route.winding geometry.clearance degreePositive
        comparisonRoute sourceInside
      have middleWinding : PreparedPathWinding.ClearPath.rawWinding
          (walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm).path =
          PreparedPathWinding.ClearPath.rawWinding
            (geometry.detour elimination clearances source targetLines).path := by
        rewrite [Winding.Walk.castEndpoints_winding, walk.property]
        exact geometry.detourWalk_winding elimination clearances source targetLines grid sourceOn targetOn
      let potential := ClearBoxPathWinding.ClearBoxPaths.windingPotential (Paths.polynomial parameter)
        (box site parameter unitQuarter current.parameter regular)
      let originalPoint := coordinate site parameter 2 unitQuarter positive current.parameter
      let finalPoint := coordinate site parameter 2 unitQuarter positive target.parameter
      have originalWinding : PreparedPathWinding.ClearPath.rawWinding comparisonRoute.path =
          chainRaw (Paths.polynomial parameter) source.point original.vertices := by
        dsimp only [original]
        rewrite [RootPathTransport.OwnerPath.append_winding, RootPathTransport.OwnerPath.append_winding,
          RootPathTransport.OwnerPath.join_winding,
          TracedPath.winding_original back,
          PreparedPathClosure.ClearPath.rawWinding_reverse,
          TracedPath.winding_original physical]
        have values : -PreparedPathWinding.ClearPath.rawWinding entry.path +
            (0 + PreparedPathWinding.ClearPath.rawWinding geometry.route.path) =
            -(potential source.point - potential originalPoint) +
              (0 + (potential finalPoint - potential originalPoint)) :=
          (congrArg (fun value : Int => -value +
            (0 + PreparedPathWinding.ClearPath.rawWinding geometry.route.path)) firstWinding).trans
            (congrArg (fun value : Int => -(potential source.point - potential originalPoint) + (0 + value))
              oldWinding)
        have scalar (first last moved : Int) : last - moved = -(moved - first) + (0 + (last - first)) := by
          omega0
        exact comparisonWinding.trans
          ((scalar (potential originalPoint) (potential finalPoint) (potential source.point)).trans values.symm)
      have movedValue : PreparedPathWinding.ClearPath.rawWinding comparisonRoute.path =
          chainRaw (Paths.polynomial parameter) source.point moved.vertices := by
        dsimp only [moved]
        rewrite [RootPathTransport.OwnerPath.append_winding,
          TracedPath.winding_original middle.traced,
          TracedPath.winding_original last.traced,
          middleWinding]
        have values : PreparedPathWinding.ClearPath.rawWinding
              (geometry.detour elimination clearances source targetLines).path +
            PreparedPathWinding.ClearPath.rawWinding returned.path =
            (potential targetLines.point - potential source.point) +
              (potential finalPoint - potential targetLines.point) :=
          (congrArg (fun value : Int => value + PreparedPathWinding.ClearPath.rawWinding returned.path)
            movedWinding).trans
            (congrArg (fun value : Int => (potential targetLines.point - potential source.point) + value)
              lastWinding)
        have scalar (first middle last : Int) : last - first = (middle - first) + (last - middle) := by
          omega0
        exact comparisonWinding.trans
          ((scalar (potential source.point) (potential targetLines.point) (potential finalPoint)).trans values.symm)
      have oldIndex := ClearBoxRootTransport.TracedPath.selection_eq_of_ownerPath reference
        comparisonRoute.within comparison original frame selected left originalWinding
      have movedIndex := ClearBoxRootTransport.TracedPath.selection_eq_of_ownerPath reference
        comparisonRoute.within comparison moved frame selected right movedValue
      exact oldIndex.symm.trans movedIndex
    exact (left.equivalent.trans (by
      rewrite [same]
      exact right.equivalent.symm)).symm

/-- Prepare the entry, retained numeric Walk and return once, storing their actual endpoint comparison.

Each original covered-path result carries its complete factory equality.
The second and third preparations inherit the actual preceding finish Owner;
the old Block and all original paid caches remain unchanged inputs. Supplied
connectors are original cleared routes, not successful root comparisons.
The optional supplied start is the literal preceding finish Owner with its
retained relation to the old paid start; no alternative retains the whole
historical three-cache procedure.
-/
def prepareDetour
    (reference : WindingOneLoop (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) ⊕
      WindingOneLoop (Paths.polynomial parameter) source.point)
    (sourceInside : (box site parameter unitQuarter current.parameter regular).Contains source.point)
    (targetInside : (box site parameter unitQuarter current.parameter regular).Contains targetLines.point)
    (walk : {value : Walks.Walk grid
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive target.parameter)) //
      value = geometry.detourWalk elimination clearances source targetLines grid sourceOn targetOn})
    (entry : ClearBoxPaths.Route (Paths.polynomial parameter)
      (box site parameter unitQuarter current.parameter regular)
      (coordinate site parameter 2 unitQuarter positive current.parameter) source.point)
    (returned : ClearBoxPaths.Route (Paths.polynomial parameter)
      (box site parameter unitQuarter current.parameter regular) targetLines.point
      (coordinate site parameter 2 unitQuarter positive target.parameter))
    (supplied : Option (Start sourceOwner) := none) :
    Σ first : {value : CoveredTracedPath entry.path (Start.owner sourceOwner supplied) //
      value = CoveredTracedPath.build entry.path entry.within (Start.owner sourceOwner supplied)},
    Σ middle : {value : CoveredTracedPath
        (walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm).path first.val.traced.finishOwner //
      value = CoveredTracedPath.build
        (walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm).path
        (walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm).withinAmbient
        first.val.traced.finishOwner},
    Σ last : {value : CoveredTracedPath returned.path middle.val.traced.finishOwner //
      value = CoveredTracedPath.build returned.path returned.within middle.val.traced.finishOwner},
      NamedEquivalent (ownerName last.val.traced.finishOwner) (ownerName block.finishOwner) :=
  let actualWalk := walk.val.castEndpoints source.point_eq.symm targetLines.point_eq.symm
  let first := CoveredTracedPath.build entry.path entry.within (Start.owner sourceOwner supplied)
  let middle := CoveredTracedPath.build actualWalk.path actualWalk.withinAmbient first.traced.finishOwner
  let last := CoveredTracedPath.build returned.path returned.within middle.traced.finishOwner
  let compared := block.detourEquivalent source targetLines reference sourceInside targetInside walk
    entry returned first middle last (Start.equivalent sourceOwner supplied)
  ⟨⟨first, rfl⟩, ⟨middle, rfl⟩, ⟨last, rfl⟩, compared⟩

/-- The whole original three-path preparation on the literal cached grid Walk and internally built connectors.

The existing subtype retains the exact original prepareDetour result.
Both connector endpoints are derived from the same selected line caches
and original chart payment; no successful endpoint comparison is assumed.
-/
@[expose] def DetourCache
    (reference : WindingOneLoop (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) ⊕
      WindingOneLoop (Paths.polynomial parameter) source.point)
    (walk : {value : Walks.Walk grid
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive target.parameter)) //
      value = geometry.detourWalk elimination clearances source targetLines grid sourceOn targetOn})
    (supplied : Option (Start sourceOwner)) :=
  let sourceInside := source.point_in_source
  let targetInside := targetLines.point_in_target current.parameter payment
  let entry := ClearBoxPaths.Route.build geometry.clearance
    (coordinate site parameter 2 unitQuarter positive current.parameter) source.point
    (source_inside (positive := positive) regular) sourceInside
  let returned := ClearBoxPaths.Route.build geometry.clearance targetLines.point
    (coordinate site parameter 2 unitQuarter positive target.parameter) targetInside
    (target_inside (positive := positive) regular payment)
  {value // value =
    block.prepareDetour source targetLines reference sourceInside targetInside walk entry returned supplied}

/-- Prepare the same original detour from its literal retained grid Walk with intrinsic endpoint containment.

The original builder receives the same computed L connectors and optional
actual preceding Owner. Its complete factory result stays in the returned
cache; the three preparation procedures and their payments are unchanged.
-/
def prepareDetourOn
    (reference : WindingOneLoop (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) ⊕
      WindingOneLoop (Paths.polynomial parameter) source.point)
    (walk : {value : Walks.Walk grid
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive target.parameter)) //
      value = geometry.detourWalk elimination clearances source targetLines grid sourceOn targetOn})
    (supplied : Option (Start sourceOwner) := none) :
    DetourCache block source targetLines reference walk supplied := ⟨_, rfl⟩

namespace DetourCache

variable {block source targetLines}
variable
    {reference : WindingOneLoop (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) ⊕
      WindingOneLoop (Paths.polynomial parameter) source.point}
    {walk : {value : Walks.Walk grid
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive current.parameter))
        (Geometry.move elimination regular (coordinate site parameter 2 unitQuarter positive target.parameter)) //
      value = geometry.detourWalk elimination clearances source targetLines grid sourceOn targetOn}}
    {supplied : Option (Start sourceOwner)}

/-- Read the actual returned finish Owner of the same retained three-cover preparation. -/
@[expose] def finishOwner (cached : DetourCache block source targetLines reference walk supplied) :
    OwnerAt site parameter unitQuarter positive target := cached.val.2.2.1.val.traced.finishOwner

/-- Read the same retained endpoint comparison with its actual result and original paid finish Owner. -/
def equivalent (cached : DetourCache block source targetLines reference walk supplied) :
    NamedEquivalent (ownerName cached.finishOwner) (ownerName block.finishOwner) := cached.val.2.2.2

/-- Retain the three actual prepared covers in their literal entry, Walk and return order. -/
@[expose] def blocks (cached : DetourCache block source targetLines reference walk supplied) :
    CoveredTracedPath.Blocks (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) (Start.owner sourceOwner supplied)
      (coordinate site parameter 2 unitQuarter positive target.parameter) cached.finishOwner :=
  .cons cached.val.1.val (.cons cached.val.2.1.val (.singleton cached.val.2.2.1.val))

/-- Read the actual trace of the three retained covers without acquiring another signed path. -/
def trace (cached : DetourCache block source targetLines reference walk supplied) := cached.blocks.trace

/-- The actual cached return has its endpoint-potential winding in the original sharp target square.

The original return route and its literal cached trace remain unchanged.
Its retained line and step containments put the complete connector hull in
the target square, whose supplied clearance gives the exact potential
formula without a new root, path or owner selection.
-/
theorem return_winding (cached : DetourCache block source targetLines reference walk supplied)
    (nextClearance : RegionClearance (Paths.polynomial parameter)
      (box site parameter unitQuarter target.parameter regular)) :
    chainRaw (Paths.polynomial parameter) targetLines.point cached.val.2.2.1.val.traced.trace.get.vertices =
      windingPotential (Paths.polynomial parameter)
        (box site parameter unitQuarter target.parameter regular)
        (coordinate site parameter 2 unitQuarter positive target.parameter) -
      windingPotential (Paths.polynomial parameter)
        (box site parameter unitQuarter target.parameter regular) targetLines.point := by
  have degreePositive : 0 < (Paths.polynomial parameter).natDegree := by
    rewrite [Paths.polynomial_natDegree]
    decide
  let common := box site parameter unitQuarter target.parameter regular
  let moved := targetLines.point
  let original := coordinate site parameter 2 unitQuarter positive target.parameter
  have movedInside : common.Contains moved := targetLines.point_in_source
  have originalInside : common.Contains original := source_inside (positive := positive) regular
  have returnHull : (Box.Hull.hull (Box.Point.pointBox moved)
      (Box.Point.pointBox original)).Refines common := Box.Hull.refines movedInside originalInside
  have returnedInside := ClearPath.InBox.mono returnHull
    (ClearBoxPaths.Route.build_inBox geometry.clearance moved original
      (targetLines.point_in_target current.parameter payment) (target_inside (positive := positive) regular payment))
  exact (TracedPath.winding_original
    cached.val.2.2.1.val.traced).trans
      (ClearBoxPathWinding.ClearPath.rawWinding_eq_potential nextClearance degreePositive _ returnedInside)

/-- The actual cached return and next entry preserve the preceding middle's root name.

The next square is the original sharp source square at the retained target.
Both connector hulls lie there by the same stored line and step payments.
The supplied old-point comparison joins the actual Owners without identifying
them. Their literal owner paths and that stationary join have zero combined
winding; the original reference certifies equality of the two retained frame
selections. Their stored comparisons supply the result without classifying
either Owner again. No path or root identity,
primitive-domain containment or physical-integral equality is asserted.
-/
def returnEntryEquivalent (cached : DetourCache block source targetLines reference walk supplied)
    (nextClearance : RegionClearance (Paths.polynomial parameter)
      (box site parameter unitQuarter target.parameter regular))
    (targetReference : WindingOneLoop (Paths.polynomial parameter) targetLines.point)
    (enteredOwner : OwnerAt site parameter unitQuarter positive target)
    (handoff : NamedEquivalent (ownerName cached.finishOwner) (ownerName enteredOwner))
    (entered : CoveredTracedPath
      (ClearBoxPaths.Route.build nextClearance
        (coordinate site parameter 2 unitQuarter positive target.parameter) targetLines.point
        (source_inside (positive := positive) regular) targetLines.point_in_source).path
      enteredOwner)
    (frame : OwnerFrame ((Paths.polynomial parameter).eval targetLines.point))
    (before : OwnerSelection frame.owners cached.val.2.1.val.traced.finishOwner)
    (after : OwnerSelection frame.owners entered.traced.finishOwner) :
    NamedEquivalent (ownerName entered.traced.finishOwner)
      (ownerName cached.val.2.1.val.traced.finishOwner) := by
  have degreePositive : 0 < (Paths.polynomial parameter).natDegree := by
    rewrite [Paths.polynomial_natDegree]
    decide
  let common := box site parameter unitQuarter target.parameter regular
  let moved := targetLines.point
  let original := coordinate site parameter 2 unitQuarter positive target.parameter
  have movedInside : common.Contains moved := targetLines.point_in_source
  have originalInside : common.Contains original := source_inside (positive := positive) regular
  have entryHull : (Box.Hull.hull (Box.Point.pointBox original)
      (Box.Point.pointBox moved)).Refines common := Box.Hull.refines originalInside movedInside
  have enteredInside := ClearPath.InBox.mono entryHull
    (ClearBoxPaths.Route.build_inBox nextClearance original moved originalInside movedInside)
  let returned := cached.val.2.2.1.val
  have firstWinding := cached.return_winding nextClearance
  have lastWinding :=
    (TracedPath.winding_original entered.traced).trans
      (ClearBoxPathWinding.ClearPath.rawWinding_eq_potential nextClearance degreePositive _ enteredInside)
  have winding : chainRaw (Paths.polynomial parameter) moved returned.traced.trace.get.vertices +
      chainRaw (Paths.polynomial parameter) original entered.traced.trace.get.vertices = 8 * (0 : Int) :=
    (congrArg₂ (fun left right : Int => left + right) firstWinding lastWinding).trans (by omega0)
  exact ClearBoxRootTransport.equivalentOfReturnSelections
    (polynomial := Paths.polynomial parameter) (start := moved) (middle := original)
    (first := cached.val.2.1.val.traced.finishOwner) (returnedOwner := cached.finishOwner)
    (enteredOwner := enteredOwner) (last := entered.traced.finishOwner)
    targetReference returned.traced.trace.get handoff entered.traced.trace.get frame before after 0 winding

/-- Read the literal starting Owner of the retained numerical middle after its actual entry cover.

The returned Owner is the exact entry trace finish already indexing the
cached middle. Both signed-spine families use this readback without
unfolding the three-cover factory or constructing another continuation.
-/
@[expose] def entryOwner (cached : DetourCache block source targetLines reference walk supplied) :
    Riemann.Topology.SquareRootContinuationChain.Owner ((Paths.polynomial parameter).eval source.point) :=
  cached.val.1.val.traced.finishOwner

/-- Read the actual retained entry path from the supplied start to its literal cached middle Owner.

The complete original entry cover supplies this owner path. Its original
start, supplied owner and moved grid endpoint remain indices, and the same
saved trace is returned without another connector or root preparation.
-/
@[expose] def entryTrace (cached : DetourCache block source targetLines reference walk supplied) :
    OwnerPath (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter)
      (Start.owner sourceOwner supplied) source.point cached.entryOwner :=
  cached.val.1.val.traced.trace.get

/-- The cached entry's winding is its endpoint-potential difference in the original sharp source square.

Both actual entry endpoints lie in the same retained source geometry.
Its original clearance and complete connector hull derive the winding of
the literal saved owner path; no winding or sheet agreement is assumed.
-/
theorem entry_winding (cached : DetourCache block source targetLines reference walk supplied) :
    chainRaw (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) cached.entryTrace.vertices =
      windingPotential (Paths.polynomial parameter) (box site parameter unitQuarter current.parameter regular)
        source.point -
      windingPotential (Paths.polynomial parameter) (box site parameter unitQuarter current.parameter regular)
        (coordinate site parameter 2 unitQuarter positive current.parameter) := by
  have degreePositive : 0 < (Paths.polynomial parameter).natDegree := by
    rewrite [Paths.polynomial_natDegree]
    decide
  let common := box site parameter unitQuarter current.parameter regular
  let original := coordinate site parameter 2 unitQuarter positive current.parameter
  have originalInside : common.Contains original := source_inside (positive := positive) regular
  have movedInside : common.Contains source.point := source.point_in_source
  have entryHull : (Box.Hull.hull (Box.Point.pointBox original)
      (Box.Point.pointBox source.point)).Refines common := Box.Hull.refines originalInside movedInside
  have enteredInside := ClearPath.InBox.mono entryHull
    (ClearBoxPaths.Route.build_inBox geometry.clearance original source.point originalInside movedInside)
  exact (TracedPath.winding_original cached.val.1.val.traced).trans
    (ClearBoxPathWinding.ClearPath.rawWinding_eq_potential geometry.clearance degreePositive _ enteredInside)

end DetourCache

end Detour

end Block

end Steps.Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
