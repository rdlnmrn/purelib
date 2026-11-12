module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
public import Purelib.Riemann.Paths.OwnerTracePath
public import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.OwnerTraceReadings
public import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Polynomial.Winding.Polygon.Stationary
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Data.List.Append
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Existing covered-path blocks with varying local polynomial-clear boxes

Each block is an unchanged original CoveredTracedPath. Its actual terminal
owner is the next block's source index. Local ambient boxes may differ, so
the composition retains those existing cover/preparation caches rather than
claiming one globally polynomial-clear ambient. The ambient-independent
OwnerPath operations provide the trace and its original endpoint ownership.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

open Purelib.Polynomial.Winding

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter)

namespace Blocks

/-- The actual target owner and complete original same-point join from the retained source.

The existing Sigma keeps the target owner beside its comparison before the
recursive tail is indexed by that same owner. No approximation, root owner
or payment is reconstructed by the projection.
-/
@[expose] def Join {polynomial : CoefficientPolynomial} {point : Canonical}
    (left : Owner (polynomial.eval point)) : Type :=
  Σ right : Owner (polynomial.eval point), OwnerJoin left right

end Blocks

set_option genInjectivity false in
/-- An ordered finite chain of original covered blocks with exact terminal-owner handoffs and varying boxes.

The original clear path, its local ambient, complete preparation, primitive
cover, trace and terminal-owner caches are retained by each existing block.
The dependent tail index uses its actual stored finish owner. This additional
invariant permits composition of locally cleared boxes that cannot safely be
replaced by one globally polynomial-clear rectangle.
-/
inductive Blocks (polynomial : CoefficientPolynomial) :
    (start : Canonical) → Owner (polynomial.eval start) →
      (finish : Canonical) → Owner (polynomial.eval finish) → Type
  /-- Retain the exact source point and full-cubic owner for a stationary empty chain. -/
  | nil (point : Canonical) (owner : Owner (polynomial.eval point)) : Blocks polynomial point owner point owner
  /-- Prepend one entire original covered block and retain the tail on its exact cached terminal owner. -/
  | cons {start middle finish : Canonical} {ambient : Box}
      {path : ClearPath polynomial ambient start middle}
      {source : Owner (polynomial.eval start)} {target : Owner (polynomial.eval finish)}
      (covered : CoveredTracedPath path source)
      (tail : Blocks polynomial middle covered.traced.finishOwner finish target) :
      Blocks polynomial start source finish target
  /-- Retain one paid stationary comparison between the two original owners at the identical spatial endpoint. -/
  | handoff {point finish : Canonical}
      {left : Owner (polynomial.eval point)} {target : Owner (polynomial.eval finish)}
      (join : Blocks.Join left) (tail : Blocks polynomial point join.1 finish target) :
      Blocks polynomial point left finish target

constructive_injectivity Blocks

namespace Blocks

variable {polynomial : CoefficientPolynomial}

/-- Count the actual retained original covered blocks in their exact owner-handoff order. -/
@[expose] def length {polynomial : CoefficientPolynomial} {start finish : Canonical}
    {source : Owner (polynomial.eval start)} {target : Owner (polynomial.eval finish)}
    (blocks : Blocks polynomial start source finish target) : Nat :=
  match blocks with
  | .nil _ _ => 0
  | .cons _ tail => tail.length + 1
  | .handoff _ tail => tail.length
termination_by structural blocks

/-- The original empty covered-block chain has zero retained blocks. -/
theorem length_nil (point : Canonical) (owner : Owner (polynomial.eval point)) :
    (Blocks.nil point owner).length = 0 := (rfl)

/-- Prepending one whole original covered block increases the retained count by one. -/
theorem length_cons {start middle finish : Canonical} {ambient : Box}
    {path : ClearPath polynomial ambient start middle}
    {source : Owner (polynomial.eval start)} {target : Owner (polynomial.eval finish)}
    (covered : CoveredTracedPath path source)
    (tail : Blocks polynomial middle covered.traced.finishOwner finish target) :
    (Blocks.cons covered tail).length = tail.length + 1 := (rfl)

/-- A retained same-point owner comparison contributes no geometric covered block.

The complete original join, its two residual tails, selected comparison
indices and payment are retained by the handoff constructor. This count
concerns geometric blocks only; it does not count numerical requests.
-/
theorem length_handoff {point finish : Canonical}
    {left right : Owner (polynomial.eval point)} {target : Owner (polynomial.eval finish)}
    (join : OwnerJoin left right) (tail : Blocks polynomial point right finish target) :
    (Blocks.handoff ⟨right, join⟩ tail).length = tail.length := (rfl)

/-- Transport the same complete block chain along equality of its defining polynomial.

Only the original polynomial and endpoint-owner indices change. Each retained
path, prepared cache, cover, trace and stationary join remains the same value.
-/
@[expose] def castPolynomial {sourcePolynomial targetPolynomial : CoefficientPolynomial}
    (same : sourcePolynomial = targetPolynomial) {start finish : Canonical}
    {source : Owner (sourcePolynomial.eval start)} {target : Owner (sourcePolynomial.eval finish)}
    (blocks : Blocks sourcePolynomial start source finish target) :
    Blocks targetPolynomial start (castOwnerParameter (congrArg (fun polynomial => polynomial.eval start) same) source)
      finish (castOwnerParameter (congrArg (fun polynomial => polynomial.eval finish) same) target) := by
  cases same
  exact blocks

/-- Polynomial reindexing preserves the entire supplied original block chain heterogeneously. -/
theorem castPolynomial_heq {sourcePolynomial targetPolynomial : CoefficientPolynomial}
    (same : sourcePolynomial = targetPolynomial) {start finish : Canonical}
    {source : Owner (sourcePolynomial.eval start)} {target : Owner (sourcePolynomial.eval finish)}
    (blocks : Blocks sourcePolynomial start source finish target) : HEq (blocks.castPolynomial same) blocks := by
  cases same
  rfl

/-- Transport a complete covered-block chain along exact endpoint and original-owner identities.

Only the displayed indices change. Every stored covered path, preparation,
primitive cover and owner handoff remains the same original value; an
operational comparison of different owners is not an endpoint identity.
-/
@[expose] def castEndpoints {start finish nextStart nextFinish : Canonical}
    {source : Owner (polynomial.eval start)} {target : Owner (polynomial.eval finish)}
    {nextSource : Owner (polynomial.eval nextStart)} {nextTarget : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (sourceEq : HEq source nextSource) (targetEq : HEq target nextTarget)
    (blocks : Blocks polynomial start source finish target) :
    Blocks polynomial nextStart nextSource nextFinish nextTarget := by
  cases startEq
  cases finishEq
  cases eq_of_heq sourceEq
  cases eq_of_heq targetEq
  exact blocks

/-- Exact endpoint transport preserves the entire original covered-block value heterogeneously. -/
theorem castEndpoints_heq {start finish nextStart nextFinish : Canonical}
    {source : Owner (polynomial.eval start)} {target : Owner (polynomial.eval finish)}
    {nextSource : Owner (polynomial.eval nextStart)} {nextTarget : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (sourceEq : HEq source nextSource) (targetEq : HEq target nextTarget)
    (blocks : Blocks polynomial start source finish target) :
    HEq (blocks.castEndpoints startEq finishEq sourceEq targetEq) blocks := by
  cases startEq
  cases finishEq
  cases eq_of_heq sourceEq
  cases eq_of_heq targetEq
  rfl

/-- Reindexing exact endpoints preserves the actual number of retained covered blocks. -/
theorem castEndpoints_length {start finish nextStart nextFinish : Canonical}
    {source : Owner (polynomial.eval start)} {target : Owner (polynomial.eval finish)}
    {nextSource : Owner (polynomial.eval nextStart)} {nextTarget : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (sourceEq : HEq source nextSource) (targetEq : HEq target nextTarget)
    (blocks : Blocks polynomial start source finish target) :
    (blocks.castEndpoints startEq finishEq sourceEq targetEq).length = blocks.length := by
  cases startEq
  cases finishEq
  cases eq_of_heq sourceEq
  cases eq_of_heq targetEq
  rfl

/-- Retain one completed covered block without repeating its primitive cover, preparation or root trace. -/
@[expose] def singleton {start finish : Canonical} {ambient : Box}
    {path : ClearPath polynomial ambient start finish} {owner : Owner (polynomial.eval start)}
    (covered : CoveredTracedPath path owner) : Blocks polynomial start owner finish covered.traced.finishOwner :=
  .cons covered (.nil finish covered.traced.finishOwner)

/-- Compose the existing cached block owner traces in their original order and exact full-cubic endpoint indices. -/
@[expose] def trace : ∀ {start finish : Canonical} {source : Owner (polynomial.eval start)}
    {target : Owner (polynomial.eval finish)}, Blocks polynomial start source finish target →
      OwnerPath polynomial start source finish target
  | _, _, _, _, .nil point owner => .nil point owner
  | _, _, _, _, .cons covered tail => covered.traced.trace.get.append (trace tail)
  | _, _, _, _, .handoff join tail => .cons (OwnerLink.stationary _ _ join.2) (trace tail)

/-- Read the original cached moving vertices of every unchanged covered preparation in their retained block order. -/
@[expose] def movingVertices : ∀ {start finish : Canonical} {source : Owner (polynomial.eval start)}
    {target : Owner (polynomial.eval finish)}, Blocks polynomial start source finish target → List Canonical
  | _, _, _, _, .nil _ _ => []
  | _, _, _, _, .cons covered tail => covered.traced.movingVertices ++ movingVertices tail
  | _, _, _, _, .handoff _ tail => movingVertices tail

/-- The same-point handoff retains the entire original stationary owner link in its trace. -/
theorem handoff_trace {point finish : Canonical}
    {left right : Owner (polynomial.eval point)} {target : Owner (polynomial.eval finish)}
    (join : OwnerJoin left right) (tail : Blocks polynomial point right finish target) :
    (Blocks.handoff ⟨right, join⟩ tail).trace = .cons (OwnerLink.stationary polynomial point join) tail.trace := rfl

/-- A same-point comparison preserves the original ordered geometric moving-vertex cache. -/
theorem handoff_movingVertices {point finish : Canonical}
    {left right : Owner (polynomial.eval point)} {target : Owner (polynomial.eval finish)}
    (join : OwnerJoin left right) (tail : Blocks polynomial point right finish target) :
    (Blocks.handoff ⟨right, join⟩ tail).movingVertices = tail.movingVertices := rfl

/-- Endpoint transport preserves the exact original ordered moving-vertex cache. -/
theorem castEndpoints_movingVertices {start finish nextStart nextFinish : Canonical}
    {source : Owner (polynomial.eval start)} {target : Owner (polynomial.eval finish)}
    {nextSource : Owner (polynomial.eval nextStart)} {nextTarget : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (sourceEq : HEq source nextSource) (targetEq : HEq target nextTarget)
    (blocks : Blocks polynomial start source finish target) :
    (blocks.castEndpoints startEq finishEq sourceEq targetEq).movingVertices = blocks.movingVertices := by
  cases startEq
  cases finishEq
  cases eq_of_heq sourceEq
  cases eq_of_heq targetEq
  rfl

/-- Endpoint transport delegates to the same exact original OwnerPath transport. -/
theorem castEndpoints_trace {start finish nextStart nextFinish : Canonical}
    {source : Owner (polynomial.eval start)} {target : Owner (polynomial.eval finish)}
    {nextSource : Owner (polynomial.eval nextStart)} {nextTarget : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (sourceEq : HEq source nextSource) (targetEq : HEq target nextTarget)
    (blocks : Blocks polynomial start source finish target) :
    (blocks.castEndpoints startEq finishEq sourceEq targetEq).trace =
      blocks.trace.castEndpoints startEq finishEq sourceEq targetEq := by
  cases startEq
  cases finishEq
  cases eq_of_heq sourceEq
  cases eq_of_heq targetEq
  rfl

/-- A singleton covered chain retains the complete original deferred owner trace value. -/
theorem singleton_trace {start finish : Canonical} {ambient : Box}
    {path : ClearPath polynomial ambient start finish} {owner : Owner (polynomial.eval start)}
    (covered : CoveredTracedPath path owner) : (singleton covered).trace = covered.traced.trace.get :=
  OwnerPath.append_nil covered.traced.trace.get

/-- A singleton chain reads the exact original moving-vertex cache without rebuilding its prepared subdivision. -/
theorem singleton_movingVertices {start finish : Canonical} {ambient : Box}
    {path : ClearPath polynomial ambient start finish} {owner : Owner (polynomial.eval start)}
    (covered : CoveredTracedPath path owner) : (singleton covered).movingVertices = covered.traced.movingVertices :=
  Data.List.Append.append_nil covered.traced.movingVertices

/-- The exact original cached moving list terminates at the same retained chain finish point. -/
theorem moving_terminal : ∀ {start finish : Canonical} {source : Owner (polynomial.eval start)}
    {target : Owner (polynomial.eval finish)} (blocks : Blocks polynomial start source finish target),
    Geometry.Rational.Polygon.Chain.terminal start blocks.movingVertices = finish
  | _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, .cons covered tail => by
      change Geometry.Rational.Polygon.Chain.terminal _ (covered.traced.movingVertices ++ tail.movingVertices) = _
      rewrite [Geometry.Rational.Polygon.Chain.terminal_append, covered.traced.movingVertices_eq,
        covered.traced.moving_terminal]
      exact tail.moving_terminal
  | _, _, _, _, .handoff _ tail => tail.moving_terminal

/-- The composed original owner trace has the same raw winding as the unchanged covered-preparation moving caches. -/
theorem trace_winding_eq : ∀ {start finish : Canonical} {source : Owner (polynomial.eval start)}
    {target : Owner (polynomial.eval finish)} (blocks : Blocks polynomial start source finish target),
    Polygon.Basic.chainRaw polynomial start blocks.trace.vertices =
      Polygon.Basic.chainRaw polynomial start blocks.movingVertices
  | _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, .cons covered tail => by
      change Polygon.Basic.chainRaw polynomial _
        (covered.traced.trace.get.append tail.trace).vertices = _
      rewrite [OwnerPath.append_vertices, Polygon.Basic.chainRaw_append,
        covered.traced.trace.get.vertices_terminal, covered.traced.winding_eq, tail.trace_winding_eq]
      change _ = Polygon.Basic.chainRaw polynomial _
        (covered.traced.movingVertices ++ tail.movingVertices)
      rewrite [Polygon.Basic.chainRaw_append, covered.traced.movingVertices_eq,
        covered.traced.moving_terminal]
      rfl
  | _, _, _, _, .handoff (left := left) join tail => by
      change Polygon.Basic.chainRaw polynomial _ (_ :: tail.trace.vertices) = _
      rewrite [Polynomial.Winding.Polygon.Stationary.chainRaw_cons_self polynomial _
        left.parameterNonzero]
      exact tail.trace_winding_eq

/-- Concatenate existing covered blocks using the identical shared endpoint and actual original terminal owner. -/
@[expose] def append : ∀ {start middle finish : Canonical} {source : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {target : Owner (polynomial.eval finish)},
    Blocks polynomial start source middle center → Blocks polynomial middle center finish target →
      Blocks polynomial start source finish target
  | _, _, _, _, _, _, .nil _ _, right => right
  | _, _, _, _, _, _, .cons covered tail, right => .cons covered (tail.append right)
  | _, _, _, _, _, _, .handoff join tail, right => .handoff join (tail.append right)

/-- Concatenation adds the counts of the two exact retained covered-block chains. -/
theorem append_length : ∀ {start middle finish : Canonical} {source : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {target : Owner (polynomial.eval finish)}
    (left : Blocks polynomial start source middle center) (right : Blocks polynomial middle center finish target),
    (left.append right).length = left.length + right.length
  | _, _, _, _, _, _, .nil _ _, right => by
      rewrite [append, length]
      exact (Nat.zero_add right.length).symm
  | _, _, _, _, _, _, .cons covered tail, right => by
      rewrite [append, length, length]
      rewrite [tail.append_length right]
      exact (Nat.add_assoc tail.length right.length 1).trans
        ((congrArg (Nat.add tail.length) (Nat.add_comm right.length 1)).trans
          (Nat.add_assoc tail.length 1 right.length).symm)
  | _, _, _, _, _, _, .handoff join tail, right => by
      rewrite [append, length, length]
      exact tail.append_length right

/-- Append across an exact base-coordinate seam using the very same retained middle owner.

The heterogeneous owner identity changes only its dependent parameter index.
This operation accepts no sheet label or numerical comparison as an owner
identity and retains both supplied complete covered-block chains.
-/
@[expose] def appendAt {start middle nextMiddle finish : Canonical}
    {source : Owner (polynomial.eval start)} {center : Owner (polynomial.eval middle)}
    {nextCenter : Owner (polynomial.eval nextMiddle)} {target : Owner (polynomial.eval finish)}
    (left : Blocks polynomial start source middle center)
    (right : Blocks polynomial nextMiddle nextCenter finish target)
    (seam : middle = nextMiddle) (ownerEq : HEq center nextCenter) :
    Blocks polynomial start source finish target :=
  (left.castEndpoints rfl seam (HEq.refl source) ownerEq).append right

/-- An exact seam preserves the sum of both original covered-block counts. -/
theorem appendAt_length {start middle nextMiddle finish : Canonical}
    {source : Owner (polynomial.eval start)} {center : Owner (polynomial.eval middle)}
    {nextCenter : Owner (polynomial.eval nextMiddle)} {target : Owner (polynomial.eval finish)}
    (left : Blocks polynomial start source middle center)
    (right : Blocks polynomial nextMiddle nextCenter finish target)
    (seam : middle = nextMiddle) (ownerEq : HEq center nextCenter) :
    (left.appendAt right seam ownerEq).length = left.length + right.length := by
  change ((left.castEndpoints rfl seam (HEq.refl source) ownerEq).append right).length = _
  rewrite [append_length, castEndpoints_length]
  rfl

/-- Covered-block concatenation delegates to the same complete original OwnerPath concatenation. -/
theorem append_trace : ∀ {start middle finish : Canonical} {source : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {target : Owner (polynomial.eval finish)}
    (left : Blocks polynomial start source middle center) (right : Blocks polynomial middle center finish target),
    (left.append right).trace = left.trace.append right.trace
  | _, _, _, _, _, _, .nil _ _, _ => rfl
  | _, _, _, _, _, _, .cons covered tail, right => by
      change covered.traced.trace.get.append (tail.append right).trace =
        (covered.traced.trace.get.append tail.trace).append right.trace
      rewrite [tail.append_trace right]
      exact (OwnerPath.append_assoc _ _ _).symm
  | _, _, _, _, _, _, .handoff join tail, right => by
      change OwnerPath.cons (OwnerLink.stationary _ _ join.2) (tail.append right).trace =
        OwnerPath.cons (OwnerLink.stationary _ _ join.2) (tail.trace.append right.trace)
      exact congrArg (OwnerPath.cons (OwnerLink.stationary _ _ join.2)) (tail.append_trace right)

/-- Concatenation retains the exact original cached moving-vertex lists in their original ordered block sequence. -/
theorem append_movingVertices : ∀ {start middle finish : Canonical} {source : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {target : Owner (polynomial.eval finish)}
    (left : Blocks polynomial start source middle center) (right : Blocks polynomial middle center finish target),
    (left.append right).movingVertices = left.movingVertices ++ right.movingVertices
  | _, _, _, _, _, _, .nil _ _, _ => rfl
  | _, _, _, _, _, _, .cons covered tail, right => by
      change covered.traced.movingVertices ++ (tail.append right).movingVertices = _
      rewrite [tail.append_movingVertices right]
      exact (Data.List.Append.append_assoc _ _ _).symm
  | _, _, _, _, _, _, .handoff join tail, right => tail.append_movingVertices right

/-- An exact seam concatenates the two original moving-vertex caches without another root preparation. -/
theorem appendAt_movingVertices {start middle nextMiddle finish : Canonical}
    {source : Owner (polynomial.eval start)} {center : Owner (polynomial.eval middle)}
    {nextCenter : Owner (polynomial.eval nextMiddle)} {target : Owner (polynomial.eval finish)}
    (left : Blocks polynomial start source middle center)
    (right : Blocks polynomial nextMiddle nextCenter finish target)
    (seam : middle = nextMiddle) (ownerEq : HEq center nextCenter) :
    (left.appendAt right seam ownerEq).movingVertices = left.movingVertices ++ right.movingVertices := by
  change ((left.castEndpoints rfl seam (HEq.refl source) ownerEq).append right).movingVertices = _
  rewrite [append_movingVertices, castEndpoints_movingVertices]
  rfl

/-- An exact seam transports and appends the same complete original OwnerPath traces. -/
theorem appendAt_trace {start middle nextMiddle finish : Canonical}
    {source : Owner (polynomial.eval start)} {center : Owner (polynomial.eval middle)}
    {nextCenter : Owner (polynomial.eval nextMiddle)} {target : Owner (polynomial.eval finish)}
    (left : Blocks polynomial start source middle center)
    (right : Blocks polynomial nextMiddle nextCenter finish target)
    (seam : middle = nextMiddle) (ownerEq : HEq center nextCenter) :
    (left.appendAt right seam ownerEq).trace =
      (left.trace.castEndpoints rfl seam (HEq.refl source) ownerEq).append right.trace := by
  change ((left.castEndpoints rfl seam (HEq.refl source) ownerEq).append right).trace = _
  rewrite [append_trace, castEndpoints_trace]
  rfl

end Blocks

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
