module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Polynomial
public import Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning
public import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
public import Purelib.RootIsolation.Owner.Local.Track
public import Purelib.RootIsolation.Owner.Local.Preparation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Geometry.Rational.Box.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original chamber branches with retained numerical root caches

Finite Rouché overlaps carry original degree-bounded owner occurrences. The
numerical trace stores one actual root program at every traversed chamber,
including both endpoint caches. Different parameter values are connected by
the original path correspondence; their numerical values need not agree.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot.Chamber

open Purelib.RootIsolation
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.Geometry.Rational
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

set_option genInjectivity false in
/-- One original chamber occurrence with its retained local numerical program.

The frame and degree-bounded index retain mathematical ownership. The same
owner initializes the stored track, whose coherent root cache remains distinct
from other occurrences even when derived arithmetic readings coincide.
-/
structure Root (frame : ChamberFrame) (index : frame.Index) where
  /-- The actual local root refinement program for the original indexed owner. -/
  track : WindingOneTrack frame.polynomial (frame.owner index).box
  /-- The numerical program starts at that same original owner box. -/
  initial_box : track.initial.box = (frame.owner index).box
  /-- The actual retained numerical root certificate and state cache. -/
  certificate : CertifiedName track

constructive_injectivity Root

namespace Root

/-- Materialize one original local owner program and its coherent numerical cache once. -/
@[expose] def ofOwner (frame : ChamberFrame) (index : frame.Index) : Root frame index :=
  let input := ChamberFrame.input frame
  let track := (frame.owner index).track input.degreeAtLeastTwo input.squarefree
  ⟨track, rfl, certifiedName track input.degreePositive⟩

/-- Build the original root cache from a retained complete local-owner readback.

The supplied prepared owner is consumed directly. Its equality identifies the
same original frame occurrence, while its retained box and clearance initialize
the numerical track without another canonical-owner producer call. -/
@[expose] def ofPreparedOwner (frame : ChamberFrame) (index : frame.Index)
    (prepared : Owner.Local.Preparation.Prepared (frame.owner index)) : Root frame index :=
  let input := ChamberFrame.input frame
  let track := prepared.owner.track input.degreeAtLeastTwo input.squarefree
  let cached : Sigma (fun track : WindingOneTrack frame.polynomial prepared.owner.box => CertifiedName track) :=
    ⟨track, certifiedName track input.degreePositive⟩
  let transported : Sigma (fun track : WindingOneTrack frame.polynomial (frame.owner index).box =>
      CertifiedName track) :=
    (congrArg Owner.Local.Basic.LocalOwner.box prepared.owner_eq) ▸
      cached
  ⟨transported.1, by
      rcases prepared with ⟨owner, same⟩
      cases same
      rfl,
    transported.2⟩

/-- A complete original-owner readback gives exactly the original root cache construction. -/
theorem ofPreparedOwner_eq (frame : ChamberFrame) (index : frame.Index)
    (prepared : Owner.Local.Preparation.Prepared (frame.owner index)) :
    ofPreparedOwner frame index prepared = ofOwner frame index := by
  rcases prepared with ⟨owner, same⟩
  cases same
  rfl

/-- An original local-owner root uses the same canonical Newton refinement on every supplied state.

The complete root readback preserves the original polynomial, ambient owner
and input certificates. Only the actual supplied current state and positive
accuracy request are evaluated by the canonical refinement operation.
-/
theorem refine_eq {frame : ChamberFrame} {index : frame.Index} (root : Root frame index)
    (same : root = ofOwner frame index)
    (current : WindingOneState frame.polynomial (frame.owner index).box)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    root.track.refine current epsilon positive = Track.Newton.Refinement.refineState
      frame.input.degreeAtLeastTwo frame.input.squarefree frame.input.elimination current epsilon positive := by
  cases same
  rfl

/-- Read the original root's quantitative residual using an exact retained ambient box.

The same track and complete certified cache are transported together. The
result remains indexed by the original coherent channel and polynomial, with
all original numerical states and residual bounds preserved.
-/
@[expose] def residualFromBox {frame : ChamberFrame} {index : frame.Index} (root : Root frame index)
    (box : Box) (same : box = (frame.owner index).box) :
    Purelib.Polynomial.Approximation.Gaussian.Residual frame.polynomial root.certificate.value :=
  let retained : Σ track : WindingOneTrack frame.polynomial box, CertifiedName track :=
    same.symm ▸ ⟨root.track, root.certificate⟩
  let certificate := retained.2
  let residual := certificate.residualCertificate
  have channelEq : certificate.value = root.certificate.value := by
    cases same
    rfl
  channelEq ▸ residual

/-- Retained ambient-box residual reading gives the complete original residual certificate. -/
theorem residualFromBox_eq {frame : ChamberFrame} {index : frame.Index} (root : Root frame index)
    (box : Box) (same : box = (frame.owner index).box) :
    root.residualFromBox box same = root.certificate.residualCertificate := by
  cases same
  rfl

/-- Two retained numerical caches of the same original chamber occurrence agree operationally.

Reconditioning the second original cache supplies one strictly interior owner.
Both original winding-one programs compare with that same retained restart,
and the two comparisons compose at their independent sample indices.
-/
def equivalent {frame : ChamberFrame} {index : frame.Index} (first second : Root frame index) :
    Purelib.Approximation.Gaussian.Equivalence.Equivalent
      first.certificate.approximation second.certificate.approximation := by
  let restarted := Reconditioning.ofTarget second.certificate 0 1 (by decide)
  have nested : restarted.restarted.initial.box.StrictInterior first.track.initial.box := by
    have same : second.track.initial.box = first.track.initial.box :=
      second.initial_box.trans first.initial_box.symm
    exact congrArg (fun box : Box => restarted.restarted.initial.box.StrictInterior box) same |>.mp restarted.nested
  exact Purelib.Approximation.Gaussian.Equivalence.Equivalent.trans
    (first.certificate.compare_nested_prepared (ChamberFrame.input frame) restarted.root nested)
    (Purelib.Approximation.Gaussian.Equivalence.Equivalent.symm
      (restarted.equivalent (ChamberFrame.input frame)))

/-- The original coherent channels of two caches for the same chamber occurrence agree. -/
def namedEquivalent {frame : ChamberFrame} {index : frame.Index} (first second : Root frame index) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      first.certificate.value.name second.certificate.value.name := by
  rewrite [first.certificate.value_approximation, second.certificate.value_approximation]
  exact (first.equivalent second).toNamed

/-- Transport one retained root cache along an equality of its original owner indices. -/
@[expose] def transport {frame : ChamberFrame} {index other : frame.Index}
    (same : index = other) (root : Root frame index) : Root frame other :=
  same ▸ root

/-- Successive original owner-index transports preserve the same complete root cache. -/
theorem transport_trans {frame : ChamberFrame} {first middle last : frame.Index}
    (before : first = middle) (after : middle = last) (root : Root frame first) :
    transport after (transport before root) = transport (before.trans after) root := by
  cases before
  cases after
  rfl

/-- Reindexing a retained root in both directions returns the identical complete root cache. -/
theorem transport_inverse {frame : ChamberFrame} {index other : frame.Index}
    (same : index = other) (root : Root frame index) :
    transport same.symm (transport same root) = root := by
  cases same
  rfl

end Root

set_option genInjectivity false in
/-- Numerical caches along one exact original chamber path and starting occurrence.

Each constructor retains the next original matched occurrence and its numerical
cache. The original path already stores every overlap, bridge and inverse owner
matching; this trace supplements it without replacing those witnesses.
-/
inductive Trace : {start finish : ChamberFrame} → (path : ChamberPath start finish) →
    (index : start.Index) → Root start index → Type 2
  /-- The empty path retains the exact supplied original root cache. -/
  | nil {frame : ChamberFrame} {index : frame.Index} (root : Root frame index) :
      Trace (.nil frame) index root
  /-- Store a cache at the actual next matched owner, then retain the remaining trace. -/
  | cons {start middle finish : ChamberFrame}
      {step : Progressive.Chamber.Overlap.ChamberOverlap start middle}
      {remaining : ChamberPath middle finish} {index : start.Index}
      {source : Root start index}
      (target : Root middle (step.matching.forward index))
      (rest : Trace remaining (step.matching.forward index) target) :
      Trace (.cons step remaining) index source

constructive_injectivity Trace

namespace Trace

/-- Compute only the numerical programs of the already prepared original chamber occurrences. -/
@[expose] def build : {start finish : ChamberFrame} → (path : ChamberPath start finish) →
    (index : start.Index) → (source : Root start index) → Trace path index source
  | _, _, .nil _, _, source => .nil source
  | _, _, .cons step remaining, index, _ =>
      let target := Root.ofOwner _ (step.matching.forward index)
      .cons target (build remaining (step.matching.forward index) target)

/-- Read the actual final numerical cache at the original path's selected endpoint occurrence. -/
@[expose] def endpoint {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source) :
    Root finish (path.finalIndex index) :=
  Trace.casesOn (motive := fun {_ finish} path index _ _ => Root finish (path.finalIndex index)) trace
    (fun {_ _} root => root)
    (fun {_ _ _ _ _ _ _} _ rest => rest.endpoint)
termination_by structural trace

/-- Read the actual bounded endpoint occurrence retained in the final trace cell.

The complete path-index readback certifies that same original occurrence.
The procedure follows stored tails and reads the final index without applying
any overlap matching.
-/
@[expose] def finalIndex {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source) :
    { value : finish.Index // value = path.finalIndex index } :=
  Trace.casesOn
    (motive := fun {_ finish} path index _ _ => { value : finish.Index // value = path.finalIndex index }) trace
    (fun {_ index} _ => ⟨index, rfl⟩)
    (fun {_ _ _ _ _ _ _} _ rest => rest.finalIndex)
termination_by structural trace

/-- Retain the empty starting trace using the actual stored source context.

The stored frame, bounded index and original root are read from the trace.
Constructing this empty prefix applies no original overlap matching.
-/
@[expose] def empty {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source) :
    Trace (.nil start) index source :=
  Trace.casesOn (motive := fun {start _} _ index source _ => Trace (.nil start) index source) trace
    (fun {_ _} root => .nil root)
    (fun {_ _ _ _ _ _ source} _ _ => .nil source)

/-- The empty prefix retains the complete original source cache at its original occurrence. -/
theorem empty_eq {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source) :
    trace.empty = .nil source := by
  cases trace <;> rfl

/-- Reindex the original starting occurrence and cache along an explicit index equality. -/
@[expose] def castIndex {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index other : start.Index} {source : Root start index} (same : index = other)
    (trace : Trace path index source) : Trace path other (Root.transport same source) :=
  by
    cases same
    exact trace

/-- Transport by the reflexive starting-index equality retains the complete original trace. -/
theorem castIndex_refl {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace path index source) :
    castIndex rfl trace = trace := rfl

/-- A transported empty trace retains the same complete original root at its reindexed occurrence. -/
theorem castIndex_nil {frame : ChamberFrame} {index other : frame.Index}
    (same : index = other) (root : Root frame index) :
    castIndex same (.nil root) = .nil (Root.transport same root) := by
  cases same
  rfl

/-- Read the complete original path from the trace's actual stored constructor fields.

The outer path record reuses the same original frames, overlap and complete
tail. No owner, matching, bridge or refinement procedure is called.
-/
@[expose] def path {start finish : ChamberFrame} {original : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (trace : Trace original index source) :
    { value : ChamberPath start finish // value = original } :=
  Trace.casesOn
    (motive := fun {start finish} path _ _ _ => { value : ChamberPath start finish // value = path }) trace
    (fun {frame _} _ => ⟨.nil frame, rfl⟩)
    (fun {_ _ _ step remaining _ _} _ _ => ⟨.cons step remaining, rfl⟩)

/-- Reindex an already computed complete trace along equality of its exact original path. -/
@[expose] def castPath {start finish : ChamberFrame} {before after : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (same : before = after)
    (trace : Trace before index source) : Trace after index source := same ▸ trace

/-- Reindexing the same original path in both directions preserves the whole numerical trace. -/
theorem castPath_inverse {start finish : ChamberFrame} {before after : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (same : before = after) (trace : Trace before index source) :
    castPath same.symm (castPath same trace) = trace := by
  cases same
  rfl

/-- Join retained numerical traces at their exact shared original endpoint cache.

The second trace must start at the first trace's actual endpoint. Structural
concatenation retains every original overlap and numerical cache; it does not
run the numerical builder again at the shared endpoint.
-/
@[expose] def append {start middle finish : ChamberFrame}
    {firstPath : ChamberPath start middle} {secondPath : ChamberPath middle finish}
    {index : start.Index} {source : Root start index} (first : Trace firstPath index source)
    (second : Trace secondPath (firstPath.finalIndex index) first.endpoint) :
    Trace (firstPath.append secondPath) index source :=
  Trace.casesOn
    (motive := fun {_ middle} firstPath index source first =>
      {finish : ChamberFrame} → {secondPath : ChamberPath middle finish} →
      (second : Trace secondPath (firstPath.finalIndex index) first.endpoint) →
        Trace (firstPath.append secondPath) index source) first
    (fun {_ _} _ {_ _} second => second)
    (fun {_ _ _ _ _ _ _} target rest {_ _} second => .cons target (rest.append second)) second
termination_by structural first

/-- The empty trace returns its original cache without constructing another numerical program. -/
theorem endpoint_nil {frame : ChamberFrame} {index : frame.Index} (root : Root frame index) :
    (Trace.nil root).endpoint = root := rfl

/-- The final cache of a nonempty trace is the same actual cache retained by its remaining trace. -/
theorem endpoint_cons {start middle finish : ChamberFrame}
    {step : Progressive.Chamber.Overlap.ChamberOverlap start middle}
    {remaining : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    (target : Root middle (step.matching.forward index))
    (rest : Trace remaining (step.matching.forward index) target) :
    (Trace.cons (source := source) target rest).endpoint = rest.endpoint := rfl

/-- Original branch correspondence composes through the exact retained middle frame. -/
theorem endpointIndex_append {start middle finish : ChamberFrame}
    (first : ChamberPath start middle) (second : ChamberPath middle finish) (index : start.Index) :
    (first.append second).finalIndex index = second.finalIndex (first.finalIndex index) :=
  first.finalIndex_append second index

/-- Joined traces finish at the exact retained endpoint of the second original trace.

The original path-index equality only transports the bound of that same cache.
Every track, initial owner certificate and numerical state remains unchanged.
-/
theorem endpoint_append {start middle finish : ChamberFrame}
    {firstPath : ChamberPath start middle} {secondPath : ChamberPath middle finish}
    {index : start.Index} {source : Root start index} (first : Trace firstPath index source)
    (second : Trace secondPath (firstPath.finalIndex index) first.endpoint) :
    Root.transport (endpointIndex_append firstPath secondPath index) (first.append second).endpoint =
      second.endpoint := by
  induction first with
  | nil => rfl
  | cons target rest previous => exact previous second

/-- Reversing the same original prepared path returns its selected endpoint to its original occurrence. -/
theorem endpointIndex_reverse {start finish : ChamberFrame}
    (path : ChamberPath start finish) (index : start.Index) :
    path.reverse.finalIndex (path.finalIndex index) = index :=
  path.finalIndex_reverse index

/-- Reverse a prepared trace using its exact original root caches and inverse overlap matchings.

The reversed suffix is joined to the original source cache transported by the
inverse owner-index law. Original source, intermediate and endpoint tracks and
state caches are consumed directly; no numerical owner builder is called.
-/
@[expose] def reverse {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (original : Trace path index source) :
    Trace path.reverse (path.finalIndex index) original.endpoint :=
  Trace.casesOn
    (motive := fun {_ _} path index _ original =>
      Trace path.reverse (path.finalIndex index) original.endpoint) original
    (fun {_ _} root => .nil root)
    (fun {start _ _ step remaining index source} _ rest =>
      let reversed := rest.reverse
      let cached := reversed.finalIndex
      have same : step.reverse.matching.forward cached.val = index :=
        (congrArg step.matching.backward cached.property).trans
          ((congrArg step.matching.backward
            (endpointIndex_reverse remaining (step.matching.forward index))).trans
            (step.matching.backward_forward index))
      let returned := Root.transport same.symm source
      let last : Trace (.cons step.reverse (.nil start)) cached.val
          (Root.transport cached.property.symm reversed.endpoint) :=
        .cons returned (Trace.castIndex same.symm (.nil source))
      let transported : Trace (.cons step.reverse (.nil start))
          (remaining.reverse.finalIndex (remaining.finalIndex (step.matching.forward index))) reversed.endpoint :=
        (Root.transport_inverse cached.property.symm reversed.endpoint) ▸
          Trace.castIndex cached.property last
      reversed.append transported)
termination_by structural original

/-- Reversing a nonempty trace retains its original reversed suffix and the exact original source cache. -/
theorem reverse_cons {start middle finish : ChamberFrame}
    {step : Progressive.Chamber.Overlap.ChamberOverlap start middle}
    {remaining : ChamberPath middle finish} {index : start.Index} {source : Root start index}
    (target : Root middle (step.matching.forward index))
    (rest : Trace remaining (step.matching.forward index) target) :
    (Trace.cons (source := source) target rest).reverse =
      let reversed := rest.reverse
      let same : step.reverse.matching.forward
          (remaining.reverse.finalIndex (remaining.finalIndex (step.matching.forward index))) = index :=
        (congrArg step.matching.backward (endpointIndex_reverse remaining (step.matching.forward index))).trans
          (step.matching.backward_forward index)
      let returned := Root.transport same.symm source
      reversed.append (.cons (source := reversed.endpoint) returned (.nil returned)) := by
  let assemble := fun (cached : { value : middle.Index // value =
      remaining.reverse.finalIndex (remaining.finalIndex (step.matching.forward index)) }) =>
    let reversed := rest.reverse
    have same : step.reverse.matching.forward cached.val = index :=
      (congrArg step.matching.backward cached.property).trans
        ((congrArg step.matching.backward
          (endpointIndex_reverse remaining (step.matching.forward index))).trans
          (step.matching.backward_forward index))
    let returned := Root.transport same.symm source
    let last : Trace (.cons step.reverse (.nil start)) cached.val
        (Root.transport cached.property.symm reversed.endpoint) :=
      .cons returned (Trace.castIndex same.symm (.nil source))
    let transported : Trace (.cons step.reverse (.nil start))
        (remaining.reverse.finalIndex (remaining.finalIndex (step.matching.forward index))) reversed.endpoint :=
      (Root.transport_inverse cached.property.symm reversed.endpoint) ▸ Trace.castIndex cached.property last
    reversed.append transported
  change assemble rest.reverse.finalIndex = _
  generalize rest.reverse.finalIndex = cached
  rcases cached with ⟨value, same⟩
  cases same
  dsimp only [assemble]
  rewrite [castIndex_nil]
  rfl

/-- A cache-preserving reverse trace returns the complete original source root cache. -/
theorem reverse_endpoint {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (original : Trace path index source) :
    Root.transport (endpointIndex_reverse path index) original.reverse.endpoint = source := by
  cases original with
  | nil => rfl
  | @cons start middle finish step remaining index source target rest =>
    let reversed := rest.reverse
    have same : step.reverse.matching.forward
        (remaining.reverse.finalIndex (remaining.finalIndex (step.matching.forward index))) = index :=
      (congrArg step.matching.backward (endpointIndex_reverse remaining (step.matching.forward index))).trans
        (step.matching.backward_forward index)
    let returned := Root.transport same.symm source
    let last := Trace.cons (source := reversed.endpoint) returned (.nil returned)
    let joined := reversed.append last
    have endpointReading := endpoint_append reversed last
    let appendIndex := endpointIndex_append remaining.reverse (.cons step.reverse (.nil start))
      (remaining.finalIndex (step.matching.forward index))
    let fullIndex := endpointIndex_reverse (.cons step remaining) index
    rewrite [reverse_cons]
    change Root.transport fullIndex joined.endpoint = source
    calc
      Root.transport fullIndex joined.endpoint =
          Root.transport (appendIndex.symm.trans fullIndex) (Root.transport appendIndex joined.endpoint) :=
        (Root.transport_trans appendIndex (appendIndex.symm.trans fullIndex) joined.endpoint).symm
      _ = Root.transport (appendIndex.symm.trans fullIndex) returned :=
        congrArg (Root.transport (appendIndex.symm.trans fullIndex)) endpointReading
      _ = source := by
        change Root.transport (appendIndex.symm.trans fullIndex) (Root.transport same.symm source) = source
        rewrite [Root.transport_trans]
        rfl

set_option genInjectivity false in
/-- A retained forward trace paired with actual numerical continuation along its reversed path.

The backward trace starts at the exact cached forward endpoint. Its original
reversed overlaps and all newly retained numerical occurrences remain available.
Only the returned cache, at the same source parameter and owner, is compared
with the original source cache.
-/
structure Reversal {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (original : Trace path index source) where
  /-- The exact original forward trace, with all its numerical caches. -/
  forward : Trace path index source
  /-- The retained forward trace is the supplied original trace. -/
  forward_eq : forward = original
  /-- Actual reversed continuation beginning at that same retained endpoint cache. -/
  backward : Trace path.reverse (path.finalIndex index) forward.endpoint

constructive_injectivity Reversal

namespace Reversal

/-- Construct reversed continuation from all exact original forward caches without another owner producer. -/
@[expose] def ofTrace {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (original : Trace path index source) : Reversal original :=
  ⟨original, rfl, original.reverse⟩

variable {start finish : ChamberFrame} {path : ChamberPath start finish}
variable {index : start.Index} {source : Root start index} {original : Trace path index source}

/-- Read the actual reversed endpoint at its original source owner using the geometric index-return certificate. -/
@[expose] def returned (reversal : Reversal original) : Root start index :=
  Root.transport (endpointIndex_reverse path index) reversal.backward.endpoint

/-- Reversal of an original trace returns its identical complete source cache. -/
theorem ofTrace_returned_eq {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (original : Trace path index source) :
    (ofTrace original).returned = source :=
  original.reverse_endpoint

/-- Cache-preserving reversal compares the identical original named source through its full cache readback.

This constructor-specific relation needs no independent numerical owner or
reconditioning. General reversals with independently supplied backward caches
retain the separate same-owner comparison below.
-/
def ofTrace_namedEquivalent {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} (original : Trace path index source) :
    NamedEquivalent source.certificate.value.name (ofTrace original).returned.certificate.value.name := by
  rewrite [ofTrace_returned_eq]
  exact NamedEquivalent.refl source.certificate.value.name

/-- The returned cache is exactly the retained backward endpoint transported by original owner identity. -/
theorem returned_eq (reversal : Reversal original) : reversal.returned =
    Root.transport (endpointIndex_reverse path index) reversal.backward.endpoint := rfl

/-- Reversed numerical continuation agrees with the original cache at the same source occurrence.

The comparison uses the original squarefree winding owner and keeps both
numerical programs. It asserts no equality of values along forward motion.
-/
def namedEquivalent (reversal : Reversal original) :
    Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
      source.certificate.value.name reversal.returned.certificate.value.name :=
  source.namedEquivalent reversal.returned

end Reversal

end Trace

end Purelib.Riemann.RootContinuation.CoherentRoot.Chamber

end
