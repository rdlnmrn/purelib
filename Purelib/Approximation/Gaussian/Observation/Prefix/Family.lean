module

public import Purelib.Approximation.Gaussian.Observation.Prefix.Source
public import Purelib.Approximation.Gaussian.Observation.Prefix.Continuation
public import Purelib.Geometry.Rational.Box.Tree
import Purelib.Data.List.Map
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Projective.Line.Matrix.Gaussian

/-!
# Separated rational continuations of one canonical recording

The actual final proper box supports a cached finite tree of disjoint child
boxes. Each original leaf sample realizes the whole original recording,
using its same matrices, inverse charts, requests and numerical replies.
The leaf caches its full continuation and automatic terminal word at that
same sample, with finite valid code for arbitrary later numerical requests.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Prefix.Source.Recording

open Purelib
open Purelib.Data
open Purelib.Data.CCL
open Purelib.Geometry.Projective
open Purelib.Computation.Query
open Purelib.Geometry.Rational.Box

set_option genInjectivity false in
/-- One retained tree address owns a rational admission of the same original canonical recording. -/
structure Leaf {origin : Snapshot} (recording : Recording origin) {depth : Nat}
    (tree : Tree recording.current.enclosure.box depth) where
  /-- The exact original address of this retained leaf. -/ address : tree.Leaf
  /-- The complete original admission, source-free history and automatic terminal result at this same leaf. -/
  continuation : Continuation.Result recording.trace
  /-- The admission uses the exact cached sample at the original tree address. -/ pointEq :
    continuation.admitted.realization.point = tree.point address

namespace Leaf

/-- Read the same leaf's original admission from its already cached complete continuation. -/
@[expose] def admitted {origin : Snapshot} {recording : Recording origin} {depth : Nat}
    {tree : Tree recording.current.enclosure.box depth} (leaf : Leaf recording tree) : Admitted recording.trace :=
  leaf.continuation.admitted

/-- Admit the exact cached sample at an address through the original recording. -/
def admissionAt {origin : Snapshot} (recording : Recording origin) {depth : Nat}
    (tree : Tree recording.current.enclosure.box depth) (address : tree.Leaf) : Admitted recording.trace :=
  let sample : NonzeroSample recording.current.enclosure.box :=
    ⟨tree.point address, tree.point_inside address, tree.point_nonzero address⟩
  let realization := recording.current.enclosure.realizeSample sample
  recording.admitWith realization

/-- The admitted point is the original cached sample at the requested address. -/
theorem admissionAt_point {origin : Snapshot} (recording : Recording origin) {depth : Nat}
    (tree : Tree recording.current.enclosure.box depth) (address : tree.Leaf) :
    (admissionAt recording tree address).realization.point = tree.point address := by
  let sample : NonzeroSample recording.current.enclosure.box :=
    ⟨tree.point address, tree.point_inside address, tree.point_nonzero address⟩
  let realization := recording.current.enclosure.realizeSample sample
  exact (recording.admitWith_point realization).trans (recording.current.enclosure.realizeSample_point sample)

/-- Admit a cached tree sample and retain its complete automatic continuation. -/
def build {origin : Snapshot} (recording : Recording origin) {depth : Nat}
    (tree : Tree recording.current.enclosure.box depth) (address : tree.Leaf) : Leaf recording tree :=
  let admitted := admissionAt recording tree address
  let continuation := Continuation.ofAdmitted admitted
  ⟨address, continuation,
    (congrArg (fun original : Admitted recording.trace => original.realization.point)
      (Continuation.ofAdmitted_admitted admitted)).trans (admissionAt_point recording tree address)⟩

/-- Building a complete leaf retains the same admission as admitting its original address. -/
theorem build_admitted {origin : Snapshot} (recording : Recording origin) {depth : Nat}
    (tree : Tree recording.current.enclosure.box depth) (address : tree.Leaf) :
    (build recording tree address).admitted = admissionAt recording tree address :=
  Continuation.ofAdmitted_admitted (admissionAt recording tree address)

private theorem build_address_specification {origin : Snapshot} (recording : Recording origin) {depth : Nat}
    (tree : Tree recording.current.enclosure.box depth) (address : tree.Leaf) :
    (build recording tree address).address = address := rfl

/-- Building a leaf retains its original address in the same actual tree. -/
theorem build_address {origin : Snapshot} (recording : Recording origin) {depth : Nat}
    (tree : Tree recording.current.enclosure.box depth) (address : tree.Leaf) :
    (build recording tree address).address = address := build_address_specification recording tree address

/-- Interpret the leaf's complete finite canonical history, including all legal future and divergent requests. -/
@[expose] def interpret {origin : Snapshot} {recording : Recording origin} {depth : Nat}
    {tree : Tree recording.current.enclosure.box depth} (leaf : Leaf recording tree) : Cursor.Question → Reply :=
  leaf.continuation.history.interpret leaf.continuation.valid

/-- The same retained leaf interpreter answers every original and recalled numerical exchange exactly. -/
theorem answers {origin : Snapshot} {recording : Recording origin} {depth : Nat}
    {tree : Tree recording.current.enclosure.box depth} (leaf : Leaf recording tree) :
    Basic.Answers leaf.interpret recording.trace := leaf.continuation.answers

/-- Every original finite adaptive execution is preserved at the same retained rational leaf. -/
theorem same_execution {origin : Snapshot} {recording : Recording origin} {depth : Nat}
    {tree : Tree recording.current.enclosure.box depth} (leaf : Leaf recording tree)
    {Value : Type} (protocol : Protocol Cursor.Question Reply Value) (oracle : Cursor.Question → Reply)
    (traceEq : (protocol.run oracle).trace = recording.trace) : protocol.run leaf.interpret = protocol.run oracle :=
  leaf.continuation.same_execution protocol oracle traceEq

/-- Two different addresses retain distinct rational readings of the same original recording. -/
theorem distinct {origin : Snapshot} {recording : Recording origin} {depth : Nat}
    {tree : Tree recording.current.enclosure.box depth} (left right : Leaf recording tree)
    (different : left.address ≠ right.address) :
    left.admitted.realization.point ≠ right.admitted.realization.point := by
  intro equal
  have same : tree.point left.address = tree.point right.address := left.pointEq.symm.trans (equal.trans right.pointEq)
  exact different (tree.point_injective left.address right.address same)

/-- Different original tree addresses retain different automatically computed canonical terminal words. -/
theorem terminal_distinct {origin : Snapshot} {recording : Recording origin} {depth : Nat}
    {tree : Tree recording.current.enclosure.box depth} (left right : Leaf recording tree)
    (different : left.address ≠ right.address) :
    left.continuation.terminal.completion.word ≠ right.continuation.terminal.completion.word := by
  intro same
  have stateEq : left.continuation.terminal.completion.state = right.continuation.terminal.completion.state :=
    left.continuation.terminal.completion.stateSpec.trans
      ((congrArg Encoding.Parser.State.parse same).trans right.continuation.terminal.completion.stateSpec.symm)
  have sameReading := congrArg (fun state : Encoding.Parser.State =>
    Line.Gaussian.Proj.affineReading (Line.Matrix.act state.matrix Line.Proj.omega)) stateEq
  exact left.distinct right different
    (left.continuation.terminal_reading.symm.trans (sameReading.trans right.continuation.terminal_reading))

end Leaf

set_option genInjectivity false in
/-- A finite depth request retains its actual separated box tree and every original rational continuation leaf. -/
structure Family {origin : Snapshot} (recording : Recording origin) (depth : Nat) where
  /-- The actual finite tree cached inside the same final uniform box. -/ tree :
    Tree recording.current.enclosure.box depth
  /-- Every leaf retains its exact admission and finite continuation code. -/ leaves : List (Leaf recording tree)
  /-- The retained admissions preserve all original leaf addresses in their original order. -/ addressesEq :
    leaves.map Leaf.address = tree.leaves

namespace Family

private theorem build_addresses {origin : Snapshot} (recording : Recording origin) {depth : Nat}
    (tree : Tree recording.current.enclosure.box depth) (addresses : List tree.Leaf) :
    (addresses.map (Leaf.build recording tree)).map Leaf.address = addresses := by
  induction addresses with
  | nil => rfl
  | cons address remaining induction =>
      change (Leaf.build recording tree address).address :: _ = address :: remaining
      exact congrArg₂ List.cons (Leaf.build_address recording tree address) induction

/-- Build all separated rational continuations by retaining each actual cached tree address and original history. -/
def build {origin : Snapshot} (recording : Recording origin) (depth : Nat) : Family recording depth :=
  let tree := Tree.build recording.current.enclosure.box recording.current.enclosure.proper depth
  ⟨tree, tree.leaves.map (Leaf.build recording tree), build_addresses recording tree tree.leaves⟩

/-- Admit the ordered tree samples without constructing their automatic terminal encodings. -/
def admissions {origin : Snapshot} (recording : Recording origin) (depth : Nat) : List (Admitted recording.trace) :=
  let tree := Tree.build recording.current.enclosure.box recording.current.enclosure.proper depth
  tree.leaves.map (Leaf.admissionAt recording tree)

/-- The directly computed admissions are exactly the admissions retained by the complete family, in order. -/
theorem admissions_eq {origin : Snapshot} (recording : Recording origin) (depth : Nat) :
    admissions recording depth = (build recording depth).leaves.map Leaf.admitted := by
  let tree := Tree.build recording.current.enclosure.box recording.current.enclosure.proper depth
  change tree.leaves.map (Leaf.admissionAt recording tree) =
    (tree.leaves.map (Leaf.build recording tree)).map Leaf.admitted
  induction tree.leaves with
  | nil => rfl
  | cons address remaining induction =>
      change Leaf.admissionAt recording tree address :: _ = (Leaf.build recording tree address).admitted :: _
      exact congrArg₂ List.cons (Leaf.build_admitted recording tree address).symm induction

/-- A finite depth request retains exactly two to that power many complete rational continuations. -/
theorem length {origin : Snapshot} {recording : Recording origin} {depth : Nat} (family : Family recording depth) :
    family.leaves.length = 2 ^ depth :=
  (List.Map.length_map Leaf.address family.leaves).symm.trans
    ((congrArg List.length family.addressesEq).trans family.tree.leaves_length)

end Family

/-- An exact singleton numerical observation cannot hold uniformly on a proper rational box. -/
theorem singleton_excludes_uniform (box : Purelib.Geometry.Rational.Box) (proper : box.Proper)
    (point : Gaussian.Basic.Canonical) :
    ¬ (∀ sample, box.Contains sample → (Enclosure.Ball.point point).Contains sample) :=
  fun uniform => box.not_uniform_singleton proper point
    (fun sample inside => (Enclosure.Ball.contains_point_iff point sample).mp (uniform sample inside))

end Purelib.Approximation.Gaussian.Observation.Prefix.Source.Recording

end
