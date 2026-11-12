module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Connection
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Independent connection execution on finite safe Legendre paths

Each segment keeps its actual original axis preparation and whole factory.
The next segment starts from that retained endpoint. Concatenation consumes
given prefix and suffix caches; it performs no Euler execution or interval
selection. Initial-value stability uses their actual cached coarse counts.
-/

public section

namespace Purelib.Curves.Legendre.Paths.SafePath

open Purelib
open Purelib.Curves.Legendre.Paths.AxisSegment
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Vector (zipWith)
open Purelib.LinearAlgebra.Gaussian

/-- An ordered connection cache retains every actual axis preparation and its original factory.

The empty path keeps the supplied initial vector. A nonempty path retains
the first whole axis cache before the tail cache, whose initial vector is
that same first endpoint. No regular point or artificial segment is needed
for the empty path.
-/
@[expose] def ConnectionPreparation {start finish : Canonical} (path : SafePath start finish)
    (refinement : Nat) (positive : 0 < refinement) (initial : Vec Canonical 2) : Type _ :=
  match path with
  | .nil _ => {value : Vec Canonical 2 // value = initial}
  | .cons _ safe remaining =>
      (axis : {value : safe.ConnectionPreparation refinement initial //
        value = safe.prepareConnection refinement positive initial}) ×
      remaining.ConnectionPreparation refinement positive axis.val.value

/-- Execute each original axis once, passing its actual retained endpoint to the next segment. -/
def prepareConnection {start finish : Canonical} (path : SafePath start finish)
    (refinement : Nat) (positive : 0 < refinement) (initial : Vec Canonical 2) :
    path.ConnectionPreparation refinement positive initial :=
  match path with
  | .nil _ => ⟨initial, rfl⟩
  | .cons _ safe remaining =>
      let axis : {value : safe.ConnectionPreparation refinement initial //
          value = safe.prepareConnection refinement positive initial} :=
        ⟨safe.prepareConnection refinement positive initial, rfl⟩
      ⟨axis, remaining.prepareConnection refinement positive axis.val.value⟩

namespace ConnectionPreparation

variable {start finish : Canonical} {path : SafePath start finish}
    {refinement : Nat} {positive : 0 < refinement} {initial : Vec Canonical 2}

/-- Read the final retained axis endpoint, or the actual empty-path vector, without executing a segment. -/
@[expose] def value {refinement : Nat} {positive : 0 < refinement} :
    {start finish : Canonical} → {path : SafePath start finish} → {initial : Vec Canonical 2} →
    path.ConnectionPreparation refinement positive initial → Vec Canonical 2
  | _, _, .nil _, _, prepared => prepared.val
  | _, _, .cons _ _ rest, _, prepared => value (path := rest) prepared.2

/-- Transport a whole path cache along exact equality of its initial vector. -/
def castInitial {otherInitial : Vec Canonical 2} (same : initial = otherInitial)
    (prepared : path.ConnectionPreparation refinement positive initial) :
    path.ConnectionPreparation refinement positive otherInitial := by
  cases same
  exact prepared

/-- Exact initial-vector transport preserves the whole original cache. -/
theorem castInitial_heq {otherInitial : Vec Canonical 2} (same : initial = otherInitial)
    (prepared : path.ConnectionPreparation refinement positive initial) :
    HEq (castInitial same prepared) prepared := by
  cases same
  rfl

/-- Initial-vector transport reads the same final cached vector. -/
theorem castInitial_value {otherInitial : Vec Canonical 2} (same : initial = otherInitial)
    (prepared : path.ConnectionPreparation refinement positive initial) :
    (castInitial same prepared).value = prepared.value := by
  cases same
  rfl

/-- An empty path's actual cached value is precisely its supplied initial vector. -/
theorem nil_value {point : Canonical}
    (prepared : (SafePath.nil point).ConnectionPreparation refinement positive initial) :
    prepared.value = initial := prepared.property

variable {middle : Canonical} {segment : AxisSegment start middle}
    {safe : AxisSegment.Safe segment} {remaining : SafePath middle finish}

/-- Read the whole first axis preparation from a nonempty path cache. -/
@[expose] def head
    (prepared : (SafePath.cons segment safe remaining).ConnectionPreparation refinement positive initial) :
    safe.ConnectionPreparation refinement initial := prepared.1.val

/-- The retained first axis cache is its original single execution factory. -/
theorem head_eq
    (prepared : (SafePath.cons segment safe remaining).ConnectionPreparation refinement positive initial) :
    prepared.head = safe.prepareConnection refinement positive initial := prepared.1.property

/-- Read the original tail cache, initialized by the same retained first axis endpoint. -/
@[expose] def tail
    (prepared : (SafePath.cons segment safe remaining).ConnectionPreparation refinement positive initial) :
    remaining.ConnectionPreparation refinement positive prepared.head.value := prepared.2

/-- A nonempty path's final value is the final value of its retained tail cache. -/
theorem cons_value
    (prepared : (SafePath.cons segment safe remaining).ConnectionPreparation refinement positive initial) :
    prepared.value = prepared.tail.value := rfl

/-- Compute finite path amplification from the actual retained axis coarse counts.

The later segment factors multiply earlier factors in execution order.
This operation reads cached counts and performs no interval selection,
coefficient sampling or Euler execution.
-/
@[expose] def amplification {refinement : Nat} {positive : 0 < refinement} :
    {start finish : Canonical} → {path : SafePath start finish} → {initial : Vec Canonical 2} →
    path.ConnectionPreparation refinement positive initial → Rational
  | _, _, .nil _, _, _ => 1
  | _, _, .cons _ _ rest, _, prepared =>
      amplification (path := rest) prepared.2 * Safe.ConnectionPreparation.amplification prepared.head

/-- Every retained path cache has nonnegative finite amplification. -/
theorem amplification_nonnegative (prepared : path.ConnectionPreparation refinement positive initial) :
    0 ≤ prepared.amplification := by
  induction path generalizing initial with
  | nil _ => exact (by decide +kernel : (0 : Rational) ≤ 1)
  | cons _ _ _ prior =>
      exact Order.Arithmetic.mul_nonneg_direct (prior prepared.tail)
        (Safe.ConnectionPreparation.amplification_nonnegative prepared.head)

/-- Two independent executions on the same safe path satisfy internally bounded initial-value stability.

The original axis stability laws pay each actual segment, and their cached
growth factors compose. The initial vectors and both whole cache spines
remain distinct; no endpoint comparison is supplied as a premise.
-/
theorem difference_le (prepared : path.ConnectionPreparation refinement positive initial)
    {otherInitial : Vec Canonical 2}
    (other : path.ConnectionPreparation refinement positive otherInitial) :
    Norm.vector (zipWith (fun first last => first - last) prepared.value other.value) ≤
      prepared.amplification * Norm.vector (zipWith (fun first last => first - last) initial otherInitial) := by
  induction path generalizing initial otherInitial with
  | nil _ =>
      change Norm.vector (zipWith (fun first last => first - last) prepared.value other.value) ≤
        1 * Norm.vector (zipWith (fun first last => first - last) initial otherInitial)
      rewrite [nil_value prepared, nil_value other, Field.one_mul]
      exact Order.Basic.le_refl _
  | cons _ _ _ prior =>
      have afterTail := prior prepared.tail other.tail
      have afterHead := prepared.head.difference_le_amplification positive other.head
      exact afterTail.trans
        ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct afterHead
          prepared.tail.amplification_nonnegative).trans_eq (by
            change prepared.tail.amplification * (prepared.head.amplification *
                Norm.vector (zipWith (fun first last => first - last) initial otherInitial)) =
              (prepared.tail.amplification * prepared.head.amplification) *
                Norm.vector (zipWith (fun first last => first - last) initial otherInitial)
            ring1))

/-- Concatenate given connection caches while retaining every prefix and suffix execution.

The suffix starts at the actual cached prefix endpoint. The empty prefix
only transports that same whole suffix cache along its certified initial
equality. No original interval selector or Euler executor is invoked.
-/
def append {refinement : Nat} {positive : 0 < refinement} :
    {first junction last : Canonical} → {firstPath : SafePath first junction} →
    {suffix : SafePath junction last} → {initial : Vec Canonical 2} →
    (prepared : firstPath.ConnectionPreparation refinement positive initial) →
    suffix.ConnectionPreparation refinement positive prepared.value →
    (firstPath.append suffix).ConnectionPreparation refinement positive initial
  | _, _, _, .nil _, _, _, prepared, continued => castInitial prepared.property continued
  | _, _, _, .cons _ _ rest, _, _, prepared, continued =>
      ⟨prepared.1, append (firstPath := rest) prepared.2 continued⟩

/-- Concatenation returns the same actual final suffix vector. -/
theorem append_value {first junction last : Canonical} {firstPath : SafePath first junction}
    {suffix : SafePath junction last}
    (prepared : firstPath.ConnectionPreparation refinement positive initial)
    (continued : suffix.ConnectionPreparation refinement positive prepared.value) :
    (prepared.append continued).value = continued.value := by
  induction firstPath generalizing initial with
  | nil _ => exact castInitial_value prepared.property continued
  | cons _ _ _ prior => exact prior prepared.tail continued

/-- Empty-prefix concatenation preserves the whole supplied suffix cache. -/
theorem append_nil_heq {point last : Canonical} {suffix : SafePath point last}
    (prepared : (SafePath.nil point).ConnectionPreparation refinement positive initial)
    (continued : suffix.ConnectionPreparation refinement positive prepared.value) :
    HEq (prepared.append continued) continued := castInitial_heq prepared.property continued

/-- Concatenation keeps the complete first axis cache and its original factory. -/
theorem append_head {last : Canonical} {suffix : SafePath finish last}
    (prepared : (SafePath.cons segment safe remaining).ConnectionPreparation refinement positive initial)
    (continued : suffix.ConnectionPreparation refinement positive prepared.value) :
    (prepared.append continued).1 = prepared.1 := by
  delta append
  rfl

/-- The remaining concatenated spine is the same recursive operation on the original retained tail cache. -/
theorem append_tail {last : Canonical} {suffix : SafePath finish last}
    (prepared : (SafePath.cons segment safe remaining).ConnectionPreparation refinement positive initial)
    (continued : suffix.ConnectionPreparation refinement positive prepared.value) :
    HEq (prepared.append continued).tail (prepared.tail.append continued) := by
  delta tail append
  rfl

end ConnectionPreparation

/-- Fresh execution on a concatenated path agrees with composing its original prefix and suffix preparations.

The equality concerns the complete ordered cache spine. The suffix starts
from the original prefix's computed endpoint; the composition operation
itself only forwards those supplied caches.
-/
theorem prepareConnection_append {first junction last : Canonical}
    (firstPath : SafePath first junction) (suffix : SafePath junction last)
    (refinement : Nat) (positive : 0 < refinement) (initial : Vec Canonical 2) :
    (firstPath.append suffix).prepareConnection refinement positive initial =
      (firstPath.prepareConnection refinement positive initial).append
        (suffix.prepareConnection refinement positive
          (firstPath.prepareConnection refinement positive initial).value) := by
  induction firstPath generalizing initial with
  | nil _ => rfl
  | cons segment safe rest prior =>
      let axis : {value : safe.ConnectionPreparation refinement initial //
          value = safe.prepareConnection refinement positive initial} :=
        ⟨safe.prepareConnection refinement positive initial, rfl⟩
      change (⟨axis, (rest.append suffix).prepareConnection refinement positive axis.val.value⟩ :
          (SafePath.cons segment safe (rest.append suffix)).ConnectionPreparation refinement positive initial) =
        ⟨axis, (rest.prepareConnection refinement positive axis.val.value).append
          (suffix.prepareConnection refinement positive
            (rest.prepareConnection refinement positive axis.val.value).value)⟩
      exact congrArg (fun cached :
          (rest.append suffix).ConnectionPreparation refinement positive axis.val.value =>
        (⟨axis, cached⟩ :
          (SafePath.cons segment safe (rest.append suffix)).ConnectionPreparation refinement positive initial))
        (prior suffix axis.val.value)

/-- The independent final reading on a joined path is the suffix reading initialized by the original prefix endpoint. -/
theorem prepareConnection_append_value {first junction last : Canonical}
    (firstPath : SafePath first junction) (suffix : SafePath junction last)
    (refinement : Nat) (positive : 0 < refinement) (initial : Vec Canonical 2) :
    ((firstPath.append suffix).prepareConnection refinement positive initial).value =
      (suffix.prepareConnection refinement positive
        (firstPath.prepareConnection refinement positive initial).value).value :=
  (congrArg (fun cached : (firstPath.append suffix).ConnectionPreparation refinement positive initial =>
      cached.value) (prepareConnection_append firstPath suffix refinement positive initial)).trans
    (ConnectionPreparation.append_value _ _)

end Purelib.Curves.Legendre.Paths.SafePath

end
