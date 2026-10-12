module

-- The exposed zero vector retains the replication length certificate in its public body.
public import Purelib.Data.List.Replicate

public import Purelib.Data.List.Bool.Xor
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Boolean vectors with retained widths

The original list stores each Boolean coordinate in order. Its length
certificate binds XOR, the all-false vector and equality decisions to that
same supplied width and retained list.
-/

namespace Purelib.Data.Vector

open Purelib.Data.List.Bool
open Purelib.Data.List

-- Preserve the nominal Purelib.Data.Vector.Boolean.Basic.Vector carrier and its generated field API.
set_option genInjectivity false in
/-- Retain a Boolean list with a certificate of its exact displayed width.

The original ordered bits are executable data; the length equality binds all
fixed-width operations to that same list. -/
@[ext]
structure Boolean (width : Nat) where
  /-- The original ordered Boolean entries. -/ bits : List Bool
  /-- The retained bit list has exactly the indexed width. -/ length_eq : bits.length = width

-- Preserve the original nominal Vector.mk.inj certificate name.

constructive_injectivity Boolean

namespace Boolean

end Boolean
namespace Boolean

end Boolean
namespace Boolean.Basic

/-- Build the all-false Boolean vector at the supplied width.

Replication produces one false coordinate per retained width position. The
owned length certificate binds that same list to the displayed vector width. -/
@[expose] def zero (width : Nat) : Boolean width where
  bits := List.replicate width false
  length_eq := Replicate.length_replicate width false

/-- Compute coordinatewise XOR of two retained Boolean vectors of the same width.

The list XOR algorithm consumes their original bit lists, and the stored equal
lengths certify that the resulting list has the same width. -/
@[expose] def xor {width : Nat} (left right : Boolean width) : Boolean width where
  bits := Xor.bitsXor left.bits right.bits
  length_eq := by
    exact (Xor.bitsXor_length_of_eq
      (left.length_eq.trans right.length_eq.symm)).trans left.length_eq

/-- Fixed-width Boolean vector XOR is commutative.

The retained list entries and their supplied length certificates determine the operation; the equality preserves that
same ordered data at the displayed width. -/
theorem xor_comm {width : Nat} (left right : Boolean width) :
    Basic.xor left right = Basic.xor right left := by
  apply Boolean.ext
  exact Xor.bitsXor_comm_of_length_eq
    (left.length_eq.trans right.length_eq.symm)

/-- Fixed-width Boolean vector XOR is associative.

The retained list entries and their supplied length certificates determine the operation; the equality preserves that
same ordered data at the displayed width. -/
theorem xor_assoc {width : Nat} (first second third : Boolean width) :
    Basic.xor (Basic.xor first second) third = Basic.xor first (Basic.xor second third) := by
  apply Boolean.ext
  exact Xor.bitsXor_assoc_of_lengths
    (first.length_eq.trans second.length_eq.symm)
    (second.length_eq.trans third.length_eq.symm)

/-- A Boolean vector XOR itself is the all-false vector of the same width.

The retained list entries and their supplied length certificates determine the operation; the equality preserves that
same ordered data at the displayed width. -/
theorem xor_self {width : Nat} (value : Boolean width) :
    Basic.xor value value = Basic.zero width := by
  apply Boolean.ext
  change Xor.bitsXor value.bits value.bits = List.replicate width false
  rw [Xor.bitsXor_self_eq_false, value.length_eq]

/-- The all-false vector is a left identity for fixed-width XOR.

The retained list entries and their supplied length certificates determine the operation; the equality preserves that
same ordered data at the displayed width. -/
theorem zero_xor {width : Nat} (value : Boolean width) :
    Basic.xor (Basic.zero width) value = value := by
  apply Boolean.ext
  change Xor.bitsXor (List.replicate width false) value.bits = value.bits
  have replicatedEqual : List.replicate width false =
      List.replicate value.bits.length false :=
    congrArg (fun length => List.replicate length false)
      value.length_eq.symm
  exact (congrArg (fun bits => Xor.bitsXor bits value.bits)
    replicatedEqual).trans (Xor.false_bitsXor value.bits)

/-- The all-false vector is a right identity for fixed-width XOR.

The retained list entries and their supplied length certificates determine the operation; the equality preserves that
same ordered data at the displayed width. -/
theorem xor_zero {width : Nat} (value : Boolean width) :
    Basic.xor value (Basic.zero width) = value := by
  apply Boolean.ext
  change Xor.bitsXor value.bits (List.replicate width false) = value.bits
  have replicatedEqual : List.replicate width false =
      List.replicate value.bits.length false :=
    congrArg (fun length => List.replicate length false)
      value.length_eq.symm
  exact (congrArg (fun bits => Xor.bitsXor value.bits bits)
    replicatedEqual).trans (Xor.bitsXor_false value.bits)

/-- Decide equality of Boolean lists by comparing their retained heads and tails.

A mismatched shape or head supplies direct inequality evidence; equal heads recurse
on the original tails and reconstruct list equality. -/
private def boolListDecEq : (left right : List Bool) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse fun impossible => by nomatch impossible
  | _ :: _, [] => isFalse fun impossible => by nomatch impossible
  | left :: leftTail, right :: rightTail =>
      match Bool.decEq left right with
      | isFalse different => isFalse fun equal =>
          different (List.cons.inj equal).1
      | isTrue equal =>
          match Purelib.Data.Vector.Boolean.Basic.boolListDecEq leftTail rightTail with
          | isFalse different => isFalse fun listEqual =>
              different (List.cons.inj listEqual).2
          | isTrue tailEqual => isTrue (by rw [equal, tailEqual])

/-- Decide fixed-width Boolean vector equality through the original bit lists. -/
private def vectorDecEq {width : Nat} (left right : Boolean width) :
    Decidable (left = right) :=
  match Basic.boolListDecEq left.bits right.bits with
  | isTrue equal => isTrue (Boolean.ext equal)
  | isFalse different => isFalse fun vectorEqual =>
      different (congrArg bits vectorEqual)

/-- XOR by a fixed Boolean vector is injective, because applying it twice cancels the
fixed vector. -/
theorem xor_left_injective {width : Nat} (generator : Boolean width) :
    Function.Injective (Basic.xor generator) := by
  intro left right equal
  have canceled := congrArg (Basic.xor generator) equal
  simpa only [← Basic.xor_assoc, Basic.xor_self, Basic.zero_xor] using canceled

/-- An exact XOR identity recovers the generator by XORing its two displayed sides. -/
theorem generator_eq_xor_of_eq_xor {width : Nat}
    {generator left right : Boolean width}
    (equal : left = Basic.xor generator right) :
    generator = Basic.xor left right := by
  calc
    generator = Basic.xor generator (Basic.zero width) := (Basic.xor_zero generator).symm
    _ = Basic.xor generator (Basic.xor right right) := by rw [Basic.xor_self]
    _ = Basic.xor (Basic.xor generator right) right :=
      (Basic.xor_assoc generator right right).symm
    _ = Basic.xor left right := by rw [equal]

end Boolean.Basic
end Purelib.Data.Vector
