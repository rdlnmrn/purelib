module

/-!
# Structural finite-list lemmas

The upstream statements replaced here concern only structural recursion over
displayed finite lists.  Their current proof routes use generic simplifier or
extensionality infrastructure that reaches `Quot.sound`.  These versions keep
the same mathematical content while exposing the finite recursion directly.
-/

public section

namespace Purelib.Data.List

universe u v w

variable {Alpha : Type u} {Beta : Type v} {Gamma : Type w}

/-- A subtype value whose underlying entry occurs in a list occurs in its attachment.

Structural recursion follows the original membership witness while retaining the
same predicate and its supplied certificate on every remaining entry. Proof
irrelevance identifies the certificates attached to the same underlying value. -/
private theorem mem_attachWith {predicate : Alpha → Prop} :
    ∀ (values : List Alpha) (certificate : ∀ value ∈ values, predicate value)
      (attached : {value // predicate value}),
      attached.val ∈ values → attached ∈ values.attachWith predicate certificate
  | [], _, _, member => by
      nomatch member
  | head :: tail, certificate, ⟨value, property⟩, member => by
      cases member with
      | head => exact List.Mem.head _
      | tail _ tailMember =>
          exact List.Mem.tail _ (mem_attachWith tail
            (fun value member => certificate value (List.Mem.tail head member))
            ⟨value, property⟩ tailMember)

/-- Every value paired with its membership proof occurs in the attached list.

Structural recursion follows the retained membership witness through the original
attachment constructors. The attached value keeps its original list owner and
its supplied membership certificate. -/
theorem Attach.mem_attach (values : List Alpha)
    (attached : {value // value ∈ values}) : attached ∈ values.attach :=
  mem_attachWith values (fun _ member => member) attached attached.property
end Purelib.Data.List

end

/-!
# Direct finite attachment erasure

The upstream map/attachment proof currently reaches `Quot.sound` through a
function-extensionality proof of `List.map_id`.  These equalities follow directly by
structural recursion over the displayed list; no function extensionality or
quotient reasoning is needed.
-/

public section

namespace Purelib.Data.List

universe u

variable {Alpha : Type u}

/-- Erasing certificates from an attached finite list recovers its original entries.

Each list member carries the supplied predicate certificate. Mapping the subtype
value projection preserves the list's order and multiplicity exactly. -/
theorem attachWith_map_subtype_val {predicate : Alpha → Prop} :
    ∀ (values : List Alpha) (certificate : ∀ value ∈ values, predicate value),
      (values.attachWith predicate certificate).map Subtype.val = values
  | [], _ => rfl
  | head :: tail, certificate =>
      congrArg (List.cons head) (attachWith_map_subtype_val tail
        (fun value member => certificate value (List.mem_cons_of_mem head member)))

/-- Erasing membership proofs from List.attach recovers the original list. -/
theorem attach_map_subtype_val (values : List Alpha) :
    values.attach.map Subtype.val = values :=
  attachWith_map_subtype_val values (fun _ member => member)

end Purelib.Data.List

end
