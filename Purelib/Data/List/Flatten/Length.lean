module

namespace Purelib.Data.List.Flatten.Length

/-- Replacing each list entry by a displayed pair doubles its length.

Each original occurrence contributes two consecutive entries in the flat-map.
Structural recursion preserves their order and multiplicity and accounts for
those entries by two successor steps on the retained tail length. -/
public theorem flatMap_pair_length {A B : Type}
    (left right : A → B) : ∀ values : List A,
    (values.flatMap fun value => [left value, right value]).length =
      2 * values.length
  | [] => rfl
  | _ :: remaining =>
      (congrArg (fun length => Nat.succ (Nat.succ length))
        (flatMap_pair_length left right remaining)).trans
          (Nat.mul_succ 2 remaining.length).symm

end Purelib.Data.List.Flatten.Length
