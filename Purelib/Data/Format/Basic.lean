module

-- The public finite formatting operation retains the original Format carrier and ToFormat contract.
public import Init.Data.Format.Basic

/-!
# Separation of finite formatted occurrences

Formatting retains the original Std.Format tree, element renderer and ordered
list occurrences. The separator and fold are the original operations.
-/

namespace Purelib.Data.Format

/-- Intercalate the original formatted entries with the supplied separator.

The empty and singleton lists retain their original shorter branches. A longer
list folds through its unchanged tail, formatting every entry in original order. -/
@[expose] public def joinSep {Alpha : Type u} [Std.ToFormat Alpha]
    (values : List Alpha) (separator : Std.Format) : Std.Format :=
  match values with
  | [] => .nil
  | first :: remaining =>
    match remaining with
    | [] => Std.format first
    | second :: tail => (second :: tail).foldl
        (fun accumulated value => accumulated ++ separator ++ Std.format value) (Std.format first)

end Purelib.Data.Format
