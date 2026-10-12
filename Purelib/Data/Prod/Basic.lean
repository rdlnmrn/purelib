module

-- Public tuple rendering retains the original Repr and ReprTuple dictionaries.
public import Init.Data.Repr
public import Purelib.Data.Format.Basic

/-!
# Representations of original product coordinates

The original tuple renderer retains the supplied coordinate dictionaries,
reverse accumulation, parentheses and finite Format separator tree.
-/

namespace Purelib.Data.Prod

open Purelib.Data

/-- Render a product with the original tuple coordinates and parenthesis layout.

The supplied ReprTuple dictionary retains flattened right coordinates. Its
original reversed accumulation and comma-line separators determine the tree. -/
@[expose] public def repr {Alpha : Type u} {Beta : Type v} [Repr Alpha] [ReprTuple Beta]
    (value : Alpha × Beta) (_precedence : Nat) : Std.Format :=
  match value with
  | (first, remaining) => Std.Format.bracket "("
      (Format.joinSep (reprTuple remaining [_root_.repr first]).reverse
        ("," ++ Std.Format.line)) ")"

end Purelib.Data.Prod
