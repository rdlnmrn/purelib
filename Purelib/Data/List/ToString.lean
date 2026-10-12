module

-- Exposed rendering and its public scoped instance retain the original native append owner.
public import Purelib.Data.String.Basic
-- Public list representations retain their original Format and element-rendering contracts.
public import Init.Data.Repr
public import Purelib.Data.Format.Basic

/-!
# Rendering original finite lists

The original element rendering instance and ordered list spine determine the
same bracketed comma-separated grammar. Empty and singleton lists retain their
original shorter branches; longer lists reuse the same left-fold accumulator.
-/

namespace Purelib.Data.List

open Purelib.Data
open Purelib.Data.String (append)

universe u

set_option backward.match.sparseCases false in
/-- Render an original finite list with brackets and comma-separated element strings.

Every original element is rendered once with its supplied ToString instance.
Empty and singleton lists retain their original branches; a longer list uses
the same left fold, separators and trailing bracket on its retained tail. -/
@[expose] public def toString {Alpha : Type u} [ToString Alpha] : List Alpha → String
  | [] => "[]"
  | [value] => append (append "[" (ToString.toString value)) "]"
  | first :: second :: tail =>
      append ((second :: tail).foldl
        (fun rendered value => append (append rendered ", ") (ToString.toString value))
        (append "[" (ToString.toString first))) "]"

/-- Select the original finite-list rendering grammar with retained native String append.

The same original List carrier and supplied element renderer determine every
entry. Opening this scope retains the original occurrence order and supplied element
renderer while selecting the owned native append for brackets and separators. -/
public scoped instance (priority := 1001) {Alpha : Type u} [ToString Alpha] :
    ToString (List Alpha) where
  toString := toString

/-- Render an original list with its supplied element representations and bracket layout.

The empty list retains its original literal tree. Every nonempty list uses the
same bracket nesting, comma-line separator and original element dictionaries. -/
@[expose] public def repr {Alpha : Type u} [Repr Alpha]
    (values : List Alpha) (_precedence : Nat) : Std.Format :=
  letI : Std.ToFormat Alpha := ⟨_root_.repr⟩
  match values with
  | [] => "[]"
  | first :: remaining => Std.Format.bracket "["
      (Format.joinSep (first :: remaining) ("," ++ Std.Format.line)) "]"

end Purelib.Data.List
