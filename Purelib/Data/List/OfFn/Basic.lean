module
import Init.Data.List.OfFn
import Purelib.Data.List.Append
-- Public index numerals retain the original successor nonzero certificate.
public import Purelib.Data.Nat.Order

/-!
# Exact finite function tables

Each theorem retains the original `List.ofFn` enumeration and its bounded
indices. Structural certificates read the same original `Fin.foldr.loop`,
without replacing the table algorithm or equating indexing functions.
-/

public section

namespace Purelib.Data.List.OfFn.Basic
open Purelib.Data.List
open scoped Purelib.Data.Nat

universe u v w

variable {Alpha : Type u} {Beta : Type v} {Gamma : Type w}

/-- Materializing a nonempty finite function table exposes its first entry and successor tail.

A structural certificate follows the original finite fold loop with its
supplied fuel bound and retained tail list. Its successor shift identifies
exactly the original bounded entries without changing the enumeration. -/
theorem ofFn_succ {size : Nat} {function : Fin (size + 1) → Alpha} :
    List.ofFn function = function 0 :: List.ofFn (fun index => function index.succ) := by
  have shifted : ∀ (fuel : Nat) (bound : fuel + 1 ≤ size + 1) (tail : List Alpha),
      Fin.foldr.loop (size + 1) (fun index remaining => function index :: remaining)
          (fuel + 1) bound tail =
        function 0 :: Fin.foldr.loop size
          (fun index remaining => function index.succ :: remaining)
          fuel (Nat.le_of_succ_le_succ bound) tail := by
    intro fuel
    induction fuel with
    | zero => intro bound tail; rfl
    | succ fuel ih =>
        intro bound tail
        exact ih (Nat.le_of_lt bound) (function ⟨fuel + 1, bound⟩ :: tail)
  exact shifted size (Nat.le_refl _) []

/-- Pointwise equal finite indexed families materialize to equal lists.

The equality witness is supplied separately at each retained Fin index; no equality
of indexing functions is required. -/
theorem ofFn_congr {size : Nat} {left right : Fin size → Alpha}
    (equal : ∀ index, left index = right index) :
    List.ofFn left = List.ofFn right := by
  induction size with
  | zero =>
      rw [List.ofFn_zero, List.ofFn_zero]
  | succ size inductionHypothesis =>
      rw [ofFn_succ, ofFn_succ, equal 0,
        inductionHypothesis (fun index => equal index.succ)]

/-- Materializing a successor-size table appends its final entry to the castSucc prefix.

The retained prefix indices keep their natural values, and Fin.last supplies the
final bounded index. Structural table equality preserves the exact order. -/
theorem ofFn_succ_last {size : Nat}
    {function : Fin (size + 1) → Alpha} :
    List.ofFn function =
      List.ofFn (fun index => function index.castSucc) ++
        [function (Fin.last size)] := by
  induction size with
  | zero =>
      rw [ofFn_succ]
      have empty : List.ofFn
          (fun index : Fin 0 => function index.castSucc) = [] :=
        List.ofFn_zero
      rw [empty, List.nil_append]
      apply congrArg List.singleton
      apply congrArg function
      apply Fin.ext
      rfl
  | succ size inductionHypothesis =>
      calc
        List.ofFn function =
            function 0 :: List.ofFn (fun index => function index.succ) :=
          ofFn_succ
        _ = function 0 ::
            (List.ofFn (fun index : Fin size =>
                function index.castSucc.succ) ++
              [function (Fin.last (size + 1))]) := by
          apply congrArg (List.cons (function 0))
          calc
            List.ofFn (fun index : Fin (size + 1) => function index.succ) =
                List.ofFn (fun index : Fin size =>
                    function index.succ.castSucc) ++
                  [function (Fin.last size).succ] :=
              inductionHypothesis
            _ = List.ofFn (fun index : Fin size =>
                    function index.castSucc.succ) ++
                  [function (Fin.last (size + 1))] := by
              have firstEqual :
                  List.ofFn (fun index : Fin size =>
                      function index.succ.castSucc) =
                    List.ofFn (fun index : Fin size =>
                      function index.castSucc.succ) := by
                apply ofFn_congr
                intro index
                apply congrArg function
                apply Fin.ext
                rfl
              have lastEqual : [function (Fin.last size).succ] =
                  [function (Fin.last (size + 1))] := by
                apply congrArg List.singleton
                apply congrArg function
                apply Fin.ext
                rfl
              rw [firstEqual, lastEqual]
        _ = (function 0 :: List.ofFn (fun index : Fin size =>
                function index.castSucc.succ)) ++
              [function (Fin.last (size + 1))] := rfl
        _ = List.ofFn (fun index : Fin (size + 1) =>
                function index.castSucc) ++
              [function (Fin.last (size + 1))] := by
          apply congrArg (fun values =>
            values ++ [function (Fin.last (size + 1))])
          rw [ofFn_succ]
          apply congrArg (List.cons (function 0))
          apply ofFn_congr
          intro index
          apply congrArg function
          apply Fin.ext
          rfl

/-- Materializing a finite table on a sum of sizes concatenates its left and right
subtables.

The left subtable uses castLE with the displayed additive bound; the right subtable
uses natAdd to shift its retained indices by the left size. -/
theorem ofFn_add {leftSize rightSize : Nat}
    {function : Fin (leftSize + rightSize) → Alpha} :
    List.ofFn function =
      List.ofFn (fun index =>
        function (index.castLE (Nat.le_add_right leftSize rightSize))) ++
      List.ofFn (fun index => function (index.natAdd leftSize)) := by
  induction rightSize with
  | zero =>
      have firstEqual : List.ofFn function =
          List.ofFn (fun index : Fin leftSize =>
            function (index.castLE (Nat.le_add_right leftSize 0))) := by
        apply ofFn_congr
        intro index
        apply congrArg function
        apply Fin.ext
        rfl
      calc
        List.ofFn function =
            List.ofFn (fun index : Fin leftSize =>
              function (index.castLE (Nat.le_add_right leftSize 0))) :=
          firstEqual
        _ = List.ofFn (fun index : Fin leftSize =>
              function (index.castLE (Nat.le_add_right leftSize 0))) ++ [] :=
          (Append.append_nil _).symm
        _ = List.ofFn (fun index : Fin leftSize =>
              function (index.castLE (Nat.le_add_right leftSize 0))) ++
            List.ofFn (fun index : Fin 0 =>
              function (index.natAdd leftSize)) := by
          rw [List.ofFn_zero]
  | succ rightSize inductionHypothesis =>
      let prefixFunction : Fin (leftSize + rightSize) → Alpha :=
        fun index => function index.castSucc
      let leftPrevious : Fin leftSize → Alpha := fun index =>
        prefixFunction
          (index.castLE (Nat.le_add_right leftSize rightSize))
      let rightPrevious : Fin rightSize → Alpha := fun index =>
        prefixFunction (index.natAdd leftSize)
      let leftCurrent : Fin leftSize → Alpha := fun index =>
        function
          (index.castLE (Nat.le_add_right leftSize (rightSize + 1)))
      let rightCurrent : Fin (rightSize + 1) → Alpha := fun index =>
        function (index.natAdd leftSize)
      have prefixSplit : List.ofFn prefixFunction =
          List.ofFn leftPrevious ++ List.ofFn rightPrevious :=
        inductionHypothesis
      have leftEqual : List.ofFn leftPrevious =
          List.ofFn leftCurrent := by
        apply ofFn_congr
        intro index
        apply congrArg function
        apply Fin.ext
        rfl
      have rightEqual : List.ofFn rightPrevious =
          List.ofFn (fun index : Fin rightSize =>
            rightCurrent index.castSucc) := by
        apply ofFn_congr
        intro index
        apply congrArg function
        apply Fin.ext
        rfl
      have lastEqual : function (Fin.last (leftSize + rightSize)) =
          rightCurrent (Fin.last rightSize) := by
        apply congrArg function
        apply Fin.ext
        rfl
      have rightSplit : List.ofFn rightCurrent =
          List.ofFn (fun index : Fin rightSize =>
            rightCurrent index.castSucc) ++
            [rightCurrent (Fin.last rightSize)] := ofFn_succ_last
      calc
        List.ofFn function =
            List.ofFn prefixFunction ++
              [function (Fin.last (leftSize + rightSize))] :=
          ofFn_succ_last
        _ = (List.ofFn leftPrevious ++ List.ofFn rightPrevious) ++
              [function (Fin.last (leftSize + rightSize))] := by
          rw [prefixSplit]
        _ = List.ofFn leftPrevious ++
              (List.ofFn rightPrevious ++
                [function (Fin.last (leftSize + rightSize))]) :=
          Append.append_assoc _ _ _
        _ = List.ofFn leftCurrent ++
              (List.ofFn (fun index : Fin rightSize =>
                  rightCurrent index.castSucc) ++
                [rightCurrent (Fin.last rightSize)]) := by
          rw [leftEqual, rightEqual, lastEqual]
        _ = List.ofFn leftCurrent ++ List.ofFn rightCurrent := by
          rw [rightSplit]

/-- The materialized list of a finite indexed family has exactly its domain size.

The original successor table retains one head followed by its bounded tail.
Structural length recursion therefore counts exactly the retained indices. -/
theorem length_ofFn {size : Nat} {function : Fin size → Alpha} :
    (List.ofFn function).length = size := by
  induction size with
  | zero =>
      rw [List.ofFn_zero]
      rfl
  | succ size inductionHypothesis =>
      rw [ofFn_succ, List.length_cons, inductionHypothesis]

/-- Mapping a materialized finite family equals materializing its pointwise images.

Each original bounded index produces the same transformed payload in both
lists. The original table order and the recursive tail remain unchanged. -/
theorem map_ofFn {size : Nat} {function : Fin size → Alpha}
    {transform : Alpha → Beta} :
    (List.ofFn function).map transform =
      List.ofFn (transform ∘ function) := by
  induction size with
  | zero =>
      rw [List.ofFn_zero, List.ofFn_zero]
      rfl
  | succ size inductionHypothesis =>
      rw [ofFn_succ, List.map_cons, ofFn_succ,
        inductionHypothesis]
      rfl

/-- Materializing every retained index of a finite list recovers that exact list.

Each read uses the original index value and its supplied bound certificate.
The first entry and structural tail recover the same retained list spine. -/
theorem ofFn_getElem {α : Type u} (values : List α) :
    List.ofFn (fun index : Fin values.length => values[index.val]'index.isLt) = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      rw [ofFn_succ]
      exact congrArg (List.cons head) ih

/-- A retained finite-table occurrence is exactly one of its original bounded entries.

Structural recursion follows the original head and successor tail of List.ofFn.
Both directions retain the actual Fin index and entry equality; no equality
of functions or proposition rewriting is needed. -/
theorem mem_ofFn {size : Nat} {function : Fin size → Alpha} {value : Alpha} :
    value ∈ List.ofFn function ↔ ∃ index, function index = value := by
  induction size with
  | zero =>
      rw [List.ofFn_zero]
      constructor
      · intro impossible
        nomatch impossible
      · intro witness
        rcases witness with ⟨index, _⟩
        exact (Nat.not_lt_zero index.val index.isLt).elim
  | succ size inductionHypothesis =>
      rw [ofFn_succ]
      constructor
      · intro member
        cases member with
        | head => exact ⟨0, rfl⟩
        | tail _ member =>
            rcases inductionHypothesis.mp member with ⟨index, equal⟩
            exact ⟨index.succ, equal⟩
      · intro witness
        rcases witness with ⟨⟨indexValue, indexBound⟩, equal⟩
        cases indexValue with
        | zero =>
            exact equal ▸ List.Mem.head _
        | succ indexValue =>
            have tailBound : indexValue < size :=
              Nat.lt_of_succ_lt_succ indexBound
            exact List.Mem.tail _
              (inductionHypothesis.mpr ⟨⟨indexValue, tailBound⟩, equal⟩)

/-- Reading a materialized finite family at its original bounded index recovers that entry.

The original head and successor tail of List.ofFn retain every domain index.
Structural induction reads the same list occurrence with its supplied bound,
without equating functions or changing the table enumeration.
-/
theorem getElem_ofFn {size : Nat} (function : Fin size → Alpha)
    (index : Fin size) (bound : index.val < (List.ofFn function).length) :
    (List.ofFn function)[index.val]'bound = function index := by
  induction size with
  | zero => exact (Nat.not_lt_zero index.val index.isLt).elim
  | succ size inductionHypothesis =>
      refine (getElem_congr (ofFn_succ (function := function))
        (Eq.refl index.val) bound).trans ?_
      cases index with
      | mk value bounded =>
          cases value with
          | zero => exact Eq.refl _
          | succ value =>
              have tailBound : value <
                  (List.ofFn (fun index : Fin size => function index.succ)).length := by
                rewrite [length_ofFn]
                exact Nat.lt_of_succ_lt_succ bounded
              exact inductionHypothesis (fun index : Fin size => function index.succ)
                ⟨value, Nat.lt_of_succ_lt_succ bounded⟩ tailBound

end Purelib.Data.List.OfFn.Basic

namespace Purelib.Data.List.OfFn.Basic

/-- Casting an exact retained length preserves indexed materialization of a list map.

The supplied equality casts each original finite index to the list's own bound.
Materialization then reads the same ordered entries and applies the same map. -/
public theorem ofFn_map_cast {Alpha Beta : Type} (entries : List Alpha) {count : Nat}
    (equal : count = entries.length) (value : Alpha → Beta) :
    List.ofFn (fun index : Fin count => value (entries[(Fin.cast equal index).val]'(Fin.cast equal index).isLt)) =
      entries.map value := by
  cases equal
  exact (map_ofFn (function := fun index : Fin entries.length => entries[index.val]'index.isLt)
    (transform := value)).symm.trans (congrArg (List.map value) (ofFn_getElem entries))

end Purelib.Data.List.OfFn.Basic
