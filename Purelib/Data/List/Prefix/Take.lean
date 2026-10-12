module

section
public section

/-!
# Finite CCL prefixes for robust approximation-sharpness runs

The RFAP construction can compute any requested finite same-source run, but
its displayed rational source depends on the final run length.  This module
therefore reserves one finite final run before exposing intermediate states.
Every state uses the same robust box, rational sample, and complete finite CCL
encoding, and reveals only initial segments of the reserved windows and word.
This is the finite prefix-coherent statement: it neither forms an infinite
stream nor asserts compatibility between independently constructed final
runs.
-/

section

namespace Purelib.Data.List.Prefix.Take
/-- Taking fewer entries of a finite list gives a prefix of a longer take.

The earlier count must not exceed the later count. Structural recursion supplies the
actual remaining suffix witnessing the prefix relation. -/
theorem takePrefixTakeDirect
    {item : Type} :
    (values : List item) → (earlier later : Nat) → earlier ≤ later →
      (values.take earlier).IsPrefix (values.take later)
  | values, 0, later, _order => ⟨values.take later, rfl⟩
  | [], _earlier + 1, 0, order => nomatch order
  | [], _earlier + 1, _later + 1, _order => ⟨[], rfl⟩
  | _head :: _tail, _earlier + 1, 0, order => nomatch order
  | head :: tail, earlier + 1, later + 1, order => by
      rcases Purelib.Data.List.Prefix.Take.takePrefixTakeDirect tail earlier later
          (Nat.le_of_succ_le_succ order) with ⟨suffix, prefixProof⟩
      exact ⟨suffix, congrArg (head :: ·) prefixProof⟩
end Purelib.Data.List.Prefix.Take

end

end

namespace Purelib.Data.List.Prefix.Take

/-- Increasing a take by one appends the original optional indexed entry.

Structural induction preserves the list's original indexed read and supplies
the equality for requests both within and beyond its length. -/
public theorem take_add_one {Alpha : Type u} (entries : List Alpha) (count : Nat) :
    entries.take (count + 1) = entries.take count ++ entries[count]?.toList := by
  induction entries generalizing count with
  | nil => cases count <;> rfl
  | cons entry remaining ih =>
      cases count with
      | zero => rfl
      | succ count => exact congrArg (entry :: ·) (ih count)

/-- Taking an initial segment retains the smaller of its request and original length.

Structural recursion follows the original take operation. The two natural
comparison branches keep the same displayed entries and exact request count. -/
public theorem length_take {Alpha : Type u} (entries : List Alpha) (count : Nat) :
    (entries.take count).length = min count entries.length := by
  induction count generalizing entries with
  | zero => rfl
  | succ count ih =>
      cases entries with
      | nil => rfl
      | cons entry remaining =>
          change (remaining.take count).length + 1 = min (count + 1) (remaining.length + 1)
          rw [ih]
          by_cases within : count ≤ remaining.length
          · simp only [-eq_self, -iff_self, Nat.min_def, if_pos within,
              if_pos (Nat.succ_le_succ within)]
            rfl
          · have beyond : ¬ count + 1 ≤ remaining.length + 1 :=
              fun ordered => within (Nat.le_of_succ_le_succ ordered)
            simp only [-eq_self, -iff_self, Nat.min_def, if_neg within, if_neg beyond]
            rfl

/-- A take within the original list length retains exactly the requested length. -/
public theorem length_take_of_le {Alpha : Type u} {entries : List Alpha} {count : Nat}
    (within : count ≤ entries.length) : (entries.take count).length = count :=
  (length_take entries count).trans (if_pos within)

/-- Dropping at least the original list length leaves no occurrences.

The proof removes one original head and one requested drop at each step;
its retained natural bound supplies the corresponding tail bound. -/
public theorem drop_eq_nil_of_le {Alpha : Type u} {entries : List Alpha} {count : Nat}
    (exhausted : entries.length ≤ count) : entries.drop count = [] := by
  induction entries generalizing count with
  | nil => cases count <;> rfl
  | cons entry remaining ih =>
      cases count with
      | zero => nomatch exhausted
      | succ count => exact ih (Nat.le_of_succ_le_succ exhausted)

end Purelib.Data.List.Prefix.Take
