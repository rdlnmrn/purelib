module

/-! Structural splitting of finite lists into alternating positions. -/

namespace Purelib.Data.List.Split.Alternating

/-- Split a finite list into the entries at alternating positions.

The first output receives positions zero, two and so on; the second receives
positions one, three and so on. Each recursive step consumes two entries without a
preliminary length traversal. -/
@[expose] public def split {Data : Type} : List Data → List Data × List Data
  | [] => ([], [])
  | [value] => ([value], [])
  | first :: second :: remaining =>
      let halves := split remaining
      (first :: halves.1, second :: halves.2)

end Purelib.Data.List.Split.Alternating
