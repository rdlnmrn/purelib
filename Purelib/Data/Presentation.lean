module

namespace Purelib.Data

universe u

set_option genInjectivity false in
/-- An explicit recognition and equality contract for presentations of an object.

The code carrier and its finite representation are supplied by the caller. Valid
codes are compared by an equivalence relation, which need not be literal code
equality. This record does not certify the code carrier or its dependencies. -/
public structure Presentation (Code : Type u) where
  /-- The admissible codes. -/
  Valid : Code → Prop
  /-- Decide admissibility with evidence for either answer. -/
  recognize : DecidablePred Valid
  /-- Equality of the objects represented by admissible codes. -/
  Same : {code : Code // Valid code} → {code : Code // Valid code} → Prop
  /-- Decide represented equality with evidence for either answer. -/
  compare : DecidableRel Same
  /-- Represented equality is an equivalence relation. -/
  same_laws : Equivalence Same

end Purelib.Data
