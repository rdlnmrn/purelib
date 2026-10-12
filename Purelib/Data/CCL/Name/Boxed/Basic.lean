module

import Purelib.Data.Gaussian.Basic
public import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
public import Purelib.Data.List.Basic
public import Purelib.Geometry.Rational.Box.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Finite boxed CCL names

This module formalizes the operational boxed-name interface independently of
arithmetic.  A certificate contains one ordinary finite raw word, one
rational box, and one displayed nonzero rational witness.  A progressive
name returns only further finite certificates.  It never forms a completed
bitstream, a completed complex value, or an intersection of all boxes.
-/

namespace Purelib.Data.CCL.Name.Boxed.Basic

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Geometry.Rational in
set_option genInjectivity false in
/-- Retain an inhabited nonzero CCL word cylinder and a rational box enclosing all its possible values.

The certificate stores the exact word, a nonzero represented Gaussian witness and the enclosing box. Its enclosure proof
covers every nonzero Gaussian represented by that same word. -/
structure Certificate where
  /-- The exact finite CCL word defining the retained cylinder. -/ word : Basic.BinaryWord
  /-- The retained rational box enclosing every nonzero value represented by this word. -/ box : Box
  /-- A retained Gaussian witness for this exact word cylinder. -/ witness : Basic.Canonical
  /-- The retained witness is nonzero. -/ witness_nonzero : witness ≠ 0
  /-- The retained word represents this exact witness. -/ witness_represented : Parser.Semantics.Prefix.Represented word
    witness
  /-- Every nonzero Gaussian represented by this same word lies in the retained box. -/ encloses : ∀ {value :
    Basic.Canonical}, value ≠ 0 →
    Parser.Semantics.Prefix.Represented word value → box.Contains value

constructive_injectivity Certificate

namespace Certificate

open Purelib.Data.CCL in
/-- The retained represented witness lies in its certificate's exact enclosing box. -/
theorem witness_inside (certificate : Certificate)
  :
    certificate.box.Contains certificate.witness :=
  certificate.encloses certificate.witness_nonzero
    certificate.witness_represented

open Purelib.Data.CCL in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
/-- Require a nonzero Gaussian represented by the certificate's exact retained word. -/
def Possible (certificate : Certificate) (value :
  Basic.Canonical) : Prop :=
  value ≠ 0 ∧ Parser.Semantics.Prefix.Represented certificate.word value

open Purelib.Data.CCL in
open Purelib.Data.Gaussian in
/-- Every possible value of the retained certificate belongs to its exact box. -/
theorem possible_inside {certificate :
  Certificate} {value : Basic.Canonical}
    (possible : certificate.Possible value) :
    certificate.box.Contains value :=
  certificate.encloses possible.1 possible.2

end Certificate

end Purelib.Data.CCL.Name.Boxed.Basic

end

section
section
@[expose] public section

/-!
# Finite enclosure representations and direct translations

This module instantiates the generic protocol for rational balls, rational
boxes, boxed raw CCL prefixes, finite fast-Cauchy indices, and states of an
arbitrary progressive enclosure process.
-/

namespace Purelib.CCL.Translation
namespace Ball
end Ball
end Purelib.CCL.Translation

end

end
