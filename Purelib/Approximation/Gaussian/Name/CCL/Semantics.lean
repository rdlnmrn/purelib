module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.CCL.Transducer.Machine.Semantics.Step
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Transducer.Machine.Committed

open Purelib

open Purelib.Approximation

open Purelib.Data.CCL.Encoding.Parser

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.CCL.Transducer.Machine.Committed

open Purelib.Data.CCL.Transducer.Machine.Semantics.Basic

open Purelib.Data.CCL.Transducer.Mode.Semantics

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line

section
@[expose] public section

/-!
# Exact projective semantics of progressive arithmetic cursors

The raw `Machine` remains the original bit-only cursor.  This module adds a
separate proof wrapper relating its quantitative mode to the ordinary raw
parser matrix.  In particular, residual modes are interpreted homogeneously
as `[1 : γr]`; this is an affine inverse tail when `r ≠ 0` and is exactly
`ω` when `r = 0`.  No equality decision on a completed value is needed.
-/

namespace Purelib.Approximation.Gaussian.Name.CCL.Semantics
namespace Named

/-- Every progressive arithmetic name starts with an exact empty raw cursor. -/
theorem machine_exact (name : Gaussian.Name.Basic.Named)
  :
    Semantics.Basic.ExactCursor name.process name.state name.machine :=
  ExactCursor.initial name.process name.state

/-- Every finite prefix requested from a progressive arithmetic name remains an exact raw CCL prefix for some candidate
admitted by the original finite process state. -/
theorem advance_exact (name : Gaussian.Name.Basic.Named)
  (count : Nat) :
    Semantics.Basic.ExactCursor name.process name.state (Advance.advance name.machine count) :=
  (machine_exact name).advance count

/-- Pointwise form of `advance_exact`, convenient for arithmetic clients: every tail admitted by the quantitative
sidecar after a finite request reconstructs an original process candidate through the pure raw parser. -/
theorem advance_candidate_exact (name :
  Gaussian.Name.Basic.Named) (count : Nat)
    {tail : Data.Gaussian.Basic.Canonical}
    (possible : SemanticMode.possible (Advance.advance name.machine count).mode tail) :
    ∃ value : Data.Gaussian.Basic.Canonical,
      name.process.Possible name.state value ∧
        (Line.Matrix.act
          (State.parse
            (Data.CCL.Transducer.Machine.committed (Advance.advance name.machine count))).matrix
          (SemanticMode.parserTail
            (Advance.advance name.machine count).mode tail)).Equivalent
              (Proj.affine value) :=
  (advance_exact name count).exact possible

end Named

end Purelib.Approximation.Gaussian.Name.CCL.Semantics

end
