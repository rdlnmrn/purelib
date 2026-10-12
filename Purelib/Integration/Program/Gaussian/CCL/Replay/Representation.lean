module
import Purelib.Approximation.Gaussian.Process.Recipe.Cursor
import Purelib.Integration.Program.Gaussian.Cached.Basic
public import Purelib.Data.CCL.Transducer.Emission.Basic
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Replay.Emission
import Purelib.Data.CCL.Transducer.Replay.Mode

public import Purelib.Approximation.Gaussian.Process.Normalization.Data.Correspondence
public import Purelib.Integration.Program.Gaussian.Query.CursorRepresentation

open Purelib.Approximation.Gaussian.Process.Recipe (Cursor)

section
@[expose] public section

/-!
# Projection from the finite replay controller to certified execution

The relation is proof-facing only.  Its process and source-index map never
enter the executable replay state.  Chart constructors derive the relation
from the original cached program; clients do not supply a simulation oracle.
-/

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Representation

open Purelib.Data.Gaussian.Basic.Canonical
namespace CursorRep
end CursorRep

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian.Cached in
open Purelib.Integration.Program.Gaussian.Query in
/-- Correspondence between an original process-backed transducer mode and its retained replay mode.

Each constructor keeps the exact process-state cursor representation and the original count, regular kind or residual
upper bound. -/
inductive ModeRep (program : Basic.CachedProgram)
  : Data.CCL.Transducer.Mode → Data.CCL.Transducer.Replay.Mode → Prop where
  /-- The retained cursor represents the exact original initial process state. -/ | initial (actual :
    Mode.Basic.InitialState) (cursor : Cursor)
      (represented : CursorRepresentation.CursorRep program cursor actual.process actual.state) :
      ModeRep program (.initial actual) (.initial cursor)
  /-- The retained cursor and count represent the exact original low-mode state. -/ | low (actual : Mode.Basic.LowState)
    (cursor : Cursor)
      (represented : CursorRepresentation.CursorRep program cursor actual.process actual.state) :
      ModeRep program (.low actual) (.low actual.count
        cursor)
  /-- The retained cursor, kind, count and domain represent the exact original loop state. -/ | loop (actual :
    Mode.Basic.LoopState) (cursor : Cursor)
      (represented : CursorRepresentation.CursorRep program cursor actual.process actual.state) :
      ModeRep program (.loop actual) (.loop actual.kind
        actual.count cursor (Process.Normalization.Data.Correspondence.Domain.ofActual actual.domain))
  /-- The retained cursor, count and upper bound represent the exact original residual state. -/ | residual (actual :
    Mode.Basic.ResidualState) (cursor : Cursor)
      (represented : CursorRepresentation.CursorRep program cursor actual.process actual.state) :
      ModeRep program (.residual actual) (.residual
        cursor actual.count actual.upper)

open Purelib.Data.CCL.Transducer in
open Purelib.Integration.Program.Gaussian in
open Purelib.Integration.Program.Gaussian.Cached in
/-- The replay emission has the exact original emitted bits and a corresponding retained next mode. -/
def EmissionRep (program : Basic.CachedProgram)
  (emission : Data.CCL.Transducer.Replay.Emission)
    (actual : Data.CCL.Transducer.Emission) : Prop :=
  emission.bits = actual.bits ∧ ModeRep program actual.next emission.next

end Purelib.Integration.Program.Gaussian.CCL.Replay.Representation

end
