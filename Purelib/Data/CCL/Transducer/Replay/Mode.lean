module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Process.Normalization.Data
public import Purelib.Approximation.Gaussian.Process.Recipe.Cursor
public import Purelib.Data.CCL.Transducer.Mode.Basic

section
@[expose] public section

/-!
# Finite numerical controller and adaptive replay

All executable state below is finite chart syntax, rational bounds, natural
source indices and bit lists.  In particular, neither a `Process` nor a
source evaluator occurs in a returned state.  Each productive chunk records
its model reads, including the second read after a residual inverse chart
change.  Buffered bits do not perform a model query.

This is the numerical interpreter.  Its connection to the certified
transducer is established separately; successful replay of an invented log
does not certify global coherence of its replies.
-/

namespace Purelib.Data.CCL.Transducer.Replay

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain the executable replay mode, exact recipe cursor and phase-specific normalization data.

Initial and low modes retain their cursor and count; loop mode also retains its regular kind and domain data. Residual
mode stores its cursor, count and rational upper bound without replacing those observations by a new process owner. -/
inductive Mode where
  /-- Retain the exact recipe cursor before initial normalization. -/
  | initial (cursor : Approximation.Gaussian.Process.Recipe.Cursor)
  /-- Retain the low-normalization count and exact recipe cursor. -/ | low (count : Nat) (cursor :
    Approximation.Gaussian.Process.Recipe.Cursor)
  /-- Retain the regular kind, count, exact cursor and normalization domain data. -/ | loop (kind :
    Mode.Basic.RegularKind) (count : Nat) (cursor : Approximation.Gaussian.Process.Recipe.Cursor) (domain :
    Process.Normalization.Data.Domain)
  /-- Retain the residual cursor, padding count and rational upper bound. -/ | residual (cursor :
    Approximation.Gaussian.Process.Recipe.Cursor) (count : Nat) (upper : Fraction.Rational)
deriving DecidableEq

constructive_injectivity Mode

end Purelib.Data.CCL.Transducer.Replay

end
