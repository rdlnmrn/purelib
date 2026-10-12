module

public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.History
public import Purelib.Geometry.CCL.Prefix.Path
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.List.Append
import Purelib.Data.List.Membership

/-!
# Joint unreserved sharpness windows and exact raw CCL prefixes

A retained state shares one proper box between its complete robust window
history and exact raw-prefix enclosure. Each finite request places new
windows beyond all earlier scales, refines the same cached prefix into that
box, constructs the requested new bits and retains one rational realization
satisfying both the old windows and the exact exposed word.

Start with `History.reserve` for specified initial window and bit counts,
or `History.ofWindowHistory` for an existing robust window owner. Apply
`History.extend` to each later `History.Request` and read `Extension.next`.
The receipt's window, word, box and witness transports use the same actual
parents and caches; clients need no record reconstruction.

The word is realized by `Encoding.Parser.Semantics.Prefix.Represented`:
its cached parser state has an affine tail satisfying the original phase
constraints. Each next bit preserves the parser's half-open decisions and
excludes the finite terminal inputs before taking that step. Complete
terminal encodings and residual-zero padding have separate contracts.
-/

public section

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.CCL
open Purelib.Geometry.Rational
open Purelib.NumberTheory.Approximation
open Purelib.NumberTheory.Approximation.Dirichlet.Critical

set_option genInjectivity false in
/-- Retain one proper joint enclosure for the exact window history, exposed raw CCL prefix and rational witness.

The original window segments and prefix parser caches remain separate
owners. Their exact box equality identifies the common enclosure. The
rational witness retains its integral fraction, cached inverse-chart tail
and complete raw-prefix realization; no terminal padding is used.
-/
structure History (threshold : Fraction.Rational) (certificate : Sharpness.IsSharperWindowThreshold threshold) where
  /-- The actual retained robust window history with all original run owners. -/ robust :
    Robust.WindowHistory threshold certificate
  /-- The actual exposed raw-prefix enclosure with its parser and inverse cache. -/ enclosure :
    Encoding.Prefix.Enclosure
  /-- Both original owners use the exact same proper box. -/ boxEq : enclosure.box = robust.box
  /-- The actual cached nonzero rational witness realizing the exposed word. -/ witness :
    Encoding.Prefix.Enclosure.Realization enclosure

namespace History

variable {threshold : Fraction.Rational} {certificate : Sharpness.IsSharperWindowThreshold threshold}

/-- Start a joint state from one retained robust window history and an empty exact raw prefix. -/
@[expose] def ofWindowHistory (robust : Robust.WindowHistory threshold certificate) :
    History threshold certificate := by
  let enclosure := Encoding.Prefix.Enclosure.ofBox robust.box robust.proper
  exact ⟨robust, enclosure, rfl, enclosure.realize⟩

/-- Read the actual common prefix box without reconstructing either retained owner. -/
@[expose] def box (history : History threshold certificate) : Box := history.enclosure.box

/-- Read the exact cached exposed raw word. -/
@[expose] def word (history : History threshold certificate) : List Bool := history.enclosure.word

/-- Read the exact cached rational witness without converting its retained fraction again. -/
@[expose] def point (history : History threshold certificate) : Gaussian.Basic.Canonical := history.witness.point

/-- The common retained box has positive width and height. -/
theorem proper (history : History threshold certificate) : history.box.Proper := history.enclosure.proper

/-- The actual cached witness lies in the same common retained box. -/
theorem point_inside (history : History threshold certificate) : history.box.Contains history.point :=
  history.witness.sample.inside

/-- The cached rational witness realizes the exact exposed word under the original affine raw-prefix semantics. -/
theorem wordRepresented (history : History threshold certificate) :
    Encoding.Parser.Semantics.Prefix.Represented history.word history.point := history.witness.wordRepresented

/-- Every actual retained window is completely consecutive best at the same displayed rational witness. -/
theorem consecutive (history : History threshold certificate) (entry : Robust.WindowHistory.Entry threshold)
    (member : entry ∈ history.robust.windows) :
    Best.Consecutive.Basic.AreConsecutiveBest history.point entry.2.lower entry.2.upper :=
  history.robust.uniformConsecutive history.point (history.boxEq ▸ history.point_inside) entry member

/-- Every actual retained window violates the requested threshold at the same displayed rational witness. -/
theorem violation (history : History threshold certificate) (entry : Robust.WindowHistory.Entry threshold)
    (member : entry ∈ history.robust.windows) :
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance history.point entry.2.lower entry.2.upper :=
  history.robust.uniformViolation history.point (history.boxEq ▸ history.point_inside) entry member

set_option genInjectivity false in
/-- A joint extension request gives the scale floor and exact additional window and bit counts. -/
structure Request where
  /-- The lower denominator-scale floor requested for every new window. -/ requestedScale : Nat
  /-- The exact number of additional windows requested beyond the current history. -/ additionalWindows : Nat
  /-- The exact number of additional raw bits requested beyond the exposed word. -/ additionalBits : Nat

set_option genInjectivity false in
/-- Retain the actual joint construction extending one original state beyond its earlier window and bit reserves.

The new homographic window placement, refined original prefix, finite bit
path and final window refinement retain their exact source and target
owners. The final rational witness uses the same joint box; all original
windows and the exact exposed word remain prefixes of the returned data.
-/
structure Extension (previous : History threshold certificate) (request : Request) where
  /-- The actual new homographic window segment and its retained numerical caches. -/ windowGrowth :
    Robust.WindowHistory.Extension previous.robust request.requestedScale request.additionalWindows
  /-- The new robust window box refines the original prefix enclosure. -/ windowsRefinePrefix :
    windowGrowth.next.box.Refines previous.enclosure.box
  /-- The actual earlier prefix refined into the new robust window box. -/ prefixStart : Encoding.Prefix.Enclosure
  /-- The refinement consumes the exact old word, parser, inverse cache and new window box. -/ prefixStartSpec :
    prefixStart = previous.enclosure.refine windowGrowth.next.box windowGrowth.next.proper windowsRefinePrefix
  /-- The actual finite geometric continuation for the additional-bit request. -/ prefixPath :
    Geometry.CCL.Prefix.Path prefixStart request.additionalBits
  /-- The actual final prefix box refines the same newly placed robust window box. -/ pathRefinesWindows :
    prefixPath.result.box.Refines windowGrowth.next.box
  /-- The actual final refinement retains every new and earlier window record and complete certificate. -/ refinement :
    Robust.WindowHistory.Refinement windowGrowth.next prefixPath.result.box
  /-- The window refinement consumes that same actual final prefix box and containment proof. -/ refinementSpec :
    refinement = windowGrowth.next.refine prefixPath.result.box prefixPath.result.proper pathRefinesWindows
  /-- The complete resulting joint state and its cached rational realization. -/ next : History threshold certificate
  /-- The resulting state retains the actual final window-refinement owner. -/ nextRobust :
    next.robust = refinement.next
  /-- The resulting state retains the actual final prefix enclosure from the finite bit path. -/ nextPrefix :
    next.enclosure = prefixPath.result

/-- Extend the exact retained windows and exposed word by every requested finite increment.

The constructor places the new windows inside the original common proper
box. It refines the earlier prefix using its existing parser and inverse
cache, constructs the additional bits by finite recurrence, then transports
all complete window laws to that exact final prefix box. The resulting
rational realization satisfies both parents without changing an exposed bit.
-/
def extend (previous : History threshold certificate) (request : Request) : Extension previous request := by
  let windowGrowth := previous.robust.extend request.requestedScale request.additionalWindows
  have windowRefines := Box.Refinement.StrictInterior.refines windowGrowth.nested
  have windowsRefinePrefix : windowGrowth.next.box.Refines previous.enclosure.box := previous.boxEq.symm ▸ windowRefines
  let prefixStart := previous.enclosure.refine windowGrowth.next.box windowGrowth.next.proper windowsRefinePrefix
  let prefixPath := Geometry.CCL.Prefix.Path.build prefixStart request.additionalBits
  have pathRefinesWindows : prefixPath.result.box.Refines windowGrowth.next.box := prefixPath.refines
  let refinement := windowGrowth.next.refine prefixPath.result.box prefixPath.result.proper pathRefinesWindows
  let enclosure := prefixPath.result
  let next : History threshold certificate :=
    { robust := refinement.next
      enclosure := enclosure
      boxEq := refinement.boxEq.symm
      witness := enclosure.realize }
  exact
    { windowGrowth := windowGrowth
      windowsRefinePrefix := windowsRefinePrefix
      prefixStart := prefixStart
      prefixStartSpec := rfl
      prefixPath := prefixPath
      pathRefinesWindows := pathRefinesWindows
      refinement := refinement
      refinementSpec := rfl
      next := next
      nextRobust := rfl
      nextPrefix := rfl }

namespace Extension

/-- The intermediate prefix refinement retains the exact previously exposed word. -/
theorem prefixStart_word {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) : extension.prefixStart.word = previous.word :=
  (congrArg Encoding.Prefix.Enclosure.word extension.prefixStartSpec).trans
    (previous.enclosure.refine_word extension.windowGrowth.next.box extension.windowGrowth.next.proper
      extension.windowsRefinePrefix)

/-- The intermediate prefix refinement retains the actual original parser-state cache. -/
theorem prefixStart_state {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) : extension.prefixStart.state = previous.enclosure.state :=
  (congrArg Encoding.Prefix.Enclosure.state extension.prefixStartSpec).trans
    (previous.enclosure.refine_state extension.windowGrowth.next.box extension.windowGrowth.next.proper
      extension.windowsRefinePrefix)

/-- The intermediate prefix refinement retains the actual original inverse-matrix cache. -/
theorem prefixStart_inverse {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) : extension.prefixStart.inverseMatrix = previous.enclosure.inverseMatrix :=
  (congrArg Encoding.Prefix.Enclosure.inverseMatrix extension.prefixStartSpec).trans
    (previous.enclosure.refine_inverseMatrix extension.windowGrowth.next.box extension.windowGrowth.next.proper
      extension.windowsRefinePrefix)

/-- The intermediate prefix refinement uses the same actual new robust window box. -/
theorem prefixStart_box {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) : extension.prefixStart.box = extension.windowGrowth.next.box :=
  (congrArg Encoding.Prefix.Enclosure.box extension.prefixStartSpec).trans
    (previous.enclosure.refine_box extension.windowGrowth.next.box extension.windowGrowth.next.proper
      extension.windowsRefinePrefix)

/-- The final window history retains all actual windows from the exact new placed segment and earlier history. -/
theorem windowsEq {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) : extension.next.robust.windows = extension.windowGrowth.next.windows :=
  (congrArg Robust.WindowHistory.windows extension.nextRobust).trans extension.refinement.windowsEq

/-- The complete retained window count increases by exactly the requested additional count. -/
theorem windowCount {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) :
    extension.next.robust.windows.length = previous.robust.windows.length + request.additionalWindows :=
  (congrArg List.length extension.windowsEq).trans extension.windowGrowth.countEq

/-- The exact final exposed word is the actual earlier word followed by the retained new suffix. -/
theorem wordEq {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) : extension.next.word = previous.word ++ extension.prefixPath.bits :=
  (congrArg Encoding.Prefix.Enclosure.word extension.nextPrefix).trans
    (extension.prefixPath.result_word.trans
      (congrArg (fun word => word ++ extension.prefixPath.bits) extension.prefixStart_word))

/-- The actual final exposed word extends the exact previously exposed word. -/
theorem wordPrefix {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) : previous.word.IsPrefix extension.next.word :=
  ⟨extension.prefixPath.bits, extension.wordEq.symm⟩

/-- The exact final exposed word pays the full additional-bit request. -/
theorem wordLength {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) :
    extension.next.word.length = previous.word.length + request.additionalBits :=
  (congrArg Encoding.Prefix.Enclosure.word extension.nextPrefix |>.trans extension.prefixPath.result_word |>
    congrArg List.length).trans ((List.Append.length_append _ _).trans
      (congrArg₂ Nat.add (congrArg List.length extension.prefixStart_word) extension.prefixPath.bits_length))

/-- The actual final proper box lies strictly inside the original common prefix enclosure. -/
theorem nested {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) : extension.next.box.StrictInterior previous.box := by
  change extension.next.enclosure.box.StrictInterior previous.enclosure.box
  have pathRefines : extension.prefixPath.result.box.Refines extension.windowGrowth.next.box :=
    extension.pathRefinesWindows
  have actual := Box.Refinement.StrictInterior.of_refines extension.windowGrowth.nested pathRefines
  have target : extension.next.enclosure.box = extension.prefixPath.result.box :=
    congrArg Encoding.Prefix.Enclosure.box extension.nextPrefix
  have sharedTarget : extension.prefixPath.result.box.StrictInterior previous.enclosure.box :=
    previous.boxEq.symm ▸ actual
  exact target.symm ▸ sharedTarget

/-- Every actual earlier window occurrence remains in the exact final retained window list. -/
theorem earlier_mem {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) (entry : Robust.WindowHistory.Entry threshold)
    (member : entry ∈ previous.robust.windows) : entry ∈ extension.next.robust.windows :=
  extension.windowsEq.symm ▸ extension.windowGrowth.earlier_mem entry member

/-- The later cached rational witness satisfies the exact previously exposed raw prefix. -/
theorem earlierWordRepresented {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) :
    Encoding.Parser.Semantics.Prefix.Represented previous.word extension.next.point :=
  Encoding.Parser.Semantics.Prefix.represented_of_prefix extension.wordPrefix extension.next.wordRepresented

/-- Every original complete consecutive-best certificate holds at the same later rational witness. -/
theorem earlierConsecutive {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) (entry : Robust.WindowHistory.Entry threshold)
    (member : entry ∈ previous.robust.windows) :
    Best.Consecutive.Basic.AreConsecutiveBest extension.next.point entry.2.lower entry.2.upper :=
  extension.next.consecutive entry (extension.earlier_mem entry member)

/-- Every original strict threshold violation holds at the same later rational witness. -/
theorem earlierViolation {previous : History threshold certificate} {request : Request}
    (extension : Extension previous request) (entry : Robust.WindowHistory.Entry threshold)
    (member : entry ∈ previous.robust.windows) :
    1 < threshold * Dirichlet.Window.SourceBound.dirichletWindowQuadrance
      extension.next.point entry.2.lower entry.2.upper :=
  extension.next.violation entry (extension.earlier_mem entry member)

end Extension

set_option genInjectivity false in
/-- Retain the actual construction of an initial finite window and raw-bit reserve with a proper continuation box.

The original fully robust run is constructed once. Its actual window owner
starts an empty raw-prefix enclosure, and the finite bit path computes the
initial exposed word. The exact path, window refinement and resulting
rational witness remain available for later finite extension requests.
-/
structure Initialization (threshold : Fraction.Rational)
    (certificate : Sharpness.IsSharperWindowThreshold threshold) (requestedScale windowCount bitCount : Nat) where
  /-- The actual original fully robust run and all its retained window certificates. -/ original :
    Robust.Run.FullyRobustRun threshold requestedScale windowCount
  /-- The original joint state before any raw bits are exposed. -/ base : History threshold certificate
  /-- The base retains that same original run through its window-history constructor. -/ baseSpec :
    base = ofWindowHistory (Robust.WindowHistory.ofRobustRun certificate original)
  /-- The actual finite geometric path paying the initial raw-bit reserve. -/ path :
    Geometry.CCL.Prefix.Path base.enclosure bitCount
  /-- The actual final prefix box refines the retained original robust box. -/ refines :
    path.result.box.Refines base.robust.box
  /-- The actual original window history transported to that same final prefix box. -/ refinement :
    Robust.WindowHistory.Refinement base.robust path.result.box
  /-- The transport uses the original window cache and actual final prefix box. -/ refinementSpec :
    refinement = base.robust.refine path.result.box path.result.proper refines
  /-- The initial fully exposed joint reserve and its cached rational witness. -/ next : History threshold certificate
  /-- The resulting reserve keeps the original window-refinement owner. -/ nextRobust : next.robust = refinement.next
  /-- The resulting reserve keeps the actual raw-prefix enclosure returned by the finite path. -/ nextEnclosure :
    next.enclosure = path.result

/-- Compute an initial finite reserve while retaining a proper box permitting further exact word and window extension.

Only this initial constructor invokes the original fully robust run builder.
The raw prefix is generated from the shared proper enclosure by finite
recurrence. Its actual length pays the requested initial bit count without
exposing a terminal word that would replace the box by a single input.
-/
def reserve (certificate : Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale windowCount bitCount : Nat) :
    Initialization threshold certificate requestedScale windowCount bitCount := by
  let original := Robust.Run.criticalFullyRobustRun certificate requestedScale windowCount
  let robust := Robust.WindowHistory.ofRobustRun certificate original
  let base := ofWindowHistory robust
  let path := Geometry.CCL.Prefix.Path.build base.enclosure bitCount
  have refines : path.result.box.Refines base.robust.box := base.boxEq ▸ path.refines
  let refinement := base.robust.refine path.result.box path.result.proper refines
  let enclosure := path.result
  let next : History threshold certificate :=
    { robust := refinement.next
      enclosure := enclosure
      boxEq := refinement.boxEq.symm
      witness := enclosure.realize }
  exact
    { original := original
      base := base
      baseSpec := rfl
      path := path
      refines := refines
      refinement := refinement
      refinementSpec := rfl
      next := next
      nextRobust := rfl
      nextEnclosure := rfl }

namespace Initialization

/-- The original base retains the exact initial window count before and after exposing the finite raw reserve. -/
theorem baseWindowCount {requestedScale windowCount bitCount : Nat}
    (initial : Initialization threshold certificate requestedScale windowCount bitCount) :
    initial.base.robust.windows.length = windowCount :=
  (congrArg (fun history => history.robust.windows.length) initial.baseSpec).trans
    (Robust.WindowHistory.ofRobustRun_length certificate initial.original)

/-- The original base exposes no raw bits before the retained finite continuation path starts. -/
theorem baseWord {requestedScale windowCount bitCount : Nat}
    (initial : Initialization threshold certificate requestedScale windowCount bitCount) : initial.base.word = [] :=
  congrArg History.word initial.baseSpec

/-- The actual initial reserve has exactly the requested number of original windows. -/
theorem windowCount {requestedScale requestedWindows bitCount : Nat}
    (initial : Initialization threshold certificate requestedScale requestedWindows bitCount) :
    initial.next.robust.windows.length = requestedWindows :=
  (congrArg (fun robust => robust.windows.length) initial.nextRobust).trans
    ((congrArg List.length initial.refinement.windowsEq).trans initial.baseWindowCount)

/-- The actual initial raw word has exactly the requested finite bit-reserve length. -/
theorem wordLength {requestedScale windowCount bitCount : Nat}
    (initial : Initialization threshold certificate requestedScale windowCount bitCount) :
    initial.next.word.length = bitCount := by
  have resultLength := initial.path.wordLength
  have emptyLength : initial.base.enclosure.word.length = 0 := congrArg List.length initial.baseWord
  rewrite [emptyLength, Nat.zero_add] at resultLength
  exact (congrArg (fun enclosure => enclosure.word.length) initial.nextEnclosure).trans resultLength

/-- Every original initial-window occurrence remains in the actual exposed reserve. -/
theorem original_mem {requestedScale windowCount bitCount : Nat}
    (initial : Initialization threshold certificate requestedScale windowCount bitCount)
    (entry : Robust.WindowHistory.Entry threshold) (member : entry ∈ initial.base.robust.windows) :
    entry ∈ initial.next.robust.windows :=
  (congrArg Robust.WindowHistory.windows initial.nextRobust).symm ▸ initial.refinement.earlier_mem entry member

end Initialization

end History

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL
