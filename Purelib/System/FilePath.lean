module

-- The public operations retain the original nominal file-path and string carriers.
public import Init.System.FilePath
import Init.System.Platform
import Init.Data.String.Bootstrap
import Purelib.Data.String.Basic

/-!
# Lexical operations on original file paths

The original platform separator, absolute-path rule and unnormalized input bytes
determine path concatenation and parent extraction. Original String bootstrap
cursors preserve UTF8 scalar boundaries without constructing slice certificates
or introducing a different file-path carrier.
-/

namespace Purelib.System.FilePath

set_option backward.match.sparseCases false

open Purelib.Data.String (append)
open _root_.System (FilePath)

/-- Identify an original platform path separator at its displayed scalar.

Windows accepts either slash, while every other platform accepts only the
forward slash. No normalization or filesystem equivalence changes the input. -/
private def isSeparator (character : Char) : Bool :=
  if _root_.System.Platform.isWindows then character == '\\' || character == '/'
  else character == '/'

/-- Test the original first scalar for a platform path separator.

An empty original string has no separator. Nonempty strings are read at their
original zero byte cursor through the same UTF8 bootstrap primitive. -/
private def startsAtRoot (text : String) : Bool :=
  if String.Internal.atEnd text ⟨0⟩ then false
  else isSeparator (String.Internal.get text ⟨0⟩)

/-- Test the original second scalar for the colon of an absolute Windows drive path.

The two original cursor boundaries are retained. Missing first or second scalars
produce false exactly as the original optional iterator lookup does. -/
private def hasDriveColon (text : String) : Bool :=
  if String.Internal.atEnd text ⟨0⟩ then false
  else
    let second := String.Internal.next text ⟨0⟩
    if String.Internal.atEnd text second then false
    else String.Internal.get text second == ':'

/-- Apply the original platform absolute-path rule to the retained path string.

A leading platform separator is absolute. On Windows the original second scalar
colon also suffices, without checking or replacing the first scalar. -/
private def isAbsolute (path : FilePath) : Bool :=
  startsAtRoot path.toString ||
    (_root_.System.Platform.isWindows && hasDriveColon path.toString)

/-- Advance an original scalar cursor up to its original end position.

The requested count follows the same nextn behavior: exhausted text retains its
end position, while each remaining scalar consumes exactly one original step. -/
private def advance (text : String) : Nat → String.Pos.Raw → String.Pos.Raw
  | 0, position => position
  | count + 1, position =>
      if String.Internal.atEnd text position then position
      else advance text count (String.Internal.next text position)

/-- Retain the last original separator cursor and its next scalar boundary.

The forward scan visits the same original scalar positions as a reverse search.
The input byte size bounds its scalar steps, and every separator updates the
retained pair without changing the input's UTF8 bytes or redundant separators. -/
private def lastSeparator (text : String) :
    Nat → String.Pos.Raw → Option (String.Pos.Raw × String.Pos.Raw) →
      Option (String.Pos.Raw × String.Pos.Raw)
  | 0, _, retained => retained
  | fuel + 1, position, retained =>
      if String.Internal.atEnd text position then retained
      else
        let next := String.Internal.next text position
        let selected := if isSeparator (String.Internal.get text position) then
          some (position, next) else retained
        lastSeparator text fuel next selected

/-- Join original paths with the original platform separator and absolute-path rule.

An absolute right operand retains that same original path. Otherwise the two
original string byte arrays surround exactly one platform separator; empty paths
and redundant separators are preserved without normalization. -/
public def join (path subpath : FilePath) : FilePath :=
  if isAbsolute subpath then subpath
  else
    let separator := if _root_.System.Platform.isWindows then "\\" else "/"
    ⟨append (append path.toString separator) subpath.toString⟩

/-- Read the lexical parent of an original unnormalized file path.

Root paths retain the original none result, and direct root children retain the
original root substring. Other paths retain exactly the original prefix before
the last separator, including Unicode scalars and redundant separators. -/
public def parent (path : FilePath) : Option FilePath :=
  let text := path.toString
  let separator := lastSeparator text (text.utf8ByteSize + 1) ⟨0⟩ none
  let retainedPrefix := separator.map fun retained =>
    FilePath.mk (String.Internal.extract text ⟨0⟩ retained.1)
  if isAbsolute path then
    let afterRoot := advance text (if startsAtRoot text then 1 else 3) ⟨0⟩
    if String.Internal.atEnd text afterRoot then none
    else
      match separator with
      | some (_, next) =>
          if next.byteIdx == afterRoot.byteIdx then
            some ⟨String.Internal.extract text ⟨0⟩ afterRoot⟩
          else retainedPrefix
      | none => retainedPrefix
  else retainedPrefix

/-- Select lexical division on the same original file-path carrier.

Opening this scope retains the original path inputs and join grammar. It changes
only the selected concatenation and cursor certificates, with no global instance. -/
public scoped instance (priority := 1001) : Div FilePath := ⟨join⟩

/-- Select original file-path joining with a retained string right operand.

The original string is wrapped once in the original FilePath constructor before
joining. Opening the scope preserves the same concrete input and result carriers. -/
public scoped instance (priority := 1001) :
    HDiv FilePath String FilePath :=
  ⟨fun path subpath => join path ⟨subpath⟩⟩

end Purelib.System.FilePath
