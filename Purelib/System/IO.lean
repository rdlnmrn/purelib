module

-- Public signatures retain the original IO, file-path, handle and stream owners.
public import Init.System.IO
-- Inline newline writers retain the native String append owner publicly.
public import Purelib.Data.String.Basic

/-!
# UTF8 filesystem, stream and process operations

The original binary reading procedures retain their handles, buffers, metadata
and byte arrays. Successful text conversion uses an exact retained UTF8 witness;
read errors and invalid-text diagnostics retain the original IO contracts.
Newline writers retain their handles and streams, and process output retains
the original spawn arguments and captured-output fields.
-/

namespace Purelib.System.IO

universe u

open Purelib.Data.String (append decapitalize fromUTF8?)

/-- Read the complete original file bytes as exactly certified UTF8 text.

The original binary file reader retains metadata, buffers and handle behavior.
A failed UTF8 conversion throws the original path-bearing user-error diagnostic. -/
public def FS.readFile (path : _root_.System.FilePath) : IO String := do
  let bytes ← _root_.IO.FS.readBinFile path
  match fromUTF8? bytes with
  | some text => return text
  | none =>
      throw (.userError (append (append "Tried to read file '" path.toString)
        "' containing non UTF-8 data."))

/-- Read an original file handle's remaining bytes as exactly certified UTF8 text.

The original binary handle reader retains its buffers and does not close the
handle. A failed conversion preserves the original handle-specific diagnostic. -/
public def FS.Handle.readToEnd (handle : _root_.IO.FS.Handle) : IO String := do
  let bytes ← handle.readBinToEnd
  match fromUTF8? bytes with
  | some text => return text
  | none => throw (.userError "Tried to read from handle containing non UTF-8 data.")

/-- Read an original stream's remaining bytes as exactly certified UTF8 text.

The original binary stream reader retains its buffers and does not close the
stream. A failed conversion preserves the original stream-specific diagnostic. -/
public def FS.Stream.readToEnd (stream : _root_.IO.FS.Stream) : IO String := do
  let bytes ← stream.readBinToEnd
  match fromUTF8? bytes with
  | some text => return text
  | none => throw (.userError "Tried to read from stream containing non UTF-8 data.")

/-- Write original UTF8 text and one trailing newline to its retained file handle.

The same original handle receives the complete text followed by the original
single line-feed byte. Its write ordering and filesystem exceptions are those
of the original putStr operation. -/
public def FS.Handle.putStrLn (handle : _root_.IO.FS.Handle) (text : String) : IO Unit :=
  handle.putStr (append text "\n")

/-- Write original UTF8 text and one trailing newline to its retained stream.

The same original stream receives the complete text followed by the original
single line-feed byte. Its write operation and exceptions are retained without
replacing the stream or selecting another output destination. -/
public def FS.Stream.putStrLn (stream : _root_.IO.FS.Stream) (text : String) : IO Unit :=
  stream.putStr (append text "\n")

/-- Render a supplied value and write one trailing newline to the original standard output.

The original ToString instance renders the value exactly once. The same current
standard-output stream receives that text and a single line feed through its
original putStr operation, preserving redirected streams and write failures. -/
public def println {Alpha : Type u} [ToString Alpha] (value : Alpha) : IO Unit :=
  _root_.IO.print (append (ToString.toString value) "\n")

/-- Render a file-bearing original IO error with its retained code and details.

Only the first ASCII letter of the gist and optional details is lowercased.
The original decimal code, punctuation, newline and filename remain in their
original order without changing the original error record. -/
private def Error.fopenErrorToString (gist filename : String) (code : UInt32) :
    Option String → String
  | some details =>
      append (append (append (append (append (append (decapitalize gist)
        " (error code: ") (Nat.repr code.toNat)) ", ") (decapitalize details))
        ")\n  file: ") filename
  | none =>
      append (append (append (append (decapitalize gist) " (error code: ")
        (Nat.repr code.toNat)) ")\n  file: ") filename

/-- Render an original IO error without a filename from its code and details.

The first ASCII letter of the gist and optional details is lowercased. The
original decimal code and punctuation remain unchanged, and absent details
produce exactly the shorter original diagnostic. -/
private def Error.otherErrorToString (gist : String) (code : UInt32) :
    Option String → String
  | some details =>
      append (append (append (append (append (decapitalize gist) " (error code: ")
        (Nat.repr code.toNat)) ", ") (decapitalize details)) ")"
  | none =>
      append (append (append (decapitalize gist) " (error code: ")
        (Nat.repr code.toNat)) ")"

/-- Render an original IO error with its original diagnostic grammar.

Every constructor retains its original gist, filename, decimal code, optional
details and punctuation. User errors retain their supplied message verbatim;
formatting does not replace the original structured error carrier. -/
public def Error.toString : _root_.IO.Error → String
  | .unexpectedEof => "end of file"
  | .inappropriateType (some filename) code details =>
      Error.fopenErrorToString "inappropriate type" filename code (some details)
  | .inappropriateType none code details =>
      Error.otherErrorToString "inappropriate type" code (some details)
  | .interrupted filename code details =>
      Error.fopenErrorToString "interrupted system call" filename code (some details)
  | .invalidArgument (some filename) code details =>
      Error.fopenErrorToString "invalid argument" filename code (some details)
  | .invalidArgument none code details =>
      Error.otherErrorToString "invalid argument" code (some details)
  | .noFileOrDirectory filename code _ =>
      Error.fopenErrorToString "no such file or directory" filename code none
  | .noSuchThing (some filename) code details =>
      Error.fopenErrorToString "no such thing" filename code (some details)
  | .noSuchThing none code details =>
      Error.otherErrorToString "no such thing" code (some details)
  | .permissionDenied (some filename) code details =>
      Error.fopenErrorToString details filename code none
  | .permissionDenied none code details =>
      Error.otherErrorToString details code none
  | .resourceExhausted (some filename) code details =>
      Error.fopenErrorToString "resource exhausted" filename code (some details)
  | .resourceExhausted none code details =>
      Error.otherErrorToString "resource exhausted" code (some details)
  | .alreadyExists none code details =>
      Error.otherErrorToString "already exists" code (some details)
  | .alreadyExists (some filename) code details =>
      Error.fopenErrorToString "already exists" filename code (some details)
  | .otherError code details => Error.otherErrorToString details code none
  | .resourceBusy code details => Error.otherErrorToString "resource busy" code (some details)
  | .resourceVanished code details =>
      Error.otherErrorToString "resource vanished" code (some details)
  | .hardwareFault code _ => Error.otherErrorToString "hardware fault" code none
  | .illegalOperation code details =>
      Error.otherErrorToString "illegal operation" code (some details)
  | .protocolError code details => Error.otherErrorToString "protocol error" code (some details)
  | .timeExpired code details => Error.otherErrorToString "time expired" code (some details)
  | .unsatisfiedConstraints code _ => Error.otherErrorToString "directory not empty" code none
  | .unsupportedOperation code details =>
      Error.otherErrorToString "unsupported operation" code (some details)
  | .userError message => message

set_option backward.match.sparseCases false in
/-- Run the original process request and capture its complete UTF8 output.

The original spawn configuration, optional input writes, dedicated stdout task,
stderr read and wait order are retained. Only the two original binary-to-text
reads use the same exactly certified UTF8 conversion and original diagnostics. -/
public def Process.output (args : _root_.IO.Process.SpawnArgs)
    (input? : Option String := none) : IO _root_.IO.Process.Output := do
  let child ←
    if let some input := input? then
      let (stdin, child) ← (← _root_.IO.Process.spawn
        { args with stdout := .piped, stderr := .piped, stdin := .piped }).takeStdin
      stdin.putStr input
      stdin.flush
      pure child
    else
      _root_.IO.Process.spawn
        { args with stdout := .piped, stderr := .piped, stdin := .null }
  let stdout ← _root_.IO.asTask (FS.Handle.readToEnd child.stdout) Task.Priority.dedicated
  let stderr ← FS.Handle.readToEnd child.stderr
  let exitCode ← child.wait
  let stdout ←
    letI : ToString _root_.IO.Error := ⟨Error.toString⟩
    _root_.IO.ofExcept stdout.get
  pure { exitCode := exitCode, stdout := stdout, stderr := stderr }

end Purelib.System.IO
