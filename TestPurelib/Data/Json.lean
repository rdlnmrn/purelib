module

import TestPurelib.Data.Json.Basic
import TestPurelib.Data.Json.Codec
import TestPurelib.Data.Json.Parser
import TestPurelib.Data.Json.Printer
import TestPurelib.Data.ByteArray.UTF8
import Init.System.FilePath

/-!
# Executable JSON regressions

The suite uses owned JSON data, codecs, parser and printer with explicit fixture
expectations. No old JSON carrier or comparator is part of its audited closure.
-/

namespace TestPurelib.Data.Json

/-- Run the owned scalar, record, equality, parser and printer regression suites.

Each suite retains its own fixture data and exact expected result. Runtime checks
raise the corresponding diagnostic without supplying native mathematical proofs. -/
public def run : IO Unit := do
  TestPurelib.Data.ByteArray.UTF8.check
  Basic.run
  Codec.run
  Parser.run
  Printer.run

end TestPurelib.Data.Json

/-- Execute the owned UTF8/JSON regressions or profile retained original file bytes.

The Lake executable links the same regression modules used by the ordinary TestPurelib
build. Its exit status reports fixture success or the first retained error. -/
public def main (arguments : List String) : IO Unit := do
  match arguments with
  | [] => TestPurelib.Data.Json.run
  | ["--byte-array-profile", path] => TestPurelib.Data.ByteArray.UTF8.profile (System.FilePath.mk path)
  | ["--parse-profile", path] => TestPurelib.Data.Json.Parser.profile (System.FilePath.mk path)
  | _ => throw (IO.userError "usage: json_regression [--byte-array-profile FILE | --parse-profile FILE]")
