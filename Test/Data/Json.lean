module

import Test.Data.Json.Basic
import Test.Data.Json.Codec
import Test.Data.Json.Parser
import Test.Data.Json.Printer

/-!
# Executable JSON regressions

The suite uses owned JSON data, codecs, parser and printer with explicit fixture
expectations. No old JSON carrier or comparator is part of its audited closure.
-/

namespace Test.Data.Json

/-- Run the owned scalar, record, equality, parser and printer regression suites.

Each suite retains its own fixture data and exact expected result. Runtime checks
raise the corresponding diagnostic without supplying native mathematical proofs. -/
public def run : IO Unit := do
  Basic.run
  Codec.run
  Parser.run
  Printer.run

end Test.Data.Json

/-- Execute the complete owned JSON runtime regression suite.

The Lake executable links the same regression modules used by the ordinary Test
build. Its exit status reports fixture success or the first retained error. -/
public def main : IO Unit := Test.Data.Json.run
