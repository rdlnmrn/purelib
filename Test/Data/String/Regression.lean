module

import Purelib.Data.String.Basic

/-!
# Retained string concatenation

Literal results specify the original bytes independently of the append
certificate. The checks cover empty inputs, ASCII, controls and multibyte
UTF8, including selection of the owned scoped instance.
-/

namespace Test.Data.String

open Purelib.Data.String (append)

/-- An empty left input retains the original right string.

The complete string record reduces to the displayed literal, including its
original byte-array data. -/
private theorem empty_left : append "" "checkpoint" = "checkpoint" := rfl

/-- An empty right input retains the original left string.

The complete string record reduces to the displayed literal without adding
any bytes. -/
private theorem empty_right : append "checkpoint" "" = "checkpoint" := rfl

/-- Concatenation preserves the original ASCII path bytes in order.

The two input literals supply the path prefix and retained checkpoint name;
the result keeps their exact consecutive byte sequence. -/
private theorem ascii_bytes :
    append "attempt/" "manifest.json" = "attempt/manifest.json" := rfl

/-- Control bytes remain literal string data during concatenation.

Tabs, line endings, quotes and backslashes retain their exact byte sequence
before any separate JSON escaping operation. -/
private theorem controls : append "\t\n" "\r\"\\" = "\t\n\r\"\\" := rfl

/-- Non-ASCII scalars retain their original multibyte encodings.

The displayed Latin, Greek and supplementary-plane characters concatenate
as their original consecutive UTF8 byte sequences. -/
private theorem unicode_bytes : append "éδ" "🙂" = "éδ🙂" := rfl

open scoped Purelib.Data.String in
/-- The scoped append instance retains the same multibyte string data.

Instance selection uses the owned concatenation operation, and its complete
result reduces to the independently specified literal. -/
private theorem scoped_append : "éδ" ++ "🙂" = "éδ🙂" := rfl

end Test.Data.String
