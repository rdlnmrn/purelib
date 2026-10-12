module
public import Purelib.Topology.Knot.Braid.Word.Basic

open Purelib.Topology.Knot

@[expose] public section

namespace Purelib.Topology.Knot.Braid.ThreeStrand

/-- Finite signed adjacent-generator words on exactly three strands. -/
abbrev Word := Braid.Word 3

end Purelib.Topology.Knot.Braid.ThreeStrand
