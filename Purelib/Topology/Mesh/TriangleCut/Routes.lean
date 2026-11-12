module

public import Purelib.Topology.Mesh.TriangleCut
public import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

/-! # Oriented boundary replacement of the retained cut chord

The chord joins the two actual cut slots of the original three-child
triangle patch. Its route goes through the same original apex. The first
child face supplies the signed correction, with every original slot and
both reversed perimeter occurrences retained.
-/

public section

namespace Purelib.Topology.Mesh.TriangleCut

open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing

/-- Replace the actual first-to-second cut chord by the two reversed perimeter sides through the original apex.

The existing EdgeRoute retains exact indexed endpoints, boundary support
and the positive first-child face correction. Its identity applies to
every antisymmetric reading; no face integral is assumed to vanish.
-/
def chordRoute : SewingRetraction.EdgeRoute faces boundary (⟨1, 4⟩ : OrientedEdge 5) where
  path := [⟨1, 0⟩, ⟨0, 4⟩]
  endpoints := .cons (.cons (.nil _))
  supported := by
    intro edge member
    rcases Membership.mem_cons.mp member with same | member
    · cases same
      refine Or.inr ?_
      rewrite [perimeter_eq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · rcases Membership.mem_cons.mp member with same | absent
      · cases same
        refine Or.inr ?_
        rewrite [perimeter_eq]
        exact List.mem_cons_self
      · exact (List.not_mem_nil absent).elim
  correction := [(1, 0)]
  value_eq := by
    intro value anti
    have first := anti (⟨0, 1⟩ : OrientedEdge 5)
    have last := anti (⟨4, 0⟩ : OrientedEdge 5)
    change value (⟨1, 0⟩ : OrientedEdge 5) = _ at first
    change value (⟨0, 4⟩ : OrientedEdge 5) = _ at last
    change value (⟨1, 4⟩ : OrientedEdge 5) =
      (value ⟨1, 0⟩ + (value ⟨0, 4⟩ + 0)) +
        (((1 : Int) : Canonical) * SewingRetraction.wordValue value (faces 0).boundary + 0)
    rewrite [faces_zero]
    change value (⟨1, 4⟩ : OrientedEdge 5) =
      (value ⟨1, 0⟩ + (value ⟨0, 4⟩ + 0)) +
        (((1 : Int) : Canonical) * (value ⟨0, 1⟩ + (value ⟨1, 4⟩ + (value ⟨4, 0⟩ + 0))) + 0)
    have unit : ((1 : Int) : Canonical) = 1 := by decide
    rewrite [unit, one_mul, first, last]
    ring1

/-- The complete route retains the two reversed original perimeter occurrences in order. -/
private theorem packaged_chordRoute_path : chordRoute.path = [⟨1, 0⟩, ⟨0, 4⟩] := rfl

/-- The complete route retains the two reversed original perimeter occurrences in order. -/
theorem chordRoute_path : chordRoute.path = [⟨1, 0⟩, ⟨0, 4⟩] := packaged_chordRoute_path

/-- The signed correction is precisely one positive occurrence of the original first child face. -/
private theorem packaged_chordRoute_correction : chordRoute.correction = [(1, 0)] := rfl

/-- The signed correction is precisely one positive occurrence of the original first child face. -/
theorem chordRoute_correction : chordRoute.correction = [(1, 0)] := packaged_chordRoute_correction

end Purelib.Topology.Mesh.TriangleCut

end
