module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.Fin.Bijection.Basic
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.RootIsolation.Owner.Bridge.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Owner.Local.Basic

open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)

open Purelib

open Purelib.Geometry.Rational

open Purelib.RootIsolation

section
public section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

namespace Purelib.RootIsolation.Progressive.Chamber.Overlap

set_option genInjectivity false in
/-- A complete finite overlap between two certified chamber frames.  Every
source owner is represented on a common rational bridge box and matched to
one target owner; the stored inverse proves that no owner is lost or
duplicated.  The bridge itself carries winding four for both endpoint
polynomials and an explicit finite Rouché connection. -/
structure ChamberOverlap (left right :
  ChamberFrame) where
  /-- The actual retained bijection between the two original chamber index sets. -/ matching :
    Data.Fin.Bijection left.degree right.degree
  /-- A retained common owner box for each original left owner and its matched right owner. -/ bridge : left.Index →
    Owner.Bridge.Basic.OwnerBridge left.polynomial right.polynomial
  /-- Each common bridge refines its original left owner box. -/ bridge_refines_left : ∀ index : left.Index,
    (bridge index).box.Refines (left.owner index).box
  /-- Each common bridge refines its matched original right owner box. -/ bridge_refines_right : ∀ index : left.Index,
    (bridge index).box.Refines
      (right.owner (matching.forward index)).box

constructive_injectivity ChamberOverlap

namespace ChamberOverlap

/-- Retain the identity owner matching and original owner boxes as a chamber overlap with itself. -/
@[expose] def identity (frame :
  ChamberFrame) : Progressive.Chamber.Overlap.ChamberOverlap frame frame where
  matching := Data.Fin.Bijection.identity frame.degree
  bridge := fun index => Owner.Bridge.Basic.OwnerBridge.reflexive (frame.owner index)
  bridge_refines_left := fun index =>
    Box.refines_refl (frame.owner index).box
  bridge_refines_right := fun index =>
    Box.refines_refl (frame.owner index).box

/-- Reverse the retained matching and common-owner bridges of a chamber overlap.

The same bridge boxes refine the original opposite inputs, indexed through the inverse bijection. -/
@[expose] def reverse {left right :
  ChamberFrame}
    (overlap : Progressive.Chamber.Overlap.ChamberOverlap left right) : Progressive.Chamber.Overlap.ChamberOverlap right
      left where
  matching := overlap.matching.reverse
  bridge := fun index =>
    (overlap.bridge (overlap.matching.backward index)).reverse
  bridge_refines_left := by
    intro index
    have refines :=
      overlap.bridge_refines_right (overlap.matching.backward index)
    rw [overlap.matching.forward_backward] at refines
    exact refines
  bridge_refines_right := by
    intro index
    exact overlap.bridge_refines_left (overlap.matching.backward index)

/-- On a self-overlap the geometric owner matching is forced to be the
identity.  A bridge box cannot refine two distinct separated owners because
its displayed anchor belongs to both. -/
theorem forward_eq_self {frame :
  ChamberFrame}
    (overlap : Progressive.Chamber.Overlap.ChamberOverlap frame frame) (index : frame.Index) :
    overlap.matching.forward index = index := by
  by_cases same : overlap.matching.forward index = index
  · exact same
  · have separated := frame.pairwiseSeparated index
      (overlap.matching.forward index) (fun reverse => same reverse.symm)
    have distinct := separated.points_ne
      ((overlap.bridge_refines_left index).contains
        (overlap.bridge index).box.contains_anchor)
      ((overlap.bridge_refines_right index).contains
        (overlap.bridge index).box.contains_anchor)
    exact (distinct rfl).elim

/-- A chamber self-overlap matches every owner to itself.

The common retained bridge cannot lie in two distinct positively separated original owner boxes. -/
theorem self_matching_identity {frame :
  ChamberFrame}
    (overlap : Progressive.Chamber.Overlap.ChamberOverlap frame frame) :
    Data.Fin.Bijection.Same overlap.matching
      (Data.Fin.Bijection.identity frame.degree) :=
  overlap.forward_eq_self

end ChamberOverlap

end Purelib.RootIsolation.Progressive.Chamber.Overlap

end
