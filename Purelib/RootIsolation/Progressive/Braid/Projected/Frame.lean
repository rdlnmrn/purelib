module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Topology.Knot.Braid.Basic
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.Data.Fin.Bijection.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.RootIsolation

section
public section

/-!
# Certified projected crossings of finite root paths

An Artin generator acts on the left-to-right positions of a chosen planar
projection, whereas finite monodromy transports the persistent owner indices
of root boxes.  Those numberings need not coincide.  This file records their
finite relabelling explicitly and folds atomic projected chamber overlaps into
an executable braid word.

A crossing chart contains only rational root boxes, a signed adjacent
generator, an exact owner-matching law, and a strict height separation of the
two crossing strands.  It is therefore finite certificate data: no completed
root track or configuration space is introduced.  The extraction theorem
proves that evaluating the resulting word gives exactly the chamber-path
transport, expressed in the endpoint projection orders.
-/

namespace Purelib.RootIsolation.Progressive.Braid.Projected.Frame

/-! ## Projection-ordered chamber frames -/

set_option genInjectivity false in
/-- A chamber frame equipped with a rationally certified left-to-right root
order.  `orderToOwner` deliberately remains separate from the chamber's
internal owner numbering.  The sampled local owners may be strict refinements
of the chamber owners and hence can resolve a projection even when the
original owner boxes are too coarse to do so. -/
structure ProjectedFrame (strands : Nat) where
  /-- The original chamber frame whose owners are projected. -/ chamber : Progressive.Chamber.Frame.ChamberFrame
  /-- The retained chamber degree equals the projected family size. -/ degree_eq : chamber.degree = strands
  /-- The retained bijection from projected positions to original chamber-owner indices. -/ orderToOwner :
    Data.Fin.Bijection strands chamber.degree
  /-- The actual sample owner retained at each projected position. -/ sampleOwner : Fin strands →
    Owner.Local.Basic.LocalOwner chamber.polynomial
  /-- Each sample box refines its matched original chamber-owner box. -/ sample_refines_owner : ∀ position : Fin
    strands,
    (sampleOwner position).box.Refines
      (chamber.owner (orderToOwner.forward position)).box
  /-- The sample-owner boxes are strictly ordered by their horizontal coordinates. -/ xOrdered : ∀ left right : Fin
    strands, left.val < right.val →
    (sampleOwner left).box.xUpper < (sampleOwner right).box.xLower

constructive_injectivity ProjectedFrame

namespace ProjectedFrame

/-- Map an index in projected order to its actual original chamber-owner index. -/
@[expose] def ownerIndex {strands : Nat}
  (frame : Progressive.Braid.Projected.Frame.ProjectedFrame strands)
    (position : Fin strands) : frame.chamber.Index :=
  frame.orderToOwner.forward position

/-- Distinct projected positions identify distinct original chamber owners. -/
theorem ownerIndex_injective {strands :
  Nat}
    (frame : Progressive.Braid.Projected.Frame.ProjectedFrame strands) : Function.Injective frame.ownerIndex :=
  frame.orderToOwner.forward_injective

/-- Adjacent projected positions have a strict horizontal gap between their retained sample boxes. -/
theorem adjacent_x_gap {strands : Nat}
  (frame : Progressive.Braid.Projected.Frame.ProjectedFrame strands)
    (generator : Topology.Knot.Braid.Generator strands) :
    (frame.sampleOwner generator.left).box.xUpper <
      (frame.sampleOwner generator.right).box.xLower := by
  apply frame.xOrdered
  change generator.index.val < generator.index.val + 1
  omega

end ProjectedFrame

end Purelib.RootIsolation.Progressive.Braid.Projected.Frame

end
