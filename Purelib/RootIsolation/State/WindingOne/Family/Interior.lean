module
import Purelib.Data.List.Map
public import Purelib.Polynomial.Clearance.Box.Interior
public import Purelib.Data.Rat.List.Minimum
public import Purelib.Geometry.Projective.Chordal.Box.Interior
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.State.WindingOne.Family.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

section

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# Comparing complete CCL profile children with winding-one states

The complete profile refinement is parameterized by an arbitrary finite
pairwise-separated box family.  This module instantiates that interface with
the boxes carried by explicit finite winding-one states.  Every retained
profile child is then compared with the actual numerical states, not with an
unrelated list of boxes.

An owned result records only a displayed Gaussian-rational curve sample in
one state, together with its small polynomial residual and nonzero derivative.
The sample-owner comparison remains pointwise and is never promoted to root
existence.  A separate affine-family scan preserves the stronger semantics
already computed for each profile: either displayed rational factor zeros are
inside the dispatched box, or the complete rational non-pole event cylinder
is outside it.  Neither alternative asserts that a factor zero exists.
-/

namespace Purelib.RootIsolation.State.WindingOne.Family.Basic.WindingFamily

/-- Projective complement gaps supplied by the uniform residual-interior
strip of every displayed winding state. -/
@[expose] def interiorStripChordalGaps
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient) : List Fraction.Rational :=
  family.states.map fun state =>
    Geometry.Projective.Chordal.Box.Interior.interiorStripChordalGap state.box
      state.clearance.residualInteriorRadius

/-- Every original state's residual-interior strip gives a strictly positive projective complement gap. -/
theorem interiorStripChordalGaps_positive
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient) :
    ∀ gap ∈ family.interiorStripChordalGaps, 0 < gap := by
  intro gap member
  change gap ∈ family.states.map _ at member
  rcases Data.List.Map.mem_map.mp member with ⟨state, _stateMember, rfl⟩
  exact
    Geometry.Projective.Chordal.Box.Interior.interiorStripChordalGap_pos
      state.box state.clearance.residualInteriorRadius_pos

/-- One positive rational projective gap below the uniform interior gap of
every state in the finite family. -/
@[expose] def interiorGapTarget
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient) : Fraction.Rational :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum
    family.interiorStripChordalGaps

/-- The finite family's common projective interior-gap target is strictly positive. -/
theorem interiorGapTarget_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient) : 0 < family.interiorGapTarget :=
  Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_pos _
    family.interiorStripChordalGaps_positive

/-- The common interior-gap target fits each indexed original state's retained projective gap. -/
theorem interiorGapTarget_le_stateAt
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient)
    (index : Fin family.boxes.length) :
    family.interiorGapTarget ≤
      Geometry.Projective.Chordal.Box.Interior.interiorStripChordalGap
        (family.stateAtBoxIndex index).box
        (family.stateAtBoxIndex index).clearance.residualInteriorRadius := by
  apply
    Data.Rat.List.Minimum.RegionOwnership.positiveMinimum_le_of_mem
  change _ ∈ family.states.map _
  apply Data.List.Map.mem_map.mpr
  refine ⟨family.stateAtBoxIndex index, ?_, rfl⟩
  exact List.get_mem family.states
    ⟨index.val, family.boxes_length ▸ index.isLt⟩
end Purelib.RootIsolation.State.WindingOne.Family.Basic.WindingFamily

end

end
