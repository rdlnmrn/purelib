module

public import Purelib.Algebra.Field.ExplicitField
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field

section
/-!
# Divine Proportions, §2.2–2.3: proportions and identities

The source's elementary identities are stated directly over constructive
commutative rings.  Its three-index antisymmetrization is an explicit six-term
operation, so none of these declarations uses permutations, finite sums, or a
global enumeration.
-/

@[expose] public section

namespace Purelib.Algebra

variable {K : Type*}

set_option genInjectivity false in
/-- An ordered triple with an explicit nonzero coordinate alternative.

Only a zero operation is required; the record retains the three coordinates and a proof that at least one differs from
zero. -/
structure Proportion.Three.Basic.ThreeProportion (K : Type*) [Zero K] where
  /-- The first homogeneous coordinate. -/ first : K
  /-- The second homogeneous coordinate. -/ second : K
  /-- The third homogeneous coordinate. -/ third : K
  /-- At least one of the three coordinates is nonzero. -/ nonzero : first ≠ 0 ∨ second ≠ 0 ∨ third ≠ 0

constructive_injectivity Proportion.Three.Basic.ThreeProportion

namespace Proportion.Three.Basic.ThreeProportion

variable [CommRing K]

open Purelib.Algebra.Proportion.Three.Basic
/-- The first two coordinate cross products of two triples agree. -/
def FirstCondition (left right : ThreeProportion K) : Prop
  :=
  left.first * right.second = right.first * left.second

/-- The second and third coordinate cross products of two triples agree. -/
def SecondCondition (left right : ThreeProportion K) :
  Prop :=
  left.second * right.third = right.second * left.third

/-- The third and first coordinate cross products of two triples agree. -/
def ThirdCondition (left right : ThreeProportion K) : Prop
  :=
  left.third * right.first = right.third * left.first

/-- Test equality of displayed three-proportions by three cross products.

All three coordinate-pair equalities are retained, without quotienting the triples or selecting a normalization. -/
def Equivalent (left right : ThreeProportion K) : Prop :=
  FirstCondition left right ∧ SecondCondition left right ∧
    ThirdCondition left right

end Proportion.Three.Basic.ThreeProportion

end Purelib.Algebra

end

end

section
@[expose] public section

/-!
# Divine Proportions, §15.1: conics and their centers

A conic is kept as its six displayed coefficients.  Its quadratic part is
required to be nonzero, exactly as in the source.  Center calculations use only
the two finite linear equations obtained by expanding rotation invariance.
-/

namespace Purelib.Curves.Plane

variable {K : Type*} [ExplicitField K]
namespace Conic

/-- Test proportionality of two displayed ordered triples by cross products.

The three pairwise coordinate equations are conjoined without division or a nonzero-coordinate assumption. -/
def OrderedTriplesEquivalent
    (left₁ left₂ left₃ right₁ right₂ right₃ : K) : Prop :=
  left₁ * right₂ = right₁ * left₂ ∧
    left₁ * right₃ = right₁ * left₃ ∧
    left₂ * right₃ = right₂ * left₃
end Conic

end Purelib.Curves.Plane

end
