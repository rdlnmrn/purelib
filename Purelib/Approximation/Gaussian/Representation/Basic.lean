module

public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.Deriving.Repr
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Certified finite translations between refinement protocols

This module separates two operations which cannot constructively be conflated.
A direct observation map converts only the information already present in one
finite observation.  A finite realizer may first refine its source in response
to a positive rational request and records the finite work performed.

Candidate readings are Gaussian rationals.  Relations between readings remain
explicit because an affine enclosure, a projective CCL tail, and a redundant
digit cell need not use identical internal coordinates.
-/

namespace Purelib.Approximation.Gaussian

namespace Representation.Basic

/-- Boundary information which a translation is not permitted to erase. -/
inductive BoundaryConvention where
  /-- Retain closed-boundary observations. -/ | closed
  /-- Retain half-open boundary observations. -/ | halfOpen
  /-- Retain observations with redundant boundary coverage. -/ | redundant
  /-- Retain projective boundary observations. -/ | projective
deriving DecidableEq

derive_exposed_repr BoundaryConvention

end Representation.Basic

set_option genInjectivity false in
/-- The common finite-observation contract. `precisionSq` is the native squared gauge of the representation; its
interpretation is documented by each instance rather than being forced to be a Euclidean diameter. -/
structure Representation where
  /-- The retained finite-observation type of this representation. -/ Observation : Type
  /-- The Gaussian rational readings admitted by a displayed observation. -/ Possible : Observation →
    Canonical → Prop
  /-- Compute the explicit Gaussian rational witness of an observation. -/ witness : Observation →
    Canonical
  /-- The displayed witness is admitted by its original observation. -/ witness_possible : ∀ observation, Possible
    observation (witness observation)
  /-- The representation's relation of finite observation refinement. -/ Refines : Observation → Observation → Prop
  /-- Every observation refines itself. -/ refines_refl : ∀ observation, Refines observation observation
  /-- Compose two successive observation refinements. -/ refines_trans : ∀ {inner middle outer},
    Refines inner middle → Refines middle outer → Refines inner outer
  /-- A refined observation admits only readings admitted by the original observation. -/ possible_persists : ∀ {inner
    outer value},
    Refines inner outer → Possible inner value → Possible outer value
  /-- The native rational squared-precision gauge of each observation. -/ precisionSq : Observation → Fraction.Rational
  /-- Every native squared-precision gauge is nonnegative. -/ precisionSq_nonneg : ∀ observation, 0 ≤ precisionSq
    observation
  /-- The boundary convention retained by this representation. -/ boundary :
    Representation.Basic.BoundaryConvention

constructive_injectivity Representation

namespace Representation.mk

end Representation.mk

namespace Representation

/-- Two observations are finitely compatible when one displayed rational reading is admitted by both. -/
def Compatible (representation :
  Representation)
    (left right : representation.Observation) : Prop :=
  ∃ value : Canonical,
    representation.Possible left value ∧
      representation.Possible right value

/-- Every observation is compatible with itself through its displayed witness. -/
theorem compatible_refl (representation :
  Representation)
    (observation : representation.Observation) :
    representation.Compatible observation observation :=
  ⟨representation.witness observation,
    representation.witness_possible observation,
    representation.witness_possible observation⟩

/-- Reverse a finite compatibility witness. -/
theorem compatible_symm {representation :
  Representation}
    {left right : representation.Observation}
    (compatible : representation.Compatible left right) :
    representation.Compatible right left := by
  rcases compatible with ⟨value, leftPossible, rightPossible⟩
  exact ⟨value, rightPossible, leftPossible⟩

/-- A refined observation is compatible with its original observation through its own retained witness. -/
theorem compatible_of_refines {representation
  : Representation}
    {inner outer : representation.Observation}
    (refines : representation.Refines inner outer) :
    representation.Compatible inner outer :=
  ⟨representation.witness inner,
    representation.witness_possible inner,
    representation.possible_persists refines
      (representation.witness_possible inner)⟩

end Representation

end Purelib.Approximation.Gaussian

end
