module

public import Purelib.Approximation.Gaussian.Name.Apart
public import Purelib.Approximation.Gaussian.Name.Coherent.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Name.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Process.Apart

public section

namespace Purelib.Approximation.Gaussian.Division.Prepared

/-! ## Apartness-certified fractional-linear output -/

set_option genInjectivity false in
/-- Exact typed preparation needed before dividing by the transformed `A`-coordinate. The prepared denominator may be a
certified based refinement of the original process; operational equivalence records that provenance without requiring
whole-process apartness at the original state. -/
structure DenominatorPreparation (denominator :
  Coherent.CoherentNamed) where
  /-- The retained coherent presentation prepared for denominator division. -/ prepared : Coherent.CoherentNamed
  /-- The whole-ball apartness certificate of that exact prepared presentation. -/ apart : Named.Apart prepared.name
  /-- The finite-request operational equivalence from the original denominator to the retained prepared presentation. -/
    equivalent : Gaussian.Equivalence.NamedEquivalent denominator.name prepared.name

constructive_injectivity Purelib.Approximation.Gaussian.Division.Prepared.DenominatorPreparation

end Purelib.Approximation.Gaussian.Division.Prepared

namespace Purelib.Approximation.Gaussian.Division.Prepared.DenominatorPreparation

/-- The former whole-process preparation is the special case obtained by apartifying the original denominator directly.
-/
@[expose] def ofPossibleApart
  (denominator : Coherent.CoherentNamed)
    (possibleApart : Possible.PossibleApart
      denominator.name.process) : Approximation.Gaussian.Division.Prepared.DenominatorPreparation denominator where
  prepared := CoherentNamed.apartify
    denominator possibleApart
  apart := { certificate := Preparation.apartifyApart possibleApart }
  equivalent :=
    CoherentNamed.apartifyEquivalent denominator
      possibleApart

end Purelib.Approximation.Gaussian.Division.Prepared.DenominatorPreparation
