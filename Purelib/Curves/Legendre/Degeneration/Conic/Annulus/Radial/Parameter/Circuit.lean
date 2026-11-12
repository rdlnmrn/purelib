module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Endpoint
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Agreement

/-!
# Normalized parameter endpoint seams of an original radial circuit

Every original circuit leg retains its existing zero and one Readings. One
Anchor and admitted Step are constructed on each identical Reading, and all
eight endpoint chains are cached once. The original ordered quarter-direction
joins identify both normalized spatial coordinates at each seam. Existing
paid same-square comparison derives agreement of the actual target root names.

The original full-source circuit seams separately derive cofactor agreement
by cancelling the same original apart Seed. Both comparisons derive agreement
of the full target endpoint products. Within-quarter prepared paths, full
transported-quarter closure, Covered finish agreement and geometric integral
transport remain separate evidence on the same original circuit.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Circuit

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)

variable {site : Fin 2} {parameter increment : Canonical} {quarter : UnitCircuitQuarter}
variable {admitted : IncrementBound site parameter increment}

/-- Retain the two exact normalized endpoint factories on one original circuit leg's existing Readings.

Both complete original source and target Readings are inputs to their own
Endpoint.ofReading construction. The two independent Anchor/Step chains keep
their original owners and factory equations; no original quarter is queried.
-/
@[expose] def Leg (original : Transport.Leg site parameter quarter) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) :=
  { source : Endpoint original.actual 0 (by decide +kernel) original.regular increment admitted //
      source = Endpoint.ofReading original.source original.regular increment admitted } ×
    { target : Endpoint original.actual 1 (by decide +kernel) original.regular increment admitted //
      target = Endpoint.ofReading original.target original.regular increment admitted }

namespace Leg

variable {original : Transport.Leg site parameter quarter}

/-- Construct the two normalized endpoint chains once on the original leg's already retained Readings. -/
def build (original : Transport.Leg site parameter quarter) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) : Leg original increment admitted :=
  let source := Endpoint.ofReading original.source original.regular increment admitted
  let target := Endpoint.ofReading original.target original.regular increment admitted
  ⟨⟨source, rfl⟩, ⟨target, rfl⟩⟩

/-- Read the actual cached normalized source endpoint at the original leg's zero chart time. -/
@[expose] def source (leg : Leg original increment admitted) :
    Endpoint original.actual 0 (by decide +kernel) original.regular increment admitted := leg.1.val

/-- Read the separate actual normalized target endpoint at the same original leg's one chart time. -/
@[expose] def target (leg : Leg original increment admitted) :
    Endpoint original.actual 1 (by decide +kernel) original.regular increment admitted := leg.2.val

/-- The cached normalized source is the exact original endpoint factory on the leg's retained source Reading. -/
theorem source_eq (leg : Leg original increment admitted) :
    leg.source = Endpoint.ofReading original.source original.regular increment admitted := leg.1.property

/-- The cached normalized target is the exact endpoint factory on the original retained target Reading. -/
theorem target_eq (leg : Leg original increment admitted) :
    leg.target = Endpoint.ofReading original.target original.regular increment admitted := leg.2.property

/-- The normalized source chain keeps the complete existing original circuit source Reading. -/
theorem source_reading (leg : Leg original increment admitted) : leg.source.reading = original.source := by
  rewrite [leg.source_eq]
  exact Endpoint.ofReading_reading _ _ _ _

/-- The normalized target chain keeps the complete existing original circuit target Reading. -/
theorem target_reading (leg : Leg original increment admitted) : leg.target.reading = original.target := by
  rewrite [leg.target_eq]
  exact Endpoint.ofReading_reading _ _ _ _

/-- An exact original quarter-direction join preserves the two normalized endpoint root channels.

The two actual Anchor and Step owners stay independent. Exact original base
and ordinate identities derive the paid same-square comparison; original
cubic product seam certificates are not substituted for normalized evidence.
-/
def seam {firstQuarter lastQuarter : UnitCircuitQuarter}
    {firstOriginal : Transport.Leg site parameter firstQuarter}
    {lastOriginal : Transport.Leg site parameter lastQuarter}
    (first : Leg firstOriginal increment admitted) (last : Leg lastOriginal increment admitted)
    (directions : Waist.direction firstQuarter 1 = Waist.direction lastQuarter 0) :
    NamedEquivalent first.target.step.root.value.name last.source.step.root.value.name :=
  Step.root_agrees_of_source_eq first.target.anchor last.source.anchor first.target.step last.source.step
    (congrArg (fun direction => (sourcePoint site parameter direction).base) directions)
    (congrArg (fun direction => (sourcePoint site parameter direction).ordinate) directions)

/-- The original full-source seam and exact normalized ordinate identify the two retained cofactor channels.

The original Circuit.Seam is transported only through the complete endpoint
Reading readbacks. Cancelling the same original apart Seed factor derives
the cofactor comparison while both original source lift owners are retained.
-/
def unit_seam {firstQuarter lastQuarter : UnitCircuitQuarter}
    {firstOriginal : Transport.Leg site parameter firstQuarter}
    {lastOriginal : Transport.Leg site parameter lastQuarter}
    (first : Leg firstOriginal increment admitted) (last : Leg lastOriginal increment admitted)
    (originalSeam : Transport.Seam firstOriginal lastOriginal)
    (directions : Waist.direction firstQuarter 1 = Waist.direction lastQuarter 0) :
    NamedEquivalent first.target.reading.lift.unitRoot.value.name last.source.reading.lift.unitRoot.value.name := by
  have firstName := congrArg
    (fun reading : Transport.Reading firstOriginal.actual 1 (by decide +kernel) => reading.lift.value.name)
    first.target_reading
  have lastName := congrArg
    (fun reading : Transport.Reading lastOriginal.actual 0 (by decide +kernel) => reading.lift.value.name)
    last.source_reading
  have sources : NamedEquivalent first.target.reading.lift.value.name last.source.reading.lift.value.name := by
    unfold Transport.Seam at originalSeam
    exact NamedEquivalent.transport firstName.symm lastName.symm originalSeam
  exact Anchor.unit_agrees_of_source_eq first.target.anchor last.source.anchor sources
    (congrArg (fun direction => (sourcePoint site parameter direction).ordinate) directions)

/-- The original source seam derives agreement of the two actual full target cubic endpoint channels.

Exact original base/ordinate identities pay normalized-root agreement. The
original full-source comparison independently pays the retained cofactor
agreement. Their original product operation combines these two certificates;
no within-quarter path or Covered finish correspondence is asserted.
-/
def value_seam {firstQuarter lastQuarter : UnitCircuitQuarter}
    {firstOriginal : Transport.Leg site parameter firstQuarter}
    {lastOriginal : Transport.Leg site parameter lastQuarter}
    (first : Leg firstOriginal increment admitted) (last : Leg lastOriginal increment admitted)
    (originalSeam : Transport.Seam firstOriginal lastOriginal)
    (directions : Waist.direction firstQuarter 1 = Waist.direction lastQuarter 0) :
    NamedEquivalent first.target.step.value.name last.source.step.value.name :=
  Step.value_agrees_of_source_eq first.target.anchor last.source.anchor first.target.step last.source.step
    (congrArg (fun direction => (sourcePoint site parameter direction).base) directions)
    (congrArg (fun direction => (sourcePoint site parameter direction).ordinate) directions)
    (first.unit_seam last originalSeam directions)

end Leg

/-- Cache the four normalized endpoint leg factories on the identical original ordered circuit.

The original circuit and common increment/admission remain indices. The
four actual cached leg values preserve all eight independent endpoint owners;
seam witnesses are derived from these values by named operations, not copied
into another cycle or supplied as final caller certificates.
-/
@[expose] def Endpoints (original : Transport.Circuit site parameter) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) :=
  { first : Leg original.first increment admitted // first = Leg.build original.first increment admitted } ×
    { second : Leg original.second increment admitted // second = Leg.build original.second increment admitted } ×
      { third : Leg original.third increment admitted // third = Leg.build original.third increment admitted } ×
        { fourth : Leg original.fourth increment admitted // fourth = Leg.build original.fourth increment admitted }

namespace Endpoints

variable {original : Transport.Circuit site parameter}

/-- Build and retain all four normalized endpoint leg caches once without querying any original Reading again. -/
def build (original : Transport.Circuit site parameter) (increment : Canonical)
    (admitted : IncrementBound site parameter increment) : Endpoints original increment admitted :=
  let first := Leg.build original.first increment admitted
  let second := Leg.build original.second increment admitted
  let third := Leg.build original.third increment admitted
  let fourth := Leg.build original.fourth increment admitted
  ⟨⟨first, rfl⟩, ⟨second, rfl⟩, ⟨third, rfl⟩, ⟨fourth, rfl⟩⟩

/-- Read the identical cached first normalized endpoint leg on its original circuit parent. -/
@[expose] def first (endpoints : Endpoints original increment admitted) : Leg original.first increment admitted :=
  endpoints.1.val

/-- Read the original second normalized endpoint leg from that same retained circuit cache. -/
@[expose] def second (endpoints : Endpoints original increment admitted) : Leg original.second increment admitted :=
  endpoints.2.1.val

/-- Read the original third normalized endpoint leg from the identical four-leg cache. -/
@[expose] def third (endpoints : Endpoints original increment admitted) : Leg original.third increment admitted :=
  endpoints.2.2.1.val

/-- Read the retained fourth normalized endpoint leg on the original ordered circuit. -/
@[expose] def fourth (endpoints : Endpoints original increment admitted) : Leg original.fourth increment admitted :=
  endpoints.2.2.2.val

/-- The first normalized leg is its exact original endpoint factory on the identical parent leg. -/
theorem first_eq (endpoints : Endpoints original increment admitted) :
    endpoints.first = Leg.build original.first increment admitted := endpoints.1.property

/-- The second normalized leg retains its exact factory on the original second parent leg. -/
theorem second_eq (endpoints : Endpoints original increment admitted) :
    endpoints.second = Leg.build original.second increment admitted := endpoints.2.1.property

/-- The third normalized leg retains the original third parent leg's exact endpoint factory. -/
theorem third_eq (endpoints : Endpoints original increment admitted) :
    endpoints.third = Leg.build original.third increment admitted := endpoints.2.2.1.property

/-- The fourth normalized leg is the retained endpoint factory on its original fourth parent. -/
theorem fourth_eq (endpoints : Endpoints original increment admitted) :
    endpoints.fourth = Leg.build original.fourth increment admitted := endpoints.2.2.2.property

/-- The original first-to-second direction join derives agreement of the two actual normalized target roots. -/
def first_second (endpoints : Endpoints original increment admitted) :
    NamedEquivalent endpoints.first.target.step.root.value.name endpoints.second.source.step.root.value.name :=
  endpoints.first.seam endpoints.second Waist.directions_join.1

/-- The retained original second-to-third direction join preserves both normalized endpoint Step owners. -/
def second_third (endpoints : Endpoints original increment admitted) :
    NamedEquivalent endpoints.second.target.step.root.value.name endpoints.third.source.step.root.value.name :=
  endpoints.second.seam endpoints.third Waist.directions_join.2.1

/-- The original third-to-fourth direction join compares the two actual retained normalized Step channels. -/
def third_fourth (endpoints : Endpoints original increment admitted) :
    NamedEquivalent endpoints.third.target.step.root.value.name endpoints.fourth.source.step.root.value.name :=
  endpoints.third.seam endpoints.fourth Waist.directions_join.2.2.1

/-- The original fourth-to-first direction closure compares both actual normalized endpoint root caches.

This is a normalized endpoint seam. Within-quarter paths and full cubic
product closure require their own original retained preparation evidence.
-/
def fourth_first (endpoints : Endpoints original increment admitted) :
    NamedEquivalent endpoints.fourth.target.step.root.value.name endpoints.first.source.step.root.value.name :=
  endpoints.fourth.seam endpoints.first Waist.directions_join.2.2.2

/-- The original first-to-second circuit seam compares both actual full target cubic endpoint products. -/
def first_second_value (endpoints : Endpoints original increment admitted) :
    NamedEquivalent endpoints.first.target.step.value.name endpoints.second.source.step.value.name :=
  endpoints.first.value_seam endpoints.second original.first_second Waist.directions_join.1

/-- The original second-to-third full-source seam derives agreement of the two retained full target products. -/
def second_third_value (endpoints : Endpoints original increment admitted) :
    NamedEquivalent endpoints.second.target.step.value.name endpoints.third.source.step.value.name :=
  endpoints.second.value_seam endpoints.third original.second_third Waist.directions_join.2.1

/-- The retained third-to-fourth original circuit seam compares both original full target endpoint products. -/
def third_fourth_value (endpoints : Endpoints original increment admitted) :
    NamedEquivalent endpoints.third.target.step.value.name endpoints.fourth.source.step.value.name :=
  endpoints.third.value_seam endpoints.fourth original.third_fourth Waist.directions_join.2.2.1

/-- The original fourth-to-first source seam gives full target product agreement at the retained endpoint closure.

This result concerns the two actual endpoint products and their original
owners. Full transported-quarter closure additionally requires the retained
within-quarter preparations and their own cofactor/product correspondence.
-/
def fourth_first_value (endpoints : Endpoints original increment admitted) :
    NamedEquivalent endpoints.fourth.target.step.value.name endpoints.first.source.step.value.name :=
  endpoints.fourth.value_seam endpoints.first original.fourth_first Waist.directions_join.2.2.2

end Endpoints

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Circuit

end
