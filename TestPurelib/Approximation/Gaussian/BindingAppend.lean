module

import Purelib.Data.List.DependentProduct
import Purelib.Approximation.Gaussian.Acquisition.Expression.Bindings
import Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Base

/-! # Whole original binding and admission append contracts

The quantified reductions preserve the actual input records, including each
sidecar's original owner and every absent slot. Identical source leaves remain
distinct bounded occurrences; no sidecar equality follows from a channel match.
-/

namespace TestPurelib.Approximation.Gaussian.BindingAppend

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Data.List (DependentProduct)

variable {arity : Nat} {environment : Fin arity → Annotated}

/-- The complete supplied right slot cache remains the actual appended tail. -/
example (head : Basic.Binding environment) (second : List (Basic.Binding environment))
    (entry : Option (Algebraic.Sidecar head.annotation.channel)) (right : Checked.Base.Slots second) :
    (Checked.Base.Slots.append [head] second (entry, PUnit.unit) right).2 = right := rfl

/-- The complete supplied right admission cache remains the actual appended tail. -/
example (head : Basic.Binding environment) (second : List (Basic.Binding environment))
    (entry : Algebraic.Sidecar head.annotation.channel) (right : Checked.Base.Admissions second) :
    (Checked.Base.Admissions.append [head] second (entry, PUnit.unit) right).2 = right := rfl

/-- The actual left optional admission remains the identical stored head after append. -/
example (head : Basic.Binding environment) (second : List (Basic.Binding environment))
    (entry : Option (Algebraic.Sidecar head.annotation.channel)) (right : Checked.Base.Slots second) :
    (Checked.Base.Slots.append [head] second (entry, PUnit.unit) right).1 = entry := rfl

/-- Both duplicate binding occurrences retain their own original records. -/
example (binding : Basic.Binding environment) :
    Basic.Binding.read ([binding] ++ [binding])
      (DependentProduct.leftIndex [binding] [binding] 0) = binding := rfl

/-- The second duplicate occurrence is read after its actual one-entry prefix. -/
example (binding : Basic.Binding environment) :
    Basic.Binding.read ([binding] ++ [binding])
      (DependentProduct.rightIndex [binding] [binding] 0) = binding := rfl

/-- Duplicated source leaves retain separate optional-admission payloads even on the same channel. -/
example (binding : Basic.Binding environment)
    (left right : Option (Algebraic.Sidecar binding.annotation.channel)) :
    Checked.Base.Slots.append [binding] [binding] (left, PUnit.unit) (right, PUnit.unit) =
      (left, right, PUnit.unit) := rfl

/-- Duplicated source leaves retain both complete sidecars rather than equating their original owners. -/
example (binding : Basic.Binding environment) (left right : Algebraic.Sidecar binding.annotation.channel) :
    Checked.Base.Admissions.append [binding] [binding] (left, PUnit.unit) (right, PUnit.unit) =
      (left, right, PUnit.unit) := rfl

/-- An absent left slot remains absent while the separately supplied right admission remains present. -/
example (binding : Basic.Binding environment) (right : Algebraic.Sidecar binding.annotation.channel) :
    Checked.Base.Slots.append [binding] [binding] (none, PUnit.unit) (some right, PUnit.unit) =
      (none, some right, PUnit.unit) := rfl

/-- Distinct source parents remain distinguishable by their bounded appended occurrences. -/
example (first second : List (Basic.Binding environment)) (left : Fin first.length) (right : Fin second.length) :
    DependentProduct.leftIndex first second left ≠ DependentProduct.rightIndex first second right :=
  DependentProduct.leftIndex_ne_rightIndex first second left right

/-- The original default Slots type is the same complete original bounded admission product. -/
example (bindings : List (Basic.Binding environment)) :
    Checked.Base.Slots bindings = DependentProduct bindings (fun index =>
      Option (Algebraic.Sidecar (Basic.Binding.read bindings index).annotation.channel)) := rfl

/-- A conjugated slot retains the actual supplied sidecar as its original conjugation parent. -/
example (binding : Basic.Binding environment) (channel : CoherentNamed) (sidecar : Algebraic.Sidecar channel) :
    (Checked.Base.Slots.conj [binding] (first := fun _ => channel)
      (second := fun _ => CoherentNamed.conj channel) (fun _ => rfl) (some sidecar, PUnit.unit)).1 =
      some sidecar.conj := rfl

/-- Double conjugation retains both actual conjugated sidecar parents at the twice conjugated numerical channel. -/
example (binding : Basic.Binding environment) (channel : CoherentNamed) (sidecar : Algebraic.Sidecar channel) :
    (Checked.Base.Slots.conj [binding] (first := fun _ => CoherentNamed.conj channel)
      (second := fun _ => CoherentNamed.conj (CoherentNamed.conj channel)) (fun _ => rfl)
      (Checked.Base.Slots.conj [binding] (first := fun _ => channel)
        (second := fun _ => CoherentNamed.conj channel) (fun _ => rfl) (some sidecar, PUnit.unit))).1 =
      some sidecar.conj.conj := rfl

end TestPurelib.Approximation.Gaussian.BindingAppend
