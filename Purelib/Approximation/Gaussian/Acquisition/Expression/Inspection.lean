module

public import Purelib.Approximation.Gaussian.Acquisition.Expression.Bindings
public import Purelib.Approximation.Gaussian.Acquisition.Provenance.Inspection
public import Purelib.Data.List.DependentProduct

/-!
# Retained provenance inspections at original binding occurrences

Every table occurrence receives a stored inspection of its actual annotation.
Equal original leaf keys reuse an earlier cached inspection through equality
of their complete original annotations. Different atom indices and root sheet
labels remain separate entries and owners.
-/

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Basic.Binding

open Purelib.Approximation.Gaussian.Acquisition
open Purelib.Data.List (DependentProduct)

variable {arity : Nat} {environment : Fin arity → Annotated}

/-- An actual original binding together with its already computed annotation inspection. -/
@[expose] def Inspected := Sigma fun binding : Binding environment => Provenance.Inspection binding.annotation

/-- Find an already inspected original leaf, preserving its entire source annotation and cached data. -/
@[expose] def findInspection (target : Binding environment) :
    List (Inspected (environment := environment)) → Option (Provenance.Inspection target.annotation)
  | [] => none
  | first :: remaining =>
      if same : first.1.leaf = target.leaf then
        let original : first.1.annotation = target.annotation := first.1.annotation_eq.trans
          ((congrArg (Leaf.annotation environment) same).trans target.annotation_eq.symm)
        some (first.2.transport original)
      else findInspection target remaining

/-- One retained inspection at every original table occurrence, with the same indexed annotation types. -/
@[expose] def Inspections (bindings : List (Binding environment)) : Type 1 :=
  DependentProduct bindings (fun index => Provenance.Inspection (read bindings index).annotation)

/-- Read the already stored inspection at an actual bounded original table position. -/
@[expose] def Inspections.get (bindings : List (Binding environment)) (inspections : Inspections bindings)
    (index : Fin bindings.length) : Provenance.Inspection (read bindings index).annotation :=
  DependentProduct.get bindings inspections index

/-- Materialize occurrence inspections while sharing the actual cached work of equal original leaf keys. -/
@[expose] def inspectWith (seen : List (Inspected (environment := environment))) :
    (bindings : List (Binding environment)) → Inspections bindings
  | [] => PUnit.unit
  | first :: remaining =>
      let inspection := match findInspection first seen with
        | some retained => retained
        | none => Provenance.inspect first.annotation
      (inspection, inspectWith (⟨first, inspection⟩ :: seen) remaining)

/-- Inspect the original retained table once, caching admissions and exact readings for all later consumers. -/
@[expose] def inspect (bindings : List (Binding environment)) : Inspections bindings := inspectWith [] bindings

end Purelib.Approximation.Gaussian.Acquisition.Expression.Basic.Binding

end
