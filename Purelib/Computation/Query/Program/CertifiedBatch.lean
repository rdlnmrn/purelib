module

public import Purelib.Computation.Query.Program
public import Purelib.Data.List.Map

/-! Ordered certified batches of dependent query results. -/

public section

namespace Purelib.Computation.Query.Program

variable {Index Item Question Reply Error : Type}

/-- An ordered list certified against its original target at every index. -/
abbrev CertifiedBatch (target : Index → Item) (indices : List Index) :=
  {items : List Item // items = indices.map target}

/-- Prepend an actual returned indexed value to a certified ordered tail. -/
@[expose] def CertifiedBatch.prepend (target : Index → Item) (Point : Index → Type)
    (build : (index : Index) → Point index → Item) (correct : ∀ index point, build index point = target index)
    (index : Index) (point : Point index) (indices : List Index) (tail : CertifiedBatch target indices) :
    CertifiedBatch target (index :: indices) :=
  ⟨build index point :: tail.val, congrArg₂ List.cons (correct index point) tail.property⟩

set_option genInjectivity false in
/-- A stopped batch retains its actual certified prefix and its original remaining indices.

The failed occurrence is between the completed prefix and unattempted suffix;
the retained equality identifies that ordering with the original input list. -/
structure CertifiedBatch.Stopped (target : Index → Item) (indices : List Index) (Error : Type) where
  /-- The exact ordered indices whose values were returned before failure. -/ before : List Index
  /-- The original occurrence whose request failed. -/ failed : Index
  /-- The original occurrences not yet attempted. -/ after : List Index
  /-- The original list decomposes into the retained prefix, failure and suffix. -/ indices_eq :
    indices = before ++ failed :: after
  /-- The actual completed values and their exact target certificate. -/ completed : CertifiedBatch target before
  /-- The original point operation's failure, including any accumulated work. -/ reason : Error

/-- Retain one actual returned item before an already stopped certified tail. -/
@[expose] def CertifiedBatch.Stopped.prepend (target : Index → Item) (Point : Index → Type)
    (build : (index : Index) → Point index → Item) (correct : ∀ index point, build index point = target index)
    (retainFailure : (index : Index) → Point index → Error → Error) (index : Index) (point : Point index)
    (remaining : List Index) (stopped : CertifiedBatch.Stopped target remaining Error) :
    CertifiedBatch.Stopped target (index :: remaining) Error :=
  ⟨index :: stopped.before, stopped.failed, stopped.after,
    congrArg (List.cons index) stopped.indices_eq,
    CertifiedBatch.prepend target Point build correct index point stopped.before stopped.completed,
    retainFailure index point stopped.reason⟩

/-- Concatenate two actual certified batches without reconstructing either value list. -/
@[expose] def CertifiedBatch.append (target : Index → Item) (before after : List Index)
    (first : CertifiedBatch target before) (second : CertifiedBatch target after) :
    CertifiedBatch target (before ++ after) :=
  ⟨first.val ++ second.val,
    (congrArg₂ List.append first.property second.property).trans
      (Purelib.Data.List.Map.map_append target before after).symm⟩

/-- Finish a stopped batch using its actual saved prefix, returned failed point and certified suffix. -/
@[expose] def CertifiedBatch.Stopped.finish (target : Index → Item) (Point : Index → Type)
    (build : (index : Index) → Point index → Item) (correct : ∀ index point, build index point = target index)
    {indices : List Index} (stopped : CertifiedBatch.Stopped target indices Error) (point : Point stopped.failed)
    (after : CertifiedBatch target stopped.after) : CertifiedBatch target indices :=
  stopped.indices_eq.symm ▸
    CertifiedBatch.append target stopped.before (stopped.failed :: stopped.after) stopped.completed
      (CertifiedBatch.prepend target Point build correct stopped.failed point stopped.after after)

/-- Advance a stopped batch through its failed point and retain any later stopped suffix.

The new certified prefix contains the exact prior prefix, the returned point
and the actual completed suffix; the original failed occurrence and remaining
indices retain their order. The later error may carry an updated cache owner. -/
@[expose] def CertifiedBatch.Stopped.advance (target : Index → Item) (Point : Index → Type)
    (build : (index : Index) → Point index → Item) (correct : ∀ index point, build index point = target index)
    {indices : List Index} (stopped : CertifiedBatch.Stopped target indices Error) (point : Point stopped.failed)
    {NextError : Type} (later : CertifiedBatch.Stopped target stopped.after NextError) :
    CertifiedBatch.Stopped target indices NextError := by
  have suffix := congrArg (fun tail : List Index => stopped.before ++ stopped.failed :: tail) later.indices_eq
  have grouped := (List.append_assoc stopped.before (stopped.failed :: later.before)
    (later.failed :: later.after)).symm
  exact ⟨stopped.before ++ stopped.failed :: later.before, later.failed, later.after,
    stopped.indices_eq.trans (suffix.trans grouped),
    CertifiedBatch.append target stopped.before (stopped.failed :: later.before) stopped.completed
      (CertifiedBatch.prepend target Point build correct stopped.failed point later.before later.completed),
    later.reason⟩

/-- Execute a batch while retaining its exact certified prefix if an occurrence fails.

Each returned item is consumed once. The failure records the original failed
index and the untouched suffix, so a continuation can reuse the prefix. -/
@[expose] def certifiedBatchProgress (target : Index → Item) (Point : Index → Type)
    (build : (index : Index) → Point index → Item) (correct : ∀ index point, build index point = target index)
    (retainFailure : (index : Index) → Point index → Error → Error)
    (point : (index : Index) → Program Question Reply (Except Error (Point index))) :
    (indices : List Index) →
      Program Question Reply (Except (CertifiedBatch.Stopped target indices Error) (CertifiedBatch target indices))
  | [] => .pure (.ok ⟨[], rfl⟩)
  | index :: remaining => (point index).bind fun returned =>
      match returned with
      | .error invalid => .pure (.error ⟨[], index, remaining, rfl, ⟨[], rfl⟩, invalid⟩)
      | .ok value => (certifiedBatchProgress target Point build correct retainFailure point remaining).map fun after =>
          match after with
          | .error invalid => .error
              (CertifiedBatch.Stopped.prepend target Point build correct retainFailure index value remaining invalid)
          | .ok tail => .ok (CertifiedBatch.prepend target Point build correct index value remaining tail)

/-- Execute original indexed requests in order and retain their certified actual returned items.

A failure preserves the original point operation's error, including its
accumulated work, and no later index is requested. -/
@[expose] def certifiedBatch (target : Index → Item) (Point : Index → Type)
    (build : (index : Index) → Point index → Item) (correct : ∀ index point, build index point = target index)
    (retainFailure : (index : Index) → Point index → Error → Error)
    (point : (index : Index) → Program Question Reply (Except Error (Point index))) (indices : List Index) :
    Program Question Reply (Except Error (CertifiedBatch target indices)) :=
  (certifiedBatchProgress target Point build correct retainFailure point indices).map fun result =>
    match result with
    | .error stopped => .error stopped.reason
    | .ok completed => .ok completed

/-- Original indexed replies return the exact original ordered target items with progress certificates. -/
theorem certifiedBatchProgress_original [DecidableEq Question] (target : Index → Item) (Point : Index → Type)
    (build : (index : Index) → Point index → Item) (correct : ∀ index point, build index point = target index)
    (retainFailure : (index : Index) → Point index → Error → Error)
    (point : (index : Index) → Program Question Reply (Except Error (Point index)))
    (oracle : Question → Reply) (expected : (index : Index) → Point index)
    (point_original : ∀ index, ((point index).protocol.run oracle).value = .ok (expected index)) :
    ∀ indices : List Index,
      ((certifiedBatchProgress target Point build correct retainFailure point indices).protocol.run oracle).value =
        .ok ⟨indices.map target, rfl⟩
  | [] => rfl
  | index :: remaining => by
      change (((point index).bind fun returned =>
        (match returned with
        | .error invalid => Program.pure (Except.error ⟨[], index, remaining, rfl, ⟨[], rfl⟩, invalid⟩)
        | .ok value => (certifiedBatchProgress target Point build correct retainFailure point remaining).map
            fun (after : Except (CertifiedBatch.Stopped target remaining Error) (CertifiedBatch target remaining)) =>
              match after with
              | .error invalid => Except.error
                  (CertifiedBatch.Stopped.prepend target Point build correct retainFailure index value
                    remaining invalid)
              | .ok tail => Except.ok (CertifiedBatch.prepend target Point build correct index value remaining tail) :
          Program Question Reply (Except (CertifiedBatch.Stopped target (index :: remaining) Error)
            (CertifiedBatch target (index :: remaining))))).protocol.run oracle).value = _
      rw [Program.bind_execution, Protocol.bind_run_value, point_original]
      rw [Program.map_execution, Protocol.map_run_value,
        certifiedBatchProgress_original target Point build correct retainFailure point oracle expected
          point_original remaining]
      apply congrArg Except.ok
      apply Subtype.ext
      change build index (expected index) :: _ = _
      rewrite [correct]
      rfl

/-- Original indexed replies return the exact original ordered target items. -/
theorem certifiedBatch_original [DecidableEq Question] (target : Index → Item) (Point : Index → Type)
    (build : (index : Index) → Point index → Item) (correct : ∀ index point, build index point = target index)
    (retainFailure : (index : Index) → Point index → Error → Error)
    (point : (index : Index) → Program Question Reply (Except Error (Point index)))
    (oracle : Question → Reply) (expected : (index : Index) → Point index)
    (point_original : ∀ index, ((point index).protocol.run oracle).value = .ok (expected index))
    (indices : List Index) :
    ((certifiedBatch target Point build correct retainFailure point indices).protocol.run oracle).value =
      .ok ⟨indices.map target, rfl⟩ := by
  unfold certifiedBatch
  rw [Program.map_execution, Protocol.map_run_value,
    certifiedBatchProgress_original target Point build correct retainFailure point oracle expected
      point_original indices]

/-- The original batch displays exactly the progress-bearing batch's ordered source requests. -/
theorem certifiedBatch_trace [DecidableEq Question] (target : Index → Item) (Point : Index → Type)
    (build : (index : Index) → Point index → Item) (correct : ∀ index point, build index point = target index)
    (retainFailure : (index : Index) → Point index → Error → Error)
    (point : (index : Index) → Program Question Reply (Except Error (Point index)))
    (indices : List Index) (oracle : Question → Reply) :
    ((certifiedBatch target Point build correct retainFailure point indices).protocol.run oracle).trace =
      ((certifiedBatchProgress target Point build correct retainFailure point indices).protocol.run oracle).trace := by
  unfold certifiedBatch
  rw [Program.map_execution, Protocol.map_run_trace]

end Purelib.Computation.Query.Program

end
