module

public import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached coherent realizations of original root-track families

The structural spine follows the original ordered track list. Each entry is a
certificate indexed by that actual original track, so lookup retains the same
nominal owner and its existing approximation cache at the original Fin index.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot

set_option genInjectivity false in
/-- A structural cache of coherent root certificates indexed by the original ordered track list. -/
inductive Family {polynomial : GaussianPolynomial} {ambient : Box} :
    List (WindingOneTrack polynomial ambient) → Type 1 where
  /-- The original empty family has no cached root entries. -/
  | nil : Family []
  /-- Retain the original head track's actual certificate and the original tail cache. -/
  | cons {head : WindingOneTrack polynomial ambient} {tail : List (WindingOneTrack polynomial ambient)}
      (root : CertifiedName head) (remaining : Family tail) : Family (head :: tail)

constructive_injectivity Family

namespace Family

/-- Construct each original root's approximation cache once in the original list order. -/
@[expose] def ofTracks {polynomial : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < polynomial.natDegree) : (tracks : List (WindingOneTrack polynomial ambient)) →
    Family tracks
  | [] => .nil
  | head :: tail => .cons (certifiedName head degreePositive) (ofTracks degreePositive tail)

/-- Read the retained root certificate at its exact original bounded track-list index. -/
@[expose] def get {polynomial : GaussianPolynomial} {ambient : Box} :
    {tracks : List (WindingOneTrack polynomial ambient)} → Family tracks →
    (index : Fin tracks.length) → CertifiedName (tracks.get index)
  | [], .nil, index => Fin.elim0 index
  | _ :: _, .cons head _, ⟨0, _⟩ => head
  | _ :: _, .cons _ tail, ⟨index + 1, bound⟩ =>
      get tail ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- Zero lookup returns the actual retained head certificate without rebuilding its cache. -/
theorem get_head {polynomial : GaussianPolynomial} {ambient : Box}
    {head : WindingOneTrack polynomial ambient} {tail : List (WindingOneTrack polynomial ambient)}
    (root : CertifiedName head) (remaining : Family tail) :
    (Family.cons root remaining).get 0 = root := rfl

/-- Successor lookup consumes the original retained tail cache and predecessor index. -/
theorem get_tail {polynomial : GaussianPolynomial} {ambient : Box}
    {head : WindingOneTrack polynomial ambient} {tail : List (WindingOneTrack polynomial ambient)}
    (root : CertifiedName head) (remaining : Family tail) (index : Fin tail.length) :
    (Family.cons root remaining).get index.succ = remaining.get index := rfl

end Family

namespace StateCache

variable {polynomial : GaussianPolynomial} {ambient : Box}

/-- Original root-state entry lists stored along their exact finite track spine.

The empty track list stores unit. Each successor stores its actual head-track
entries and the original tail bank as an ordinary product in the same universe.
-/
@[expose] def FamilyEntries :
    List (WindingOneTrack polynomial ambient) → Type
  | [] => Unit
  | head :: remaining => List (StateCache.Entry head) × FamilyEntries remaining

namespace FamilyEntries

/-- Read the exact original owner cell from the retained finite product spine. -/
@[expose] def get : {tracks : List (WindingOneTrack polynomial ambient)} →
    FamilyEntries tracks → (owner : Fin tracks.length) → List (StateCache.Entry (tracks.get owner))
  | [], _, owner => Fin.elim0 owner
  | _ :: _, (first, _), ⟨0, _⟩ => first
  | _ :: _, (_, remaining), ⟨owner + 1, bound⟩ =>
      get remaining ⟨owner, Nat.lt_of_succ_lt_succ bound⟩

/-- Replace one exact original owner cell, retaining every other stored cell and tail. -/
@[expose] def set : {tracks : List (WindingOneTrack polynomial ambient)} →
    FamilyEntries tracks → (owner : Fin tracks.length) →
    List (StateCache.Entry (tracks.get owner)) → FamilyEntries tracks
  | [], _, owner, _ => Fin.elim0 owner
  | _ :: _, (_, remaining), ⟨0, _⟩, entries => (entries, remaining)
  | _ :: _, (first, remaining), ⟨owner + 1, bound⟩, entries =>
      (first, set remaining ⟨owner, Nat.lt_of_succ_lt_succ bound⟩ entries)

/-- Reading the replaced original owner cell returns exactly the supplied complete entries. -/
theorem get_set_same : ∀ {tracks : List (WindingOneTrack polynomial ambient)}
    (bank : FamilyEntries tracks) (owner : Fin tracks.length)
    (entries : List (StateCache.Entry (tracks.get owner))),
    (bank.set owner entries).get owner = entries
  | [], _, owner, _ => Fin.elim0 owner
  | _ :: _, (_, _), ⟨0, _⟩, _ => rfl
  | _ :: _, (_, remaining), ⟨owner + 1, bound⟩, entries =>
      get_set_same remaining ⟨owner, Nat.lt_of_succ_lt_succ bound⟩ entries

/-- Replacing one original owner preserves every distinct original owner's complete entry list. -/
theorem get_set_other : ∀ {tracks : List (WindingOneTrack polynomial ambient)}
    (bank : FamilyEntries tracks) (owner other : Fin tracks.length)
    (entries : List (StateCache.Entry (tracks.get owner))), other ≠ owner →
    (bank.set owner entries).get other = bank.get other
  | [], _, owner, _, _, _ => Fin.elim0 owner
  | _ :: _, (_, _), ⟨0, _⟩, ⟨0, _⟩, _, different => (different rfl).elim
  | _ :: _, (_, _), ⟨0, _⟩, ⟨_ + 1, _⟩, _, _ => rfl
  | _ :: _, (_, _), ⟨_ + 1, _⟩, ⟨0, _⟩, _, _ => rfl
  | _ :: _, (_, remaining), ⟨owner + 1, ownerBound⟩, ⟨other + 1, otherBound⟩, entries, different =>
      get_set_other remaining ⟨owner, Nat.lt_of_succ_lt_succ ownerBound⟩
        ⟨other, Nat.lt_of_succ_lt_succ otherBound⟩ entries
        (fun equal => different (congrArg Fin.succ equal))

/-- Materialize each actual original root's initial entry once along the retained family spine. -/
@[expose] def initial : {tracks : List (WindingOneTrack polynomial ambient)} →
    (roots : Family tracks) → FamilyEntries tracks
  | [], .nil => ()
  | head :: _, .cons _ remaining =>
      ([first head], initial remaining)

/-- Each initial cell contains the original first entry of the actual retained track at that owner. -/
theorem get_initial : ∀ {tracks : List (WindingOneTrack polynomial ambient)}
    (roots : Family tracks) (owner : Fin tracks.length),
    (initial roots).get owner =
      [first (tracks.get owner)]
  | [], .nil, owner => Fin.elim0 owner
  | _ :: _, .cons _ _, ⟨0, _⟩ => rfl
  | _ :: _, .cons _ remaining, ⟨owner + 1, bound⟩ =>
      get_initial remaining ⟨owner, Nat.lt_of_succ_lt_succ bound⟩

end FamilyEntries

end StateCache

end Purelib.Riemann.RootContinuation.CoherentRoot

end
