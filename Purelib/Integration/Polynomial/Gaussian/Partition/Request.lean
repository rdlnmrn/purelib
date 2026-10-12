module

import Purelib.Data.Rat.Fraction
public import Purelib.Integration.Polynomial.Gaussian.Partition.Source
import Purelib.Integration.Polynomial.Gaussian.Segment.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Source-indexed Gaussian polynomial partitions

The ordered source segments retain their cut requests, child restrictions and
cached integral samples. Compilation and comparison preserve the nominal
source owners, dependent indices and exact ordered model readbacks.
-/

public section
namespace Purelib.Integration.Polynomial.Gaussian.Partition

open Purelib.Data.Rat

open Purelib.Integration.Polynomial.Gaussian.Segment.Basic (PolynomialSegment)
set_option genInjectivity false in
/-- An original source-path-indexed list of rational cut requests, one per segment.

The dependent constructors retain the original segment list while keeping the supplied cut order for every segment. -/
inductive Request.CutRequest : Source.PolynomialPath → Type
  /-- The empty request for the exact empty original source path. -/ | nil :
    Purelib.Integration.Polynomial.Gaussian.Partition.Request.CutRequest []
  /-- Retain the original segment's cut list and the exact tail request. -/ | cons {source : PolynomialSegment} {rest :
    Source.PolynomialPath}
      (cuts : List Fraction.Rational) (tail : Purelib.Integration.Polynomial.Gaussian.Partition.Request.CutRequest rest)
        : Purelib.Integration.Polynomial.Gaussian.Partition.Request.CutRequest (source :: rest)

constructive_injectivity Request.CutRequest

@[expose] public section
set_option genInjectivity false in
/-- A serialized cut row containing its original source index and ordered rational cuts.

The source index identifies the segment claimed by this row. The rational cuts retain their supplied list order,
including repeated or out-of-interval values for later normalization. -/
structure Request.CutRow where
  /-- The original segment index claimed by this serialized row. -/ sourceIndex : Nat
  /-- The original ordered rational cuts for this row. -/ cuts : List Fraction.Rational
deriving DecidableEq

constructive_injectivity Request.CutRow

end

set_option genInjectivity false in
/-- A typed missing, extra or misindexed cut row for the exact original source and serialized rows.

Later failures retain the matched original row and tail error, so the certificate identifies where the original request
shape failed. -/
inductive Request.CutError : Nat → Source.PolynomialPath → List Request.CutRow → Type
  /-- The original nonempty source still needs a row but the row list is empty. -/ | missingCell (offset : Nat) (source
    : PolynomialSegment) (rest : Source.PolynomialPath) :
      Purelib.Integration.Polynomial.Gaussian.Partition.Request.CutError offset (source :: rest) []
  /-- The original source is exhausted while a retained row remains. -/ | extraCell (offset : Nat) (row :
    Request.CutRow) (rows : List Request.CutRow) :
      Purelib.Integration.Polynomial.Gaussian.Partition.Request.CutError offset [] (row :: rows)
  /-- The retained row's source index differs from the expected original offset. -/ | wrongCell (offset : Nat) (source :
    PolynomialSegment) (rest : Source.PolynomialPath)
      (row : Request.CutRow) (rows : List Request.CutRow) (different : row.sourceIndex ≠ offset) :
      Purelib.Integration.Polynomial.Gaussian.Partition.Request.CutError offset (source :: rest) (row :: rows)
  /-- The current original row matched, and the retained failure occurs in its exact tail. -/ | afterCell (offset : Nat)
    (source : PolynomialSegment) (rest : Source.PolynomialPath)
      (row : Request.CutRow) (rows : List Request.CutRow) (matched : row.sourceIndex = offset)
      (tail : Purelib.Integration.Polynomial.Gaussian.Partition.Request.CutError (offset + 1) rest rows) :
      Purelib.Integration.Polynomial.Gaussian.Partition.Request.CutError offset (source :: rest) (row :: rows)

constructive_injectivity Request.CutError

/-- Assign the same retained cut list to every segment of the exact original source path.

Each source segment keeps the supplied cut list, and recursion follows the same ordered source tail. -/
@[expose] def Request.CutRequest.every (cuts : List Fraction.Rational) : (source : Source.PolynomialPath) →
  Request.CutRequest source
  | [] => .nil
  | _ :: rest => .cons cuts (Purelib.Integration.Polynomial.Gaussian.Partition.Request.CutRequest.every cuts rest)

/-- Decode original serialized cut rows against the exact source path and starting index.

Success retains the path-indexed request; failure records a missing row, extra row, wrong source index or exact later
failure. -/
@[expose] def Request.CutRequest.decode (offset : Nat) : (source : Source.PolynomialPath) → (rows : List Request.CutRow)
  →
    Except (Request.CutError offset source rows) (Request.CutRequest source)
  | [], rows =>
      match rows with
      | [] => .ok .nil
      | row :: rows => .error (.extraCell offset row rows)
  | source :: rest, rows =>
      match rows with
      | [] => .error (.missingCell offset source rest)
      | row :: rows =>
          if matched : row.sourceIndex = offset then
            match Purelib.Integration.Polynomial.Gaussian.Partition.Request.CutRequest.decode (offset + 1) rest rows
              with
            | .error error => .error (.afterCell offset source rest row rows matched error)
            | .ok tail => .ok (.cons row.cuts tail)
          else .error (.wrongCell offset source rest row rows matched)

/-- Serialize the retained source-indexed cut request from the supplied original starting index.

Each row retains the supplied starting index and cut list. The tail advances that index exactly once per source segment.
-/
@[expose] def Request.CutRequest.serialize (offset : Nat) {source : Source.PolynomialPath} : Request.CutRequest source →
  List Request.CutRow
  | .nil => []
  | .cons cuts tail => ⟨offset, cuts⟩ :: Purelib.Integration.Polynomial.Gaussian.Partition.Request.CutRequest.serialize
    (offset + 1) tail

/-- Decoding an original request's serialization recovers that exact request.

The retained source indices match each serialized row, and decoding the ordered tail recovers the same dependent
request. -/
theorem Request.CutRequest.decode_serialize (offset : Nat) : ∀ {source : Source.PolynomialPath} (request :
  Request.CutRequest source),
    Request.CutRequest.decode offset source (Request.CutRequest.serialize offset request) = .ok request
  | [], .nil => rfl
  | _ :: _, .cons cuts tail => by
      rw [Request.CutRequest.serialize, Request.CutRequest.decode, dif_pos rfl,
        Purelib.Integration.Polynomial.Gaussian.Partition.Request.CutRequest.decode_serialize (offset + 1) tail]

/-- A retained cut error proves the original rows cannot serialize any request for that exact source and offset.

The certificate retains the exact source path, offset and rows. Missing, extra and misindexed rows contradict the
corresponding serialized request shape. -/
theorem Request.CutError.rejects_serialization :
    {offset : Nat} → {source : Source.PolynomialPath} → {rows : List Request.CutRow} →
      (failure : Request.CutError offset source rows) → (request : Request.CutRequest source) →
        rows ≠ Request.CutRequest.serialize offset request
  | _, _, _, .missingCell _ _ _, .cons _ _ => by
      intro equal
      nomatch equal
  | _, _, _, .extraCell _ _ _, .nil => by
      intro equal
      nomatch equal
  | _, _, _, .wrongCell _ _ _ _ _ different, .cons _ _ => by
      intro equal
      exact different (congrArg Request.CutRow.sourceIndex (List.cons.inj equal).1)
  | _, _, _, .afterCell _ _ _ _ _ _ tail, .cons _ request => by
      intro equal
      exact tail.rejects_serialization request (List.cons.inj equal).2

end Purelib.Integration.Polynomial.Gaussian.Partition
end
