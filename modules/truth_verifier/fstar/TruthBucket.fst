module TruthBucket

(* Core truth bucket system with compile-time proofs *)

(* Define bucket types *)
type bucket_type =
  | Truth
  | False  
  | Derived
  | Uncertain
  | Philosophical

(* Define hash algorithms *)
type hash_algorithm =
  | SHA3_256
  | SHA3_512
  | SHA2_256  (* Not allowed! *)
  | Blake3    (* Not allowed! *)

(* Only SHA3 is allowed *)
let is_allowed_hash (h: hash_algorithm) : bool =
  match h with
  | SHA3_256 -> true
  | SHA3_512 -> true
  | _ -> false

(* T005: Only SHA3 allowed - proven at compile time *)
let t005_only_sha3 : unit =
  assert (is_allowed_hash SHA3_256);
  assert (is_allowed_hash SHA3_512);
  assert (not (is_allowed_hash SHA2_256));
  assert (not (is_allowed_hash Blake3))