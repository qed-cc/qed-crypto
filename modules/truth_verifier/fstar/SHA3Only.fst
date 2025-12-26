module SHA3Only

open BaseFoldSecurity

(* Enforce SHA3-only at the type level *)

(* This module makes it IMPOSSIBLE to use non-SHA3 hashes *)

(* Safe hash type - can only be constructed with SHA3 *)
abstract type safe_hash = h:hash_function{allowed_hash h}

(* Constructor functions - only for SHA3 *)
let make_sha3_256 () : safe_hash = SHA3_256
let make_sha3_512 () : safe_hash = SHA3_512

(* Attempting to make SHA2 would cause TYPE ERROR at compile time *)
(* let make_sha2 () : safe_hash = SHA2_256  -- COMPILE ERROR! *)

(* All Gate Computer functions must use safe_hash *)
let compute_merkle_root (h: safe_hash) (data: list nat) : nat = 
  (* Implementation would go here *)
  0

let verify_proof (h: safe_hash) (proof: list nat) : bool =
  (* Implementation would go here *)
  true

(* This GUARANTEES at compile time that only SHA3 can be used *)
let type_level_sha3_enforcement : unit =
  let h1 = make_sha3_256 () in
  let h2 = make_sha3_512 () in
  (* let h3 = SHA2_256 -- TYPE ERROR: Expected safe_hash, got hash_function *)
  assert (allowed_hash h1);
  assert (allowed_hash h2)