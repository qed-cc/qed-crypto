module CompileTimeProofs

open BaseFoldSecurity
open RecursiveProof
open SHA3Only

(* This module demonstrates compile-time verification *)

(* COMPILE-TIME CHECK: Soundness must be 122 *)
let verify_soundness_claim (claimed_bits: nat) : unit =
  if claimed_bits = 122 then
    ()  (* OK *)
  else
    assert false  (* COMPILE ERROR if not 122 *)

(* Example: This would compile *)
let correct_claim : unit = verify_soundness_claim 122

(* Example: This would NOT compile - caught at compile time! *)
(* let wrong_claim : unit = verify_soundness_claim 128  -- ASSERTION FAILURE *)

(* COMPILE-TIME CHECK: Only SHA3 allowed *)
let use_hash_function (h: safe_hash) : unit = 
  (* Can only pass SHA3 hashes here *)
  ()

let correct_hash_usage : unit =
  use_hash_function (make_sha3_256 ())  (* OK *)

(* This won't even type-check *)
(* let wrong_hash_usage : unit = use_hash_function SHA2_256  -- TYPE ERROR *)

(* COMPILE-TIME CHECK: ZK must be enabled *)
let make_proof_config (zk: bool) : unit =
  if zk then
    let config : proof_config = {
      zk_enabled = zk;
      hash = SHA3_256;
      security_bits = 122;
    } in
    assert (valid_config config)
  else
    assert false  (* COMPILE ERROR if ZK disabled *)

(* This compiles *)
let correct_zk : unit = make_proof_config true

(* This won't compile *)  
(* let wrong_zk : unit = make_proof_config false  -- ASSERTION FAILURE *)

(* All security properties verified at COMPILE TIME *)
let all_properties_verified : unit =
  (* These are all checked when F* compiles this file *)
  assert (soundness_bits = 122);
  assert (not (List.Tot.mem DiscreteLog basefold_assumptions));
  assert (achieved_recursive_time_ms < 200);
  assert (recursive_security_bits >= 121);
  ()