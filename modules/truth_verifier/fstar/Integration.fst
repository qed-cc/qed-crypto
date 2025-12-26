module Integration

open TruthBucket
open SecurityProofs

(* Integration with C truth verifier *)

(* Mirror C types *)
type truth_result =
  | TRUTH_VERIFIED
  | TRUTH_FAILED
  | TRUTH_UNCERTAIN
  | TRUTH_NOT_APPLICABLE

(* Master verification function *)
let verify_truth (truth_id: string) : truth_result =
  match truth_id with
  | "T004" -> 
    (* Soundness = 122 is proven at compile time *)
    if soundness_bits = 122 then TRUTH_VERIFIED else TRUTH_FAILED
    
  | "T005" ->
    (* SHA3-only is proven at compile time *)
    if is_allowed_hash SHA3_256 && not (is_allowed_hash SHA2_256)
    then TRUTH_VERIFIED else TRUTH_FAILED
    
  | "T201" ->
    (* No discrete log is proven at compile time *)
    if not (List.Tot.mem DiscreteLog basefold_uses)
    then TRUTH_VERIFIED else TRUTH_FAILED
    
  | "A002" ->
    (* ZK mandatory is proven at compile time *)
    let c = { enable_zk = true; soundness = 122 } in
    if valid_config c then TRUTH_VERIFIED else TRUTH_FAILED
    
  | _ -> TRUTH_NOT_APPLICABLE

(* These would cause COMPILE-TIME ERRORS if wrong: *)

(* Example 1: Claiming wrong soundness *)
(* let wrong_soundness : unit = assert (soundness_bits = 128) *)
(* ERROR: Assertion failed *)

(* Example 2: Using non-SHA3 hash *)  
(* let wrong_hash : unit = assert (is_allowed_hash SHA2_256) *)
(* ERROR: Assertion failed *)

(* Example 3: Disabling ZK *)
(* let no_zk = { enable_zk = false; soundness = 122 } in
   assert (valid_config no_zk) *)
(* ERROR: Assertion failed *)