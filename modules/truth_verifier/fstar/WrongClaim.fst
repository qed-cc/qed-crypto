module WrongClaim

open SecurityProofs

(* This will FAIL at compile time - demonstrating F* catches errors *)

(* Try to claim 128-bit soundness instead of 122 *)
let wrong_soundness_claim : unit =
  assert (soundness_bits = 128)  (* COMPILE ERROR! *)

(* Try to disable zero-knowledge *)
let wrong_zk_config : unit =
  let bad_config = { enable_zk = false; soundness = 122 } in
  assert (valid_config bad_config)  (* COMPILE ERROR! *)