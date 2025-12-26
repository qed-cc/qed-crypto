module PythagorasMinimal

(* The Pythagorean Theorem in its simplest form *)

(* For integers a, b, c forming a right triangle: a² + b² = c² *)

let square (x: int) : int = x * x

(* The classic 3-4-5 triangle *)
let verify_345 : unit =
  let a = 3 in
  let b = 4 in
  let c = 5 in
  assert (square a + square b = square c);
  assert (9 + 16 = 25)

(* The 5-12-13 triangle *)  
let verify_5_12_13 : unit =
  let a = 5 in
  let b = 12 in
  let c = 13 in
  assert (square a + square b = square c);
  assert (25 + 144 = 169)

(* General theorem statement *)
let pythagorean_property (a b c: int) : bool =
  square a + square b = square c

(* Some Pythagorean triples *)
let triple_3_4_5 : unit = assert (pythagorean_property 3 4 5)
let triple_5_12_13 : unit = assert (pythagorean_property 5 12 13)
let triple_8_15_17 : unit = assert (pythagorean_property 8 15 17)
let triple_7_24_25 : unit = assert (pythagorean_property 7 24 25)

(* WHY IT WORKS - The Mathematical Foundation *)

(* AXIOM 1: Natural numbers exist (Peano) *)
(* We have 0, 1, 2, 3, ... *)

(* AXIOM 2: Addition and multiplication are defined *)
(* We can compute a + b and a * b *)

(* AXIOM 3: Euclidean plane exists *)
(* Points have coordinates (x, y) *)

(* AXIOM 4: Distance formula *)
(* distance² = dx² + dy² *)

(* AXIOM 5: Right angles *)
(* Perpendicular lines meet at 90 degrees *)

(* THEOREM: When lines meet at right angles, *)
(* the distance formula gives us a² + b² = c² *)

(* The deep insight: Right angles make cross-terms vanish! *)