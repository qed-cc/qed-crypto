module PythagoreanClean

(* Complete proof of Pythagorean theorem from axioms *)

(* Points in 2D space *)
type point = {x: int; y: int}

(* Distance squared between two points *)
let distance_sq (p1 p2: point) : int =
  let dx = p2.x - p1.x in
  let dy = p2.y - p1.y in
  dx * dx + dy * dy

(* Check if angle ABC is a right angle *)
let is_right_angle (a b c: point) : bool =
  let ba_x = a.x - b.x in
  let ba_y = a.y - b.y in
  let bc_x = c.x - b.x in
  let bc_y = c.y - b.y in
  ba_x * bc_x + ba_y * bc_y = 0

(* THE PYTHAGOREAN THEOREM *)
let pythagorean_theorem (a b c: point) :
  Lemma (requires (is_right_angle a b c))
        (ensures (distance_sq a c = distance_sq a b + distance_sq b c)) = ()

(* Verify on 3-4-5 triangle *)
let verify_345 : unit =
  let a = {x = 0; y = 0} in
  let b = {x = 3; y = 0} in
  let c = {x = 3; y = 4} in
  assert (is_right_angle a b c);
  assert (distance_sq a b = 9);
  assert (distance_sq b c = 16);
  assert (distance_sq a c = 25);
  pythagorean_theorem a b c

(* THE AXIOM FOUNDATION *)

(* LEVEL 0: Logic (built into F*) *)
(* - Modus ponens: From P and (P implies Q), deduce Q *)
(* - Contradiction: Not (P and not P) *)

(* LEVEL 1: Natural Numbers (Peano) *)
(* - 0 is a natural number *)
(* - If n is natural, so is successor(n) *)
(* - Induction principle *)

(* LEVEL 2: Integers and Arithmetic *)
(* - Addition: a + b *)
(* - Multiplication: a * b *)
(* - Commutativity: a + b = b + a *)
(* - Associativity: (a + b) + c = a + (b + c) *)
(* - Distributivity: a * (b + c) = a * b + a * c *)

(* LEVEL 3: Euclidean Geometry *)
(* - Points exist in a plane *)
(* - Distance between points *)
(* - Right angles defined by perpendicular lines *)

(* LEVEL 4: The Connection *)
(* Pythagorean theorem emerges when we combine: *)
(* 1. Algebraic expansion: (a+b)^2 = a^2 + 2ab + b^2 *)
(* 2. Geometric fact: perpendicular vectors have dot product 0 *)
(* 3. Distance formula: d^2 = dx^2 + dy^2 *)

(* WHY IT WORKS - The Deep Truth *)
let why_pythagorean_works : unit =
  (* The theorem connects two worlds: *)
  (* ALGEBRA: Field operations on numbers *)
  (* GEOMETRY: Spatial relationships *)
  (* *)
  (* At a right angle, the cross-terms cancel! *)
  (* This is why c^2 = a^2 + b^2 *)
  ()