module Pythagoras

(* Pythagorean Theorem: Proof from Mathematical Axioms *)

type point = {x: int; y: int}

let distance_squared (p1 p2: point) : int =
  let dx = p2.x - p1.x in
  let dy = p2.y - p1.y in
  dx * dx + dy * dy

let dot_product (ax ay bx by: int) : int = 
  ax * bx + ay * by

let is_right_angle_at_b (a b c: point) : bool =
  let ba_x = a.x - b.x in
  let ba_y = a.y - b.y in
  let bc_x = c.x - b.x in
  let bc_y = c.y - b.y in
  dot_product ba_x ba_y bc_x bc_y = 0

(* THEOREM: For right triangle ABC with right angle at B *)
(* |AC|^2 = |AB|^2 + |BC|^2 *)
let pythagorean_theorem (a b c: point) :
  Lemma 
    (requires (is_right_angle_at_b a b c))
    (ensures (distance_squared a c = 
              distance_squared a b + distance_squared b c)) = ()

(* Example: The 3-4-5 triangle *)
let example_345 : unit =
  let o = {x = 0; y = 0} in
  let a = {x = 3; y = 0} in  
  let b = {x = 3; y = 4} in
  
  (* Verify right angle *)
  assert (is_right_angle_at_b o a b);
  
  (* Verify distances *)
  assert (distance_squared o a = 9);
  assert (distance_squared a b = 16);
  assert (distance_squared o b = 25);
  
  (* Apply theorem *)
  pythagorean_theorem o a b;
  assert (9 + 16 = 25)