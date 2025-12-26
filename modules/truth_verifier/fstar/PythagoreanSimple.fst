module PythagoreanSimple

(* A minimal proof of the Pythagorean theorem *)

(* Points as integer coordinates *)
let distance_squared (x1 y1 x2 y2: int) : int =
  let dx = x2 - x1 in
  let dy = y2 - y1 in
  dx * dx + dy * dy

(* Check if three points form a right angle at the middle point *)
let is_right_angle (ax ay bx by cx cy: int) : bool =
  (* Vectors BA and BC *)
  let ba_x = ax - bx in
  let ba_y = ay - by in
  let bc_x = cx - bx in
  let bc_y = cy - by in
  (* Perpendicular if dot product is zero *)
  ba_x * bc_x + ba_y * bc_y = 0

(* The Pythagorean Theorem *)
(* If ABC has a right angle at B, then |AC|² = |AB|² + |BC|² *)
let pythagorean (ax ay bx by cx cy: int) :
  Lemma 
    (requires (is_right_angle ax ay bx by cx cy))
    (ensures (distance_squared ax ay cx cy = 
              distance_squared ax ay bx by + 
              distance_squared bx by cx cy)) = ()

(* Verify on the 3-4-5 triangle *)
let test_345 : unit =
  (* Triangle with vertices at (0,0), (3,0), (3,4) *)
  let ax, ay = 0, 0 in
  let bx, by = 3, 0 in  
  let cx, cy = 3, 4 in
  
  (* Check right angle at B *)
  assert (is_right_angle ax ay bx by cx cy);
  
  (* Check distances *)
  assert (distance_squared ax ay bx by = 9);   (* 3² *)
  assert (distance_squared bx by cx cy = 16);  (* 4² *)
  assert (distance_squared ax ay cx cy = 25);  (* 5² *)
  
  (* Verify theorem *)
  pythagorean ax ay bx by cx cy;
  assert (9 + 16 = 25)

(* The proof works because:
   1. We expand |AC|² algebraically
   2. The cross-terms involve the dot product BA·BC
   3. Since the angle is 90°, this dot product is 0
   4. Therefore |AC|² = |AB|² + |BC|²
*)