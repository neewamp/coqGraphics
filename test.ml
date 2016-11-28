type unit0 =
| Tt

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q0 -> XO (succ q0)
       | XO q0 -> XI q0
       | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Coq_Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> Eq
       | Zpos _ -> Lt
       | Zneg _ -> Gt)
    | Zpos x' ->
      (match y with
       | Zpos y' -> Coq_Pos.compare x' y'
       | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True
 end

type q = { qnum : z; qden : positive }

(** val qnum : q -> z **)

let qnum x = x.qnum

(** val qden : q -> positive **)

let qden x = x.qden

(** val qle_bool : q -> q -> bool **)

let qle_bool x y =
  Z.leb (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

type color =
| Red
| Blue
| Green
| White

type point = (positive, positive) prod

type g_com =
| Open_graph of point
| Resize_window of point
| Plot of point * point * color
| Draw_rect of point * point * color
| Seq of g_com * g_com

type 't graphics_prims = { init_state : (unit0 -> 't); update_state : ('t -> point -> 't); draw_pixel : ('t -> point -> color -> 't) }

(** val init_state : 'a1 graphics_prims -> unit0 -> 'a1 **)

let init_state x = x.init_state

(** val update_state : 'a1 graphics_prims -> 'a1 -> point -> 'a1 **)

let update_state x = x.update_state

(** val draw_pixel : 'a1 graphics_prims -> 'a1 -> point -> color -> 'a1 **)

let draw_pixel x = x.draw_pixel

(** val pos_to_nat : positive -> nat **)

let rec pos_to_nat = function
| XI p' -> add (add (pos_to_nat p') (pos_to_nat p')) (S O)
| XO p' -> add (pos_to_nat p') (pos_to_nat p')
| XH -> S O

(** val nat_to_pos : nat -> positive **)

let rec nat_to_pos = function
| O -> XH
| S n' -> Coq_Pos.succ (nat_to_pos n')

(** val draw_line_rc : 'a1 graphics_prims -> 'a1 -> point -> color -> nat -> q -> q -> 'a1 **)

let rec draw_line_rc h t0 p c i er der =
  match i with
  | O -> h.draw_pixel t0 p c
  | S i' ->
    let Pair (x, y) = p in
    h.draw_pixel
      (match qle_bool { qnum = (Zpos XH); qden = XH } (qplus er der) with
       | True -> draw_line_rc h t0 (Pair (x, (Coq_Pos.add y XH))) c i' (qplus der (qminus er { qnum = (Zpos XH); qden = XH })) der
       | False ->
         (match qle_bool (qplus er der) { qnum = (Zneg XH); qden = XH } with
          | True -> draw_line_rc h t0 (Pair (x, (Coq_Pos.sub y XH))) c i' (qplus der (qplus er { qnum = (Zpos XH); qden = XH })) der
          | False -> draw_line_rc h t0 p c i' (qplus der er) der)) (Pair ((Coq_Pos.add x (nat_to_pos i)), y)) c

(** val interp_draw_line : 'a1 graphics_prims -> 'a1 -> color -> point -> point -> 'a1 **)

let interp_draw_line h t0 c p1 p2 =
  let Pair (x1, y1) = p1 in
  let Pair (x2, y2) = p2 in
  draw_line_rc h t0 p1 c (pos_to_nat (Coq_Pos.sub x2 x1)) { qnum = (Zneg XH); qden = XH } { qnum = (Zpos (Coq_Pos.sub y2 y1)); qden =
    (Coq_Pos.sub x2 x1) }

(** val interp : 'a1 graphics_prims -> 'a1 -> g_com -> 'a1 **)

let rec interp h t0 = function
| Open_graph s_size -> h.update_state t0 s_size
| Resize_window s_size -> h.update_state t0 s_size
| Plot (p1, p2, c) -> interp_draw_line h t0 c p1 p2
| Draw_rect (p1, p2, c) ->
  let Pair (x, y) = p1 in
  let Pair (z0, w) = p2 in
  let t1 = interp_draw_line h t0 c (Pair (x, y)) (Pair (x, w)) in
  let t2 = interp_draw_line h t1 c (Pair (x, y)) (Pair (z0, y)) in
  let t3 = interp_draw_line h t2 c (Pair (x, w)) (Pair (z0, w)) in interp_draw_line h t3 c (Pair (z0, w)) (Pair (z0, y))
| Seq (g1, _) -> let st = interp h t0 g1 in interp h st g1

(** val prog1 : g_com **)

let prog1 =
  Draw_rect ((Pair (XH, (XO XH))), (Pair ((XI XH), (XO (XO XH)))), Red)

type oGState = unit

(** val ocaml_graphics_init : unit0 -> oGState **)

let ocaml_graphics_init = (fun _ -> Graphics.open_graph ())

(** val ocaml_update_state : oGState -> point -> oGState **)

let ocaml_update_state s _ =
  s

(** val ocaml_draw_pixel : oGState -> point -> color -> oGState **)

let ocaml_draw_pixel = (fun _ p c -> 
     let rec int_of_pos p = 
       (match p with 
         | XH -> 1
         | XO p' -> 2 * int_of_pos p'
         | XI p' -> (2 * int_of_pos p') + 1)
     in 
     Graphics.set_color c;
     Graphics.plot "" (int_of_pos p))

(** val oGState_graphics_prims : oGState graphics_prims **)

let oGState_graphics_prims =
  { init_state = ocaml_graphics_init; update_state = ocaml_update_state; draw_pixel = ocaml_draw_pixel }

(** val t : oGState **)

let t =
  interp oGState_graphics_prims (oGState_graphics_prims.init_state Tt) prog1
