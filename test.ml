type bool =
| True
| False

type nat =
| O
| S of nat

(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,_ -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| _,y -> y

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)
 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
let add = Coq__1.add


(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k ->
    (match m with
     | O -> n
     | S l -> sub k l)

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
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
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
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
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
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val square : positive -> positive **)

  let rec square = function
  | XI p0 -> XI (XO (add (square p0) p0))
  | XO p0 -> XO (XO (square p0))
  | XH -> XH

  (** val compare_cont :
      comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val leb : positive -> positive -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) ->
      (positive*mask) -> positive*mask **)

  let sqrtrem_step f g = function
  | s,y ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       (match leb s' r' with
        | True -> (XI s),(sub_mask r' s')
        | False -> (XO s),(IsPos r'))
     | _ -> (XO s),(sub_mask (g (f XH)) (XO (XO XH))))

  (** val sqrtrem : positive -> positive*mask **)

  let rec sqrtrem = function
  | XI p0 ->
    (match p0 with
     | XI p1 ->
       sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p1)
     | XO p1 ->
       sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p1)
     | XH -> XH,(IsPos (XO XH)))
  | XO p0 ->
    (match p0 with
     | XI p1 ->
       sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p1)
     | XO p1 ->
       sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p1)
     | XH -> XH,(IsPos XH))
  | XH -> XH,IsNul

  (** val sqrt : positive -> positive **)

  let sqrt p =
    fst (sqrtrem p)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
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
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Coq_Pos.pred_double q)
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

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

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

  (** val square : z -> z **)

  let square = function
  | Z0 -> Z0
  | Zpos p -> Zpos (Coq_Pos.square p)
  | Zneg p -> Zpos (Coq_Pos.square p)

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

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> O

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Coq_Pos.of_succ_nat n0)

  (** val pos_div_eucl : positive -> z -> z*z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let q,r = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      (match ltb r' b with
       | True -> (mul (Zpos (XO XH)) q),r'
       | False -> (add (mul (Zpos (XO XH)) q) (Zpos XH)),(sub r' b))
    | XO a' ->
      let q,r = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      (match ltb r' b with
       | True -> (mul (Zpos (XO XH)) q),r'
       | False -> (add (mul (Zpos (XO XH)) q) (Zpos XH)),(sub r' b))
    | XH ->
      (match leb (Zpos (XO XH)) b with
       | True -> Z0,(Zpos XH)
       | False -> (Zpos XH),Z0)

  (** val div_eucl : z -> z -> z*z **)

  let div_eucl a b =
    match a with
    | Z0 -> Z0,Z0
    | Zpos a' ->
      (match b with
       | Z0 -> Z0,Z0
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let q,r = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> (opp q),Z0
          | _ -> (opp (add q (Zpos XH))),(add b r)))
    | Zneg a' ->
      (match b with
       | Z0 -> Z0,Z0
       | Zpos _ ->
         let q,r = pos_div_eucl a' b in
         (match r with
          | Z0 -> (opp q),Z0
          | _ -> (opp (add q (Zpos XH))),(sub b r))
       | Zneg b' -> let q,r = pos_div_eucl a' (Zpos b') in q,(opp r))

  (** val div : z -> z -> z **)

  let div a b =
    let q,_ = div_eucl a b in q

  (** val sqrt : z -> z **)

  let sqrt = function
  | Zpos p -> Zpos (Coq_Pos.sqrt p)
  | _ -> Z0
 end

type rgb = (z*z)*z

(** val fromRGB : rgb -> z **)

let fromRGB = function
| p,b ->
  let r,g = p in
  Z.add
    (Z.add r
      (Z.mul g (Zpos (XO (XO (XO (XO (XO (XO (XO (XO XH)))))))))))
    (Z.mul b (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
      (XO (XO (XO XH))))))))))))))))))

type color = z

(** val red : z **)

let red =
  fromRGB ((Z0,Z0),(Zpos (XI (XI (XI (XI (XI (XI (XI XH)))))))))

type point = z*z

type g_com =
| Draw_pix of point * color
| Open_graph of point
| Resize_window of point
| Lineto of point * point * color
| Draw_rect of point * point * color
| Fill_rect of point * point * color
| Seq of g_com * g_com

type 't graphics_prims = { init_state : (unit -> 't);
                           update_state : ('t -> point -> 't);
                           draw_pixel : ('t -> point -> color -> 't) }

(** val init_state : 'a1 graphics_prims -> unit -> 'a1 **)

let init_state x = x.init_state

(** val update_state : 'a1 graphics_prims -> 'a1 -> point -> 'a1 **)

let update_state x = x.update_state

(** val draw_pixel :
    'a1 graphics_prims -> 'a1 -> point -> color -> 'a1 **)

let draw_pixel x = x.draw_pixel

(** val distance : point -> point -> z **)

let distance p1 p2 =
  let dx = Z.sub (fst p2) (fst p1) in
  let dy = Z.sub (snd p2) (snd p1) in
  Z.sqrt (Z.add (Z.square dx) (Z.square dy))

(** val interpolate :
    'a1 graphics_prims -> 'a1 -> nat -> point -> point -> point -> z ->
    color -> 'a1 **)

let rec interpolate h t0 i p1 p2 v num_points c =
  match i with
  | O -> h.draw_pixel t0 p1 c
  | S i' ->
    (match i' with
     | O -> h.draw_pixel t0 p1 c
     | S _ ->
       let p1' =
         (Z.add (fst p1)
           (Z.div (Z.mul (fst v) (Z.of_nat i)) num_points)),(Z.add
                                                              (snd p1)
                                                              (Z.div
                                                              (Z.mul
                                                              (snd v)
                                                              (Z.of_nat
                                                              i))
                                                              num_points))
       in
       h.draw_pixel (interpolate h t0 i' p1 p2 v num_points c) p1' c)

(** val draw_vline :
    'a1 graphics_prims -> 'a1 -> point -> color -> nat -> 'a1 **)

let rec draw_vline h t0 p c = function
| O -> t0
| S h' ->
  let x,y = p in
  h.draw_pixel (draw_vline h t0 p c h') (x,(Z.add y (Z.of_nat h'))) c

(** val draw_hline :
    'a1 graphics_prims -> 'a1 -> point -> color -> nat -> 'a1 **)

let rec draw_hline h t0 p c = function
| O -> t0
| S w' ->
  let x,y = p in
  h.draw_pixel (draw_hline h t0 p c w') ((Z.add x (Z.of_nat w')),y) c

(** val fill_rect_rc :
    'a1 graphics_prims -> 'a1 -> point -> nat -> nat -> color -> 'a1 **)

let rec fill_rect_rc h t0 p w h0 c =
  match h0 with
  | O -> t0
  | S h' ->
    let x,y = p in
    draw_hline h (fill_rect_rc h t0 p w h' c)
      (x,(Z.add y (Z.of_nat h'))) c w

(** val interp_draw_line :
    'a1 graphics_prims -> 'a1 -> color -> point -> point -> 'a1 **)

let interp_draw_line h t0 c p1 p2 =
  interpolate h t0 (sub (Z.to_nat (distance p1 p2)) (S O)) p1 p2
    ((Z.sub (fst p2) (fst p1)),(Z.sub (snd p2) (snd p1)))
    (distance p1 p2) c

(** val interp : 'a1 graphics_prims -> 'a1 -> g_com -> 'a1 **)

let rec interp h t0 = function
| Draw_pix (p, c) -> h.draw_pixel t0 p c
| Open_graph s_size -> h.update_state t0 s_size
| Resize_window s_size -> h.update_state t0 s_size
| Lineto (p1, p2, c) ->
  let st = interp_draw_line h t0 c p1 p2 in
  let st' = h.draw_pixel st p1 c in h.draw_pixel st' p2 c
| Draw_rect (p, p0, c) ->
  let x,y = p in
  let w,h0 = p0 in
  let w' = Z.to_nat w in
  let h' = Z.to_nat h0 in
  let t1 = draw_hline h t0 (x,y) c w' in
  let t2 = draw_hline h t1 (x,(Z.add y h0)) c w' in
  let t3 = draw_vline h t2 (x,y) c h' in
  draw_vline h t3 ((Z.add x w),y) c h'
| Fill_rect (p, p0, c) ->
  let w,h0 = p0 in fill_rect_rc h t0 p (Z.to_nat w) (Z.to_nat h0) c
| Seq (g1, g2) -> let st = interp h t0 g1 in interp h st g2

type oGState = unit

(** val ocaml_graphics_init : unit -> oGState **)

let ocaml_graphics_init = (fun _ -> Graphics.open_graph " 1920x1080")

(** val ocaml_update_state : oGState -> point -> oGState **)

let ocaml_update_state s _ =
  s

(** val ocaml_draw_pixel : oGState -> point -> color -> oGState **)

let ocaml_draw_pixel =   (fun _ (p : point) c ->     let rec int_of_z po =   (match po with    |Z0 -> 0    |Zpos p'' ->      (match p'' with       | XH -> 1       | XO p' -> 2 * int_of_z (Zpos p')       | XI p' -> (2 * int_of_z (Zpos p')) + 1)    |Zneg p'' ->      (match p'' with       | XH -> -1       | XO p' -> 2 * int_of_z (Zneg p')       | XI p' -> (2 * int_of_z (Zneg p')) + 1))       in   Graphics.plot (int_of_z (fst p)) (int_of_z (snd p)); Graphics.set_color (int_of_z c));; 

(** val oGState_graphics_prims : oGState graphics_prims **)

let oGState_graphics_prims =
  { init_state = ocaml_graphics_init; update_state =
    ocaml_update_state; draw_pixel = ocaml_draw_pixel }

(** val prog : g_com **)

let prog =
  Lineto (((Zpos (XO (XO (XI (XO (XO (XI XH))))))),(Zpos (XO (XO (XO
    (XI (XO (XO (XI XH))))))))), ((Zpos (XO (XO (XI (XO (XO (XI (XO (XI
    (XO (XI XH))))))))))),(Zpos (XO (XO (XI (XO (XO (XO (XO (XI (XI
    XH))))))))))), red)

(** val t : oGState **)

let t =
  interp oGState_graphics_prims (oGState_graphics_prims.init_state ())
    prog
;;read_line();;
