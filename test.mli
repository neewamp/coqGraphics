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

val compOpp : comparison -> comparison

val add : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool
 end

type q = { qnum : z; qden : positive }

val qnum : q -> z

val qden : q -> positive

val qle_bool : q -> q -> bool

val qplus : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

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

val init_state : 'a1 graphics_prims -> unit0 -> 'a1

val update_state : 'a1 graphics_prims -> 'a1 -> point -> 'a1

val draw_pixel : 'a1 graphics_prims -> 'a1 -> point -> color -> 'a1

val pos_to_nat : positive -> nat

val nat_to_pos : nat -> positive

val draw_line_rc : 'a1 graphics_prims -> 'a1 -> point -> color -> nat -> q -> q -> 'a1

val interp_draw_line : 'a1 graphics_prims -> 'a1 -> color -> point -> point -> 'a1

val interp : 'a1 graphics_prims -> 'a1 -> g_com -> 'a1

val prog1 : g_com

type oGState = unit

val ocaml_graphics_init : unit0 -> oGState

val ocaml_update_state : oGState -> point -> oGState

val ocaml_draw_pixel : oGState -> point -> color -> oGState

val oGState_graphics_prims : oGState graphics_prims

val t : oGState
