type bool =
| True
| False

type nat =
| O
| S of nat

val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val add : nat -> nat -> nat

val sub : nat -> nat -> nat

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

  val mul : positive -> positive -> positive

  val square : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val leb : positive -> positive -> bool

  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive*mask)
    -> positive*mask

  val sqrtrem : positive -> positive*mask

  val sqrt : positive -> positive

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val square : z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val to_nat : z -> nat

  val of_nat : nat -> z

  val pos_div_eucl : positive -> z -> z*z

  val div_eucl : z -> z -> z*z

  val div : z -> z -> z

  val sqrt : z -> z
 end

type rgb = (z*z)*z

val fromRGB : rgb -> z

type color = z

val red : z

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

val init_state : 'a1 graphics_prims -> unit -> 'a1

val update_state : 'a1 graphics_prims -> 'a1 -> point -> 'a1

val draw_pixel : 'a1 graphics_prims -> 'a1 -> point -> color -> 'a1

val distance : point -> point -> z

val interpolate :
  'a1 graphics_prims -> 'a1 -> nat -> point -> point -> point -> z ->
  color -> 'a1

val draw_vline :
  'a1 graphics_prims -> 'a1 -> point -> color -> nat -> 'a1

val draw_hline :
  'a1 graphics_prims -> 'a1 -> point -> color -> nat -> 'a1

val fill_rect_rc :
  'a1 graphics_prims -> 'a1 -> point -> nat -> nat -> color -> 'a1

val interp_draw_line :
  'a1 graphics_prims -> 'a1 -> color -> point -> point -> 'a1

val interp : 'a1 graphics_prims -> 'a1 -> g_com -> 'a1

type oGState = unit

val ocaml_graphics_init : unit -> oGState

val ocaml_update_state : oGState -> point -> oGState

val ocaml_draw_pixel : oGState -> point -> color -> oGState

val oGState_graphics_prims : oGState graphics_prims

val prog : g_com

val t : oGState
