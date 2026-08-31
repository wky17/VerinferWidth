open Extraction
open Hifirrtl_lang
open Useocamlscc
open Printf
open Transhiast
open Mlir_lang
open List
open Extraction.Env
open Extraction.HiEnv
open Extraction.HiFirrtl
open Extraction.Constraints 
open Extraction.Extract_cswithmin
open Extraction.InferWidths_multimod
(** val pl2btyp : hfport list -> ffield **)

let rec pl2btyp = function
| [] -> Fnil
| h :: tl ->
  (match h with
   | Finput (v, t0) -> Fflips (((Obj.magic v) : int), Nflip, t0, (pl2btyp tl))
   | Foutput (v, t0) -> Fflips (((Obj.magic v) : int), Flipped, t0, (pl2btyp tl)))

(** val add_pairs :
    'a1 -> 'a2 list -> ('a1 * 'a2) list -> ('a1 * 'a2) list **)

let rec add_pairs x ys acc =
  match ys with
  | [] -> acc
  | y :: ys' -> add_pairs x ys' ((x, y) :: acc)

(** val cartesian_tail :
    'a1 list -> 'a2 list -> ('a1 * 'a2) list -> ('a1 * 'a2) list **)

let rec cartesian_tail xs ys acc =
  match xs with
  | [] -> rev acc
  | x :: xs' -> cartesian_tail xs' ys (add_pairs x ys acc)

(** val cartesian : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let cartesian xs ys =
  cartesian_tail xs ys []

module H = struct
  type 'v t = (int, 'v) Hashtbl.t
  let empty () = Hashtbl.create 1000
  let find k tbl = Hashtbl.find_opt tbl k
  let add k v tbl = Hashtbl.replace tbl k v
end

module H_triple = struct
  type 'v t = (int * (int * int), 'v) Hashtbl.t
  let empty () = Hashtbl.create 1000
  let find k tbl = Hashtbl.find_opt tbl k
  let add k v tbl = Hashtbl.replace tbl k v
end

(** val type_of_ref : href -> (ftype * forient) H.t -> ftype option **)

let rec type_of_ref r tmap =
  match r with
  | Eid v ->
    (match H.find ((Obj.magic v) : int) tmap with
     | Some p -> let (ft, _) = p in Some ft
     | None -> None)
  | Esubfield (r0, v) ->
    (match type_of_ref r0 tmap with
     | Some f ->
       (match f with
        | Btyp fs ->
          let rec aux = function
          | Fnil -> None
          | Fflips (v', _, t0, fxs) ->
            if (Obj.magic v : int) = (Obj.magic v' : int)
            then Some t0
            else aux fxs
          in aux fs
        | _ -> None)
     | None -> None)
  | Esubindex (r0, _) ->
    (match type_of_ref r0 tmap with
     | Some f -> (match f with
                  | Atyp (ty, _) -> Some ty
                  | _ -> None)
     | None -> None)
  | Esubaccess (r0, _) ->
    (match type_of_ref r0 tmap with
     | Some f -> (match f with
                  | Atyp (ty, _) -> Some ty
                  | _ -> None)
     | None -> None)

(** val fgtyp_mux :
    fgtyp_explicit -> fgtyp_explicit -> fgtyp_explicit option **)

let fgtyp_mux x y =
  match x with
  | Fuint wx ->
    (match y with
     | Fuint wy -> Some (Fuint (max wx wy))
     | _ -> None)
  | Fsint wx ->
    (match y with
     | Fsint wy -> Some (Fsint (max wx wy))
     | _ -> None)
  | Fclock -> (match y with
               | Fclock -> Some Fclock
               | _ -> None)
  | Fasyncreset -> (match y with
                    | Fasyncreset -> Some Fasyncreset
                    | _ -> None)
  | _ -> None

(** val ftype_mux' : ftype -> ftype -> ftype_explicit option **)

let rec ftype_mux' x y =
  match x with
  | Gtyp tx ->
    (match y with
     | Gtyp ty ->
       (match fgtyp_mux tx ty with
        | Some f -> Some (Gtyp f)
        | None -> None)
     | _ -> None)
  | Atyp (tx, nx) ->
    (match y with
     | Atyp (ty, ny) ->
       if nx = ny   (* 去掉 Obj.magic *)
       then (match ftype_mux' tx ty with
             | Some f -> Some (Atyp (f, nx))
             | None -> None)
       else None
     | _ -> None)
  | Btyp fx ->
    (match y with
     | Btyp fy ->
       (match ffield_mux' fx fy with
        | Some f -> Some (Btyp f)
        | None -> None)
     | _ -> None)

(** val ffield_mux' : ffield -> ffield -> ffield_explicit option **)
and ffield_mux' f1 f2 =
  match f1 with
  | Fnil -> (match f2 with
             | Fnil -> Some Fnil
             | Fflips (_, _, _, _) -> None)
  | Fflips (v1, f, t1, fs1) ->
    (match f with
     | Flipped -> None
     | Nflip ->
       (match f2 with
        | Fnil -> None
        | Fflips (v2, f0, t2, fs2) ->
          (match f0 with
           | Flipped -> None
           | Nflip ->
             if v1 = v2   (* 去掉 Obj.magic *)
             then (match ftype_mux' t1 t2 with
                   | Some f3 ->
                     (match ffield_mux' fs1 fs2 with
                      | Some f4 -> Some (Fflips (v1, Nflip, f3, f4))
                      | None -> None)
                   | None -> None)
             else None)))
  | _ -> None

(** val ftype_mux :
    ftype_explicit -> ftype_explicit -> ftype_explicit option **)

let ftype_mux = ftype_mux'

(** val type_of_hfexpr :
    hfexpr -> (ftype * forient) H.t -> ftype_explicit option **)

let rec type_of_hfexpr e tmap =
  match e with
  | Econst (t0, bs) ->
    (match t0 with
     | Fuint_implicit _ -> Some (Gtyp (Fuint (Stdlib.List.length bs)))
     | Fsint_implicit _ -> Some (Gtyp (Fsint (Stdlib.List.length bs)))
     | x -> Some (Gtyp x))
  | Ecast (u, e1) ->
    (match u with
     | AsUInt ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w -> Some (Gtyp (Fuint w))
              | Fsint w -> Some (Gtyp (Fuint w))
              | Fuint_implicit _ -> None
              | Fsint_implicit _ -> None
              | _ -> Some (Gtyp (Fuint 1)))
           | _ -> None)
        | None -> None)
     | AsSInt ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w -> Some (Gtyp (Fsint w))
              | Fsint w -> Some (Gtyp (Fsint w))
              | Fuint_implicit _ -> None
              | Fsint_implicit _ -> None
              | _ -> Some (Gtyp (Fsint 1)))
           | _ -> None)
        | None -> None)
     | AsClock ->
       (match type_of_hfexpr e1 tmap with
        | Some f -> (match f with
                     | Gtyp _ -> Some (Gtyp Fclock)
                     | _ -> None)
        | None -> None)
     | AsAsync ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp _ -> Some (Gtyp Fasyncreset)
           | _ -> None)
        | None -> None))
  | Eprim_unop (e0, e1) ->
    (match e0 with
     | Upad n ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w -> Some (Gtyp (Fuint (max w n)))
              | Fsint w -> Some (Gtyp (Fsint (max w n)))
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Ushl n ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w -> Some (Gtyp (Fuint (w + n)))
              | Fsint w -> Some (Gtyp (Fsint (w + n)))
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Ushr n ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w -> Some (Gtyp (Fuint (max (w - n) 0)))
              | Fsint w ->
                Some (Gtyp (Fsint (max (w - n) 1)))
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Ucvt ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w -> Some (Gtyp (Fsint (w + 1)))
              | Fsint w -> Some (Gtyp (Fsint w))
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Uneg ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w -> Some (Gtyp (Fsint (w + 1)))
              | Fsint w -> Some (Gtyp (Fsint (w + 1)))
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Unot ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w -> Some (Gtyp (Fuint w))
              | Fsint w -> Some (Gtyp (Fuint w))
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Uextr (n1, n2) ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ -> Some (Gtyp (Fuint (n1 - n2 + 1)))
              | Fsint _ -> Some (Gtyp (Fuint (n1 - n2 + 1)))
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Uhead n ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ -> Some (Gtyp (Fuint n))
              | Fsint _ -> Some (Gtyp (Fuint n))
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Utail n ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w -> Some (Gtyp (Fuint (w - n)))
              | Fsint w -> Some (Gtyp (Fuint (w - n)))
              | _ -> None)
           | _ -> None)
        | None -> None)
     | _ ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ -> Some (Gtyp (Fuint 1))
              | Fsint _ -> Some (Gtyp (Fuint 1))
              | _ -> None)
           | _ -> None)
        | None -> None))
  | Eprim_binop (e0, e1, e2) ->
    (match e0 with
     | Badd ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint w2 ->
                         Some (Gtyp (Fuint ((max w1 w2) + 1)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint w2 ->
                         Some (Gtyp (Fsint ((max w1 w2) + 1)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bsub ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint w2 ->
                         Some (Gtyp (Fuint ((max w1 w2) + 1)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint w2 ->
                         Some (Gtyp (Fsint ((max w1 w2) + 1)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bmul ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint w2 -> Some (Gtyp (Fuint (w1 + w2)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint w2 -> Some (Gtyp (Fsint (w1 + w2)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bdiv ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ -> Some (Gtyp (Fuint w1))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint _ ->
                         Some (Gtyp (Fsint (w1 + 1)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Brem ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint w2 -> Some (Gtyp (Fuint (min w1 w2)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint w2 -> Some (Gtyp (Fsint (min w1 w2)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bcomp _ ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ -> Some (Gtyp (Fuint 1))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint _ ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint _ -> Some (Gtyp (Fuint 1))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bdshl ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint w2 ->
                         Some (Gtyp (Fuint (((1 lsl w2) + w1) - 1)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint w2 ->
                         Some (Gtyp (Fsint (((1 lsl w2) + w1) - 1)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bdshr ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ -> Some (Gtyp (Fuint w1))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ -> Some (Gtyp (Fsint w1))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bcat ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint w2 -> Some (Gtyp (Fuint (w1 + w2)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint w2 -> Some (Gtyp (Fuint (w1 + w2)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | _ ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint w2 -> Some (Gtyp (Fuint (max w1 w2)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint w2 -> Some (Gtyp (Fuint (max w1 w2)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None))
  | Emux (c, e1, e2) ->
    (match type_of_hfexpr c tmap with
     | Some f ->
       (match f with
        | Gtyp f1 ->
          (match f1 with
           | Fuint _ ->
             (match type_of_hfexpr e1 tmap with
              | Some t1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some t2 -> ftype_mux t1 t2
                 | None -> None)
              | None -> None)
           | _ -> None)
        | _ -> None)
     | None -> None)
  | Eref r ->
    (match type_of_ref r tmap with
     | Some ft -> Some (make_ftype_explicit ft)
     | None -> None)

(** val stmts_tmap : ... -> ... option **)
let rec stmts_tmap (modplmap : hfport list H.t) tmap = function
| Qnil -> Some tmap
| Qcons (s, ss') ->
  match stmt_tmap modplmap tmap s with
  | Some tmap' -> stmts_tmap modplmap tmap' ss'
  | None -> None

and stmt_tmap (modplmap : hfport list H.t) tmap = function
| Swire (v, t0) ->
  (match H.find ((Obj.magic v) : int) tmap with
   | Some _ -> None
   | None -> H.add ((Obj.magic v) : int) (t0, Duplex) tmap; Some tmap)
| Sreg (v, reg) ->
  (match H.find ((Obj.magic v) : int) tmap with
   | Some _ -> None
   | None ->
     match type_of_hfexpr reg.clock tmap with
     | Some _ -> H.add ((Obj.magic v) : int) (reg.coq_type, Duplex) tmap; Some tmap
     | None -> None)
| Smem (v, m) -> H.add ((Obj.magic v) : int) (m.data_type, Duplex) tmap; Some tmap
| Sinst (v, mv) ->
  (match H.find ((Obj.magic mv) : int) modplmap with
   | Some pl ->
     let t0 = Btyp (pl2btyp pl) in
     H.add ((Obj.magic v) : int) (t0, Duplex) tmap; Some tmap
   | None -> None)
| Snode (v, expr) ->
  (match H.find ((Obj.magic v) : int) tmap with
   | Some _ -> None
   | None ->
     match type_of_hfexpr expr tmap with
     | Some f -> H.add ((Obj.magic v) : int) ((make_ftype_implicit f), Source) tmap; Some tmap
     | None -> None)
| Swhen (cond, ss_true, ss_false) ->
  (match type_of_hfexpr cond tmap with
   | Some f ->
     (match f with
      | Gtyp f1 ->
        (match f1 with
         | Fuint n ->
           let rec aux n tmap =
             if n = 0 then None
             else
               match stmts_tmap modplmap tmap ss_true with
               | Some tmap_true -> stmts_tmap modplmap tmap_true ss_false
               | None -> aux (n-1) tmap
           in aux n tmap
         | _ -> None)
      | _ -> None)
   | None -> None)
| _ -> Some tmap

(** val ports_tmap :
    (ftype * forient) H.t -> hfport list -> (ftype * forient) H.t option **)
let rec ports_tmap tmap = function
| [] -> Some tmap
| h :: pp' ->
  match h with
  | Finput (v, t0) ->
    (match H.find ((Obj.magic v) : int) tmap with
     | Some _ -> None
     | None -> H.add ((Obj.magic v) : int) (t0, Source) tmap; ports_tmap tmap pp')
  | Foutput (v, t0) ->
    (match H.find ((Obj.magic v) : int) tmap with
     | Some _ -> None
     | None -> H.add ((Obj.magic v) : int) (t0, Duplex) tmap; ports_tmap tmap pp')

let rec modules_tmap (modplmap : hfport list H.t) tmap = function
| [] -> Some tmap
| h :: tl ->
  match h with
  | FInmod (mv, ps, ss) ->
    (match ports_tmap (H.empty ()) ps with
     | Some pmap ->
       (match stmts_tmap modplmap pmap ss with
        | Some tmap' ->
            H.add ((Obj.magic mv) : int) tmap' tmap;
            modules_tmap modplmap tmap tl
        | None -> None)
     | None -> None)
  | FExmod (_, _, _) -> modules_tmap modplmap tmap tl

let circuit_tmap = function
| Fcircuit (_, ml) ->
  let modplmap =
    Stdlib.List.fold_left (fun acc m ->
      match m with
      | FInmod (mv, ps, _) -> H.add ((Obj.magic mv) : int) ps acc; acc
      | FExmod (mv, ps, _) -> H.add ((Obj.magic mv) : int) ps acc; acc) (H.empty ()) ml
  in
  modules_tmap modplmap (H.empty ()) ml

(** val terms_value : int H_triple.t -> (int * (int * (int * int))) list -> Z.t -> Z.t **)
let terms_value (v : int H_triple.t) (terms0 : (int * (int * (int * int))) list) (init : Z.t) : Z.t =
  List.fold_left (fun acc (coeff, var) ->
    let vi = match H_triple.find var v with
             | Some val0 -> val0
             | None -> 0 in
    Z.add acc (Z.of_int (coeff * vi))) terms0 init

(** val power_value : int H_triple.t -> (int * (int * (int * int))) list -> Z.t **)
let power_value (v : int H_triple.t) (terms0 : (int * (int * (int * int))) list) : Z.t =
  match terms0 with
  | [] -> Z.zero
  | _ :: _ ->
      let n = terms_value v terms0 Z.zero in
      Z.pow (Z.of_int 2) (Z.to_int n)   (* n 是 Z.t，转换为 int *)

(** val min_rhs_value : int H_triple.t -> min_rhs -> Z.t **)
let rec min_rhs_value v = function
| Expr r ->
    Z.add (terms_value v r.regular_terms (Z.of_int r.regular_const))
          (power_value v r.regular_power)
| Min (e1, e2) -> Z.min (min_rhs_value v e1) (min_rhs_value v e2)

(** val add_cs1_2_c1map :
    coq_Constraint1 list -> int H_triple.t -> int H_triple.t **)

let rec add_cs1_2_c1map cs c1map =
  match cs with
  | [] -> c1map
  | hd :: tl ->
      (* 原地修改：根据是否存在键，更新映射 *)
      (match H_triple.find hd.lhs_var1 c1map with
       | Some cs1 -> H_triple.add hd.lhs_var1 (hd :: cs1) c1map
       | None -> H_triple.add hd.lhs_var1 [hd] c1map);
      add_cs1_2_c1map tl c1map   (* 继续使用同一个哈希表 *)

(** val rhs_value1 : int H_triple.t -> coq_Constraint1 -> Z.t **)

let rhs_value1 v c =
  Z.add (terms_value v c.rhs_terms1 (Z.of_int c.rhs_const1)) (power_value v c.rhs_power)

(** val satisfies_constraint1 : int H_triple.t -> coq_Constraint1 -> bool **)

let satisfies_constraint1 v c =
  match H_triple.find c.lhs_var1 v with
  | Some val0 -> Z.leq (rhs_value1 v c) (Z.of_int val0)
  | None -> false

type coq_Constraint2 = { lhs_const2 : int; rhs_terms2 : (int * (int * (int * int))) list }

(** val satisfies_constraint2 : int H_triple.t -> coq_Constraint2 -> bool **)

let satisfies_constraint2 v c =
  let total =
    Stdlib.List.fold_left (fun acc (bi, xi) ->
      let vi = match H_triple.find xi v with
               | Some val0 -> val0
               | None -> 0 in
      acc + (bi * vi)) 0 c.rhs_terms2
  in
  total <= c.lhs_const2

(** val rhs_vars : coq_Constraint1 -> (int * (int * int)) list **)

let rhs_vars c =
  Stdlib.List.rev_append (List.map snd c.rhs_power) (List.map snd c.rhs_terms1)

(** val remove_power1 : int H_triple.t -> coq_Constraint1 -> coq_Constraint1 **)

let remove_power1 value c =
  { lhs_var1 = c.lhs_var1;
    rhs_const1 = c.rhs_const1 + (Z.to_int (power_value value c.rhs_power));
    rhs_terms1 = c.rhs_terms1;
    rhs_power = [] }

(** val remove_power_regular : int H_triple.t -> regular_rhs -> regular_rhs **)

let remove_power_regular value r =
  { regular_const = r.regular_const + (Z.to_int (power_value value r.regular_power));
    regular_terms = r.regular_terms;
    regular_power = [] }

(** val remove_power_min_rhs : int H_triple.t -> min_rhs -> min_rhs **)

let rec remove_power_min_rhs value = function
| Expr r -> Expr (remove_power_regular value r)
| Min (min1, min2) ->
    Min (remove_power_min_rhs value min1, remove_power_min_rhs value min2)

(** val remove_power_min :
    int H_triple.t -> coq_Constraint_Min -> coq_Constraint_Min **)

let remove_power_min value c =
  { lhs_var_min = c.lhs_var_min;
    rhs_expr_min = remove_power_min_rhs value c.rhs_expr_min }

(** val find_ref_inside : int -> href -> href option **)
let rec find_ref_inside instv = function
| Eid _ -> None
| Esubfield (ref, v) ->
  (match ref with
   | Eid _ -> Some (Eid v)
   | _ ->
     (match find_ref_inside instv ref with
      | Some subref -> Some (Esubfield (subref, v))
      | None -> None))
| Esubindex (ref, n) ->
  (match find_ref_inside instv ref with
   | Some subref -> Some (Esubindex (subref, n))
   | None -> None)
| Esubaccess (ref, e) ->
  (match find_ref_inside instv ref with
   | Some subref -> Some (Esubaccess (subref, e))
   | None -> None)

(** val offset_of_subfield_b :
    ffield -> Equality.sort -> int -> int option **)

let rec offset_of_subfield_b ft fid n =
  match ft with
  | Fnil -> None
  | Fflips (v, _, t0, fs) ->
    if fid = ((Obj.magic v) : int)
    then Some n
    else offset_of_subfield_b fs fid (n + (size_of_ftype t0))


(** val offset_ref : href -> (ftype * forient) H.t -> int option **)

let rec offset_ref r tmap =
  match r with
  | Eid _ -> Some 0
  | Esubfield (v, f) ->
    (match offset_ref v tmap with
     | Some n ->
       (match type_of_ref v tmap with
        | Some f0 ->
          (match f0 with
           | Btyp ft -> offset_of_subfield_b ft ((Obj.magic f) : int) n
           | _ -> None)
        | None -> None)
     | None -> None)
  | Esubindex (v, _) -> offset_ref v tmap
  | Esubaccess (v, _) -> offset_ref v tmap

(** val base_id : href -> var **)

let rec base_id = function
| Eid v -> v
| Esubfield (v, _) -> base_id v
| Esubindex (v, _) -> base_id v
| Esubaccess (v, _) -> base_id v

(** val ref2pv : href -> (ftype * forient) H.t -> ProdVar.t option **)

let ref2pv r tmap =
  let base_v = base_id r in
  (match offset_ref r tmap with
   | Some os -> Some (((Obj.magic base_v) : int), os)   (* N.of_nat -> N.of_int *)
   | None -> None)

(** val ref2pv_mod :
    href -> int -> int H.t -> (ftype * forient) H.t H.t -> (int * (int * int)) option **)
let ref2pv_mod r mv instmap tmap =
  let base_ref = base_id r in
  (match H.find ((Obj.magic base_ref) : int) instmap with
   | Some inst_mv ->
     (match find_ref_inside base_ref r with
      | Some inst_ref ->
        (match H.find inst_mv tmap with
         | Some inst_tmap ->
           (match ref2pv inst_ref inst_tmap with
            | Some pv -> Some (inst_mv, pv)
            | None -> None)
         | None -> None)
      | None -> None)
   | None ->
     (match H.find mv tmap with
      | Some mod_tmap ->
        (match ref2pv r mod_tmap with
         | Some pv -> Some (mv, pv)
         | None -> None)
      | None -> None))

(** val extract_constraint_expr_mod :
    int -> hfexpr -> (ftype * forient) H.t -> (ftype * forient) H.t H.t
    -> int H.t -> (min_rhs list * min_rhs list) option **)
let rec extract_constraint_expr_mod (mv : int) (e : hfexpr) 
    (mod_tmap : (ftype * forient) H.t) 
    (tmap : (ftype * forient) H.t H.t) 
    (instmap : int H.t) : (min_rhs list * min_rhs list) option = 
  match e with
  | Econst (t0, bs) ->
    (match t0 with
     | Fuint_implicit _ ->
       Some (((Expr (make_rhs [] [] ((Stdlib.List.length bs)))) :: []), [])
     | Fsint_implicit _ ->
       Some (((Expr (make_rhs [] [] ((Stdlib.List.length bs)))) :: []), [])
     | _ ->
       Some (((Expr (make_rhs [] [] ((sizeof_fgtyp t0)))) :: []), []))
  | Ecast (u, e1) ->
    (match u with
     | AsUInt ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp _ -> extract_constraint_expr_mod mv e1 mod_tmap tmap instmap
           | _ -> None)
        | None -> None)
     | AsSInt ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp _ -> extract_constraint_expr_mod mv e1 mod_tmap tmap instmap
           | _ -> None)
        | None -> None)
     | _ ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp _ ->
             (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
              | Some p ->
                let (_, cs) = p in
                Some (((Expr (make_rhs [] [] 1)) :: []), cs)
              | None -> None)
           | _ -> None)
        | None -> None))
  | Eprim_unop (e0, e1) ->
    (match e0 with
     | Upad n ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (el, cs) = p in
                   Some (((Expr (make_rhs [] [] n)) :: el), cs)
                 | None -> None)
              | Fsint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (el, cs) = p in
                   Some (((Expr (make_rhs [] [] n)) :: el), cs)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Ushl n ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (el, cs) = p in
                   Some
                   ((Stdlib.List.map (fun temp_e -> min_rhs_add_cst temp_e n)
                      el), cs)
                 | None -> None)
              | Fsint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (el, cs) = p in
                   Some
                   ((Stdlib.List.map (fun temp_e -> min_rhs_add_cst temp_e n)
                      el), cs)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Ushr n ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (el, cs) = p in
                   Some
                   ((Stdlib.List.map (fun temp_e ->
                      min_rhs_add_cst temp_e (- n)) el), cs)
                 | None -> None)
              | Fsint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (el, cs) = p in
                   let nexp =
                    Stdlib.List.map (fun temp_e ->
                       min_rhs_add_cst temp_e (-n)) el
                   in
                   Some (((Expr (make_rhs [] [] 1)) :: nexp), cs)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Ucvt ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (el, cs) = p in
                   Some ((Stdlib.List.map (fun temp_e -> min_rhs_add_cst temp_e 1) el),
                   cs)
                 | None -> None)
              | Fsint _ ->
                extract_constraint_expr_mod mv e1 mod_tmap tmap instmap
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Uneg ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (el, cs) = p in
                   Some ((Stdlib.List.map (fun temp_e -> min_rhs_add_cst temp_e 1) el),
                   cs)
                 | None -> None)
              | Fsint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (el, cs) = p in
                   Some ((Stdlib.List.map (fun temp_e -> min_rhs_add_cst temp_e 1) el),
                   cs)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Unot ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                extract_constraint_expr_mod mv e1 mod_tmap tmap instmap
              | Fsint _ ->
                extract_constraint_expr_mod mv e1 mod_tmap tmap instmap
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Uextr (n1, n2) ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (_, cs) = p in
                   Some (((Expr
                   (make_rhs [] []
                     (n1-n2 +1))) :: []),
                   cs)
                 | None -> None)
              | Fsint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (_, cs) = p in
                   Some (((Expr
                   (make_rhs [] []
                   (n1-n2 +1))) :: []),
                   cs)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Uhead n ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (_, cs) = p in
                   Some (((Expr (make_rhs [] [] n)) :: []), cs)
                 | None -> None)
              | Fsint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (_, cs) = p in
                   Some (((Expr (make_rhs [] [] n)) :: []), cs)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Utail n ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (el, cs) = p in
                   Some
                   ((Stdlib.List.map (fun temp_e ->
                      min_rhs_add_cst temp_e (-n)) el), cs)
                 | None -> None)
              | Fsint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (el, cs) = p in
                   Some
                   ((Stdlib.List.map (fun temp_e ->
                      min_rhs_add_cst temp_e (-n)) el), cs)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | _ ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (_, cs) = p in
                   Some (((Expr (make_rhs [] [] 1)) :: []), cs)
                 | None -> None)
              | Fsint _ ->
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p ->
                   let (_, cs) = p in
                   Some (((Expr (make_rhs [] [] 1)) :: []), cs)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None))
  | Eprim_binop (e0, e1, e2) ->
    (match e0 with
     | Badd ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (el2, cs2) = p0 in
                               let nexp1 =
                                Stdlib.List.map (fun temp_e -> min_rhs_add_cst temp_e 1)
                                   el1
                               in
                               let nexp2 =
                                Stdlib.List.map (fun temp_e -> min_rhs_add_cst temp_e 1)
                                   el2
                               in
                               Some ((rev_append nexp1 nexp2),
                               (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (el2, cs2) = p0 in
                               let nexp1 =
                                Stdlib.List.map (fun temp_e -> min_rhs_add_cst temp_e 1)
                                   el1
                               in
                               let nexp2 =
                                Stdlib.List.map (fun temp_e -> min_rhs_add_cst temp_e 1)
                                   el2
                               in
                               Some ((rev_append nexp1 nexp2),
                               (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bsub ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (el2, cs2) = p0 in
                               let nexp1 =
                                Stdlib.List.map (fun temp_e -> min_rhs_add_cst temp_e 1)
                                   el1
                               in
                               let nexp2 =
                                Stdlib.List.map (fun temp_e -> min_rhs_add_cst temp_e 1)
                                   el2
                               in
                               Some ((rev_append nexp1 nexp2),
                               (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (el2, cs2) = p0 in
                               let nexp1 =
                                Stdlib.List.map (fun temp_e -> min_rhs_add_cst temp_e 1)
                                   el1
                               in
                               let nexp2 =
                                Stdlib.List.map (fun temp_e -> min_rhs_add_cst temp_e 1)
                                   el2
                               in
                               Some ((rev_append nexp1 nexp2),
                               (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bmul ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (el2, cs2) = p0 in
                               Some
                               ((Stdlib.List.map (fun pat ->
                                  let (e3, e4) = pat in combine_min_rhs e3 e4)
                                  (cartesian el1 el2)), (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (el2, cs2) = p0 in
                               Some
                               ((Stdlib.List.map (fun pat ->
                                  let (e3, e4) = pat in combine_min_rhs e3 e4)
                                  (cartesian el1 el2)), (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bdiv ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (_, cs2) = p0 in
                               Some (el1, (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (_, cs2) = p0 in
                               Some
                               ((Stdlib.List.map (fun temp_e ->
                                  min_rhs_add_cst temp_e (-1)) el1),
                               (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Brem ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (el2, cs2) = p0 in
                               Some
                               ((Stdlib.List.map (fun pat ->
                                  let (a, b) = pat in Min (a, b))
                                  (cartesian el1 el2)), (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (el2, cs2) = p0 in
                               Some
                               ((Stdlib.List.map (fun pat ->
                                  let (a, b) = pat in Min (a, b))
                                  (cartesian el1 el2)), (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bcomp _ ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (_, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (_, cs2) = p0 in
                               Some (((Expr (make_rhs [] [] 1)) :: []),
                               (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (_, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (_, cs2) = p0 in
                               Some (((Expr (make_rhs [] [] 1)) :: []),
                               (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bdshl ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match e2 with
                             | Econst (t0, bs) ->
                               (match t0 with
                                | Fuint_implicit _ ->
                                  Some
                                    ((Stdlib.List.map (fun temp_e ->
                                       min_rhs_add_cst temp_e
                                         (Z.to_int
                                           (Z.pow (Z.of_int 2)
                                             ((Stdlib.List.length bs))) -1)) el1),
                                    cs1)
                                | Fsint_implicit _ ->
                                  Some
                                    ((Stdlib.List.map (fun temp_e ->
                                       min_rhs_add_cst temp_e
                                         (Z.to_int
                                         (Z.pow (Z.of_int 2)
                                           ((Stdlib.List.length bs))) -1)) el1),
                                    cs1)
                                | _ ->
                                  Some
                                    ((Stdlib.List.map (fun temp_e ->
                                       min_rhs_add_cst temp_e
                                         (Z.to_int
                                           (Z.pow (Z.of_int 2)
                                             ((sizeof_fgtyp t0))) -1))
                                       el1), cs1))
                             | Eref r ->
                               (match type_of_ref r mod_tmap with
                                | Some f0 ->
                                  (match f0 with
                                   | Gtyp f3 ->
                                     (match f3 with
                                      | Fuint w ->
                                        Some
                                          ((Stdlib.List.map (fun temp_e ->
                                             min_rhs_add_cst temp_e
                                               (Z.to_int
                                                 (Z.pow (Z.of_int 2)
                                                   (w)) -1)) el1),
                                          cs1)
                                      | Fuint_implicit _ ->
                                        (match ref2pv_mod r mv instmap tmap with
                                         | Some pv ->
                                           Some
                                             ((Stdlib.List.map (fun temp_e ->
                                                min_rhs_add_power temp_e pv)
                                                el1), cs1)
                                         | None -> None)
                                      | _ -> None)
                                   | _ -> None)
                                | None -> None)
                             | _ -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match e2 with
                             | Econst (t0, bs) ->
                               (match t0 with
                                | Fuint_implicit _ ->
                                  Some
                                    ((Stdlib.List.map (fun temp_e ->
                                       min_rhs_add_cst temp_e
                                         (Z.to_int
                                         (Z.pow (Z.of_int 2)
                                           ((Stdlib.List.length bs))) -1)) el1),
                                    cs1)
                                | Fsint_implicit _ ->
                                  Some
                                    ((Stdlib.List.map (fun temp_e ->
                                       min_rhs_add_cst temp_e
                                         (Z.to_int
                                         (Z.pow (Z.of_int 2)
                                           ((Stdlib.List.length bs))) -1)) el1),
                                    cs1)
                                | _ ->
                                  Some
                                    ((Stdlib.List.map (fun temp_e ->
                                       min_rhs_add_cst temp_e
                                         (Z.to_int
                                         (Z.pow (Z.of_int 2)
                                           ((sizeof_fgtyp t0))) -1))
                                       el1), cs1))
                             | Eref r ->
                               (match type_of_ref r mod_tmap with
                                | Some f0 ->
                                  (match f0 with
                                   | Gtyp f3 ->
                                     (match f3 with
                                      | Fuint w ->
                                        Some
                                          ((Stdlib.List.map (fun temp_e ->
                                             min_rhs_add_cst temp_e
                                               (Z.to_int
                                               (Z.pow (Z.of_int 2)
                                                 (w)) -1)) el1),
                                          cs1)
                                      | Fuint_implicit _ ->
                                        (match ref2pv_mod r mv instmap tmap with
                                         | Some pv ->
                                           Some
                                             ((Stdlib.List.map (fun temp_e ->
                                                min_rhs_add_power temp_e pv)
                                                el1), cs1)
                                         | None -> None)
                                      | _ -> None)
                                   | _ -> None)
                                | None -> None)
                             | _ -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bdshr ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (_, cs2) = p0 in
                               Some (el1, (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (_, cs2) = p0 in
                               Some (el1, (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Bcat ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (el2, cs2) = p0 in
                               Some
                               ((Stdlib.List.map (fun pat ->
                                  let (e3, e4) = pat in combine_min_rhs e3 e4)
                                  (cartesian el1 el2)), (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (el2, cs2) = p0 in
                               Some
                               ((Stdlib.List.map (fun pat ->
                                  let (e3, e4) = pat in combine_min_rhs e3 e4)
                                  (cartesian el1 el2)), (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | _ ->
       (match type_of_hfexpr e1 mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fuint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (el2, cs2) = p0 in
                               Some ((rev_append el1 el2),
                               (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint _ ->
                (match type_of_hfexpr e2 mod_tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint _ ->
                         (match extract_constraint_expr_mod mv e1 mod_tmap
                                  tmap instmap with
                          | Some p ->
                            let (el1, cs1) = p in
                            (match extract_constraint_expr_mod mv e2 mod_tmap
                                     tmap instmap with
                             | Some p0 ->
                               let (el2, cs2) = p0 in
                               Some ((rev_append el1 el2),
                               (rev_append cs1 cs2))
                             | None -> None)
                          | None -> None)
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None))
  | Emux (c, e1, e2) ->
    (match type_of_hfexpr c mod_tmap with
     | Some f ->
       (match f with
        | Gtyp f1 ->
          (match f1 with
           | Fuint _ ->
             (match extract_constraint_expr_mod mv c mod_tmap tmap instmap with
              | Some p ->
                let (ec, cs0) = p in
                (match extract_constraint_expr_mod mv e1 mod_tmap tmap instmap with
                 | Some p0 ->
                   let (el1, cs1) = p0 in
                   (match extract_constraint_expr_mod mv e2 mod_tmap tmap
                            instmap with
                    | Some p1 ->
                      let (el2, cs2) = p1 in
                      Some ((rev_append el1 el2),
                      (rev_append ec (rev_append cs0 (rev_append cs1 cs2))))
                    | None -> None)
                 | None -> None)
              | None -> None)
           | _ -> None)
        | _ -> None)
     | None -> None)
  | Eref r ->
    (match type_of_ref r mod_tmap with
     | Some f ->
       (match f with
        | Gtyp gt ->
          (match gt with
           | Fuint_implicit _ ->
             (match ref2pv_mod r mv instmap tmap with
              | Some pv ->
                Some (((Expr
                  (make_rhs (((Stdlib.Int.succ 0), pv) :: []) [] 0)) :: []),
                  [])
              | None ->
                Some (((Expr
                  (make_rhs [] [] ((sizeof_fgtyp gt)))) :: []), []))
           | Fsint_implicit _ ->
             (match ref2pv_mod r mv instmap tmap with
              | Some pv ->
                Some (((Expr
                  (make_rhs (((Stdlib.Int.succ 0), pv) :: []) [] 0)) :: []),
                  [])
              | None ->
                Some (((Expr
                  (make_rhs [] [] ((sizeof_fgtyp gt)))) :: []), []))
           | _ ->
             Some (((Expr
               (make_rhs [] [] ((sizeof_fgtyp gt)))) :: []), []))
        | _ -> None)
     | None -> None)

(** val extract_mux_mod :
    int -> int H.t -> hfexpr -> (ftype * forient) H.t ->
    (ftype * forient) H.t H.t -> (href list * min_rhs list) option **)
let rec extract_mux_mod mv instmap e _ tmap =
  match H.find mv tmap with
  | Some mod_tmap ->
    (match e with
     | Emux (c, e1, e2) ->
       (match type_of_hfexpr c mod_tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ ->
                (match extract_constraint_expr_mod mv c mod_tmap tmap instmap with
                 | Some p ->
                   let (ec, cs0) = p in
                   (match extract_mux_mod mv instmap e1 mod_tmap tmap with
                    | Some p0 ->
                      let (r1, cs1) = p0 in
                      (match extract_mux_mod mv instmap e2 mod_tmap tmap with
                       | Some p1 ->
                         let (r2, cs2) = p1 in
                         Some ((rev_append r1 r2),
                         (rev_append ec (rev_append cs0 (rev_append cs1 cs2))))
                       | None -> None)
                    | None -> None)
                 | None -> None)
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Eref r -> Some ((r :: []), [])
     | _ -> None)
  | None -> None

(** val extract_constraint_passive :
    ftype -> ftype -> (int * (int * int)) -> (int * (int * int)) -> coq_Constraint1 list H_triple.t ->
    coq_Constraint1 list H_triple.t **)

let rec extract_constraint_passive ft ft_ref pv pvar c1map =
  match ft with
  | Gtyp f ->
    (match f with
     | Fuint_implicit _ ->
       (match ft_ref with
        | Gtyp f0 ->
          (match f0 with
           | Fuint w ->
             let nc = { lhs_var1 = pv; rhs_const1 = w;
               rhs_terms1 = []; rhs_power = [] } in
             (match H_triple.find pv c1map with
              | Some cs1 -> H_triple.add pv (nc :: cs1) c1map
              | None -> H_triple.add pv [nc] c1map);
             c1map
           | Fuint_implicit _ ->
             let nc = { lhs_var1 = pv; rhs_const1 = 0; rhs_terms1 =
               [(1, pvar)]; rhs_power = [] } in
             (match H_triple.find pv c1map with
              | Some cs1 -> H_triple.add pv (nc :: cs1) c1map
              | None -> H_triple.add pv [nc] c1map);
             c1map
           | _ -> c1map)
        | _ -> c1map)
     | Fsint_implicit _ ->
       (match ft_ref with
        | Gtyp f0 ->
          (match f0 with
           | Fsint w ->
             let nc = { lhs_var1 = pv; rhs_const1 = w;
               rhs_terms1 = []; rhs_power = [] } in
             (match H_triple.find pv c1map with
              | Some cs1 -> H_triple.add pv (nc :: cs1) c1map
              | None -> H_triple.add pv [nc] c1map);
             c1map
           | Fsint_implicit _ ->
             let nc = { lhs_var1 = pv; rhs_const1 = 0; rhs_terms1 =
               [(1, pvar)]; rhs_power = [] } in
             (match H_triple.find pv c1map with
              | Some cs1 -> H_triple.add pv (nc :: cs1) c1map
              | None -> H_triple.add pv [nc] c1map);
             c1map
           | _ -> c1map)
        | _ -> c1map)
     | _ -> c1map)
  | Atyp (atyp, _) ->
    (match ft_ref with
     | Atyp (atyp_ref, _) ->
       extract_constraint_passive atyp atyp_ref pv pvar c1map
     | _ -> c1map)
  | Btyp ff ->
    (match ft_ref with
     | Btyp ff_ref -> extract_constraint_passive_f ff ff_ref pv pvar c1map
     | _ -> c1map)

(** val extract_constraint_passive_f :
    ffield -> ffield -> (int * (int * int)) -> (int * (int * int)) -> coq_Constraint1 list H_triple.t
    -> coq_Constraint1 list H_triple.t **)

and extract_constraint_passive_f ff ff_ref pv pvar c1map =
  match ff with
  | Fnil -> c1map
  | Fflips (_, f, t0, fs) ->
    (match f with
     | Flipped -> c1map
     | Nflip ->
       (match ff_ref with
        | Fnil -> c1map
        | Fflips (_, f0, t_ref, fs_ref) ->
          (match f0 with
           | Flipped -> c1map
           | Nflip ->
             let nmap = extract_constraint_passive t0 t_ref pv pvar c1map in
             extract_constraint_passive_f fs fs_ref 
               ((fst pv), ((fst (snd pv)), ((snd (snd pv)) + (size_of_ftype t0))))
               ((fst pvar), ((fst (snd pvar)), ((snd (snd pvar)) + (size_of_ftype t0))))
               nmap)))

(** val extract_constraint_non_passive :
    ftype -> ftype -> bool -> (int * (int * int)) -> (int * (int * int)) -> coq_Constraint1 list
    H_triple.t -> coq_Constraint1 list H_triple.t **)

let rec extract_constraint_non_passive ft ft_ref flip pv pvar c1map =
  match ft with
  | Gtyp f ->
    (match f with
     | Fuint w ->
       (match ft_ref with
        | Gtyp f0 ->
          (match f0 with
           | Fuint_implicit _ ->
             if flip = false then c1map
             else
               let nc = { lhs_var1 = pvar; rhs_const1 = w;
                         rhs_terms1 = []; rhs_power = [] } in
               (match H_triple.find pvar c1map with
                | Some cs1 -> H_triple.add pvar (nc :: cs1) c1map
                | None -> H_triple.add pvar [nc] c1map);
               c1map
           | _ -> c1map)
        | _ -> c1map)
     | Fsint w ->
       (match ft_ref with
        | Gtyp f0 ->
          (match f0 with
           | Fsint_implicit _ ->
             if flip = false then c1map
             else
               let nc = { lhs_var1 = pvar; rhs_const1 = w;
                         rhs_terms1 = []; rhs_power = [] } in
               (match H_triple.find pvar c1map with
                | Some cs1 -> H_triple.add pvar (nc :: cs1) c1map
                | None -> H_triple.add pvar [nc] c1map);
               c1map
           | _ -> c1map)
        | _ -> c1map)
     | Fuint_implicit _ ->
       (match ft_ref with
        | Gtyp f0 ->
          (match f0 with
           | Fuint w ->
             if flip = false then
               let nc = { lhs_var1 = pv; rhs_const1 = w;
                         rhs_terms1 = []; rhs_power = [] } in
               (match H_triple.find pv c1map with
                | Some cs1 -> H_triple.add pv (nc :: cs1) c1map
                | None -> H_triple.add pv [nc] c1map);
               c1map
             else c1map
           | Fuint_implicit _ ->
             if flip = false then
               let nc = { lhs_var1 = pv; rhs_const1 = 0; rhs_terms1 =
                         [(1, pvar)]; rhs_power = [] } in
               (match H_triple.find pv c1map with
                | Some cs1 -> H_triple.add pv (nc :: cs1) c1map
                | None -> H_triple.add pv [nc] c1map);
               c1map
             else
               let nc = { lhs_var1 = pvar; rhs_const1 = 0; rhs_terms1 =
                         [(1, pv)]; rhs_power = [] } in
               (match H_triple.find pvar c1map with
                | Some cs1 -> H_triple.add pvar (nc :: cs1) c1map
                | None -> H_triple.add pvar [nc] c1map);
               c1map
           | _ -> c1map)
        | _ -> c1map)
     | Fsint_implicit _ ->
       (match ft_ref with
        | Gtyp f0 ->
          (match f0 with
           | Fsint w ->
             if flip = false then
               let nc = { lhs_var1 = pv; rhs_const1 = w;
                         rhs_terms1 = []; rhs_power = [] } in
               (match H_triple.find pv c1map with
                | Some cs1 -> H_triple.add pv (nc :: cs1) c1map
                | None -> H_triple.add pv [nc] c1map);
               c1map
             else c1map
           | Fsint_implicit _ ->
             if flip = false then
               let nc = { lhs_var1 = pv; rhs_const1 = 0; rhs_terms1 =
                         [(1, pvar)]; rhs_power = [] } in
               (match H_triple.find pv c1map with
                | Some cs1 -> H_triple.add pv (nc :: cs1) c1map
                | None -> H_triple.add pv [nc] c1map);
               c1map
             else
               let nc = { lhs_var1 = pvar; rhs_const1 = 0; rhs_terms1 =
                         [(1, pv)]; rhs_power = [] } in
               (match H_triple.find pvar c1map with
                | Some cs1 -> H_triple.add pvar (nc :: cs1) c1map
                | None -> H_triple.add pvar [nc] c1map);
               c1map
           | _ -> c1map)
        | _ -> c1map)
     | _ -> c1map)
  | Atyp (atyp, _) ->
    (match ft_ref with
     | Atyp (atyp_ref, _) ->
       extract_constraint_non_passive atyp atyp_ref flip pv pvar c1map
     | _ -> c1map)
  | Btyp ff ->
    (match ft_ref with
     | Btyp ff_ref ->
       extract_constraint_non_passive_f ff ff_ref flip pv pvar c1map
     | _ -> c1map)

(** val extract_constraint_non_passive_f :
    ffield -> ffield -> bool -> (int * (int * int)) -> (int * (int * int)) -> coq_Constraint1
    list H_triple.t -> coq_Constraint1 list H_triple.t **)

and extract_constraint_non_passive_f ff ff_ref flip pv pvar c1map =
  match ff with
  | Fnil -> c1map
  | Fflips (_, f, t0, fs) ->
    (match f with
     | Flipped ->
       (match ff_ref with
        | Fnil -> c1map
        | Fflips (_, f0, t_ref, fs_ref) ->
          (match f0 with
           | Flipped ->
             let nmap =
               extract_constraint_non_passive t0 t_ref (not flip) pv pvar c1map
             in
             extract_constraint_non_passive_f fs fs_ref flip
               ((fst pv), ((fst (snd pv)), ((snd (snd pv)) + (size_of_ftype t0))))
               ((fst pvar), ((fst (snd pvar)), ((snd (snd pvar)) + (size_of_ftype t0))))
               nmap
           | Nflip -> c1map))
     | Nflip ->
       (match ff_ref with
        | Fnil -> c1map
        | Fflips (_, f0, t_ref, fs_ref) ->
          (match f0 with
           | Flipped -> c1map
           | Nflip ->
             let nmap =
               extract_constraint_non_passive t0 t_ref flip pv pvar c1map
             in
             extract_constraint_non_passive_f fs fs_ref flip
               ((fst pv), ((fst (snd pv)), ((snd (snd pv)) + (size_of_ftype t0))))
               ((fst pvar), ((fst (snd pvar)), ((snd (snd pvar)) + (size_of_ftype t0))))
               nmap)))

(** val extract_constraint_ss :
    int -> hfstmt_seq -> (ftype * forient) H.t -> (ftype * forient) H.t H.t
    -> coq_Constraint1 list H_triple.t -> min_rhs list -> coq_Constraint_Min list
    -> int H.t -> (((coq_Constraint1 list H_triple.t * min_rhs list) * coq_Constraint_Min list) * int H.t) option **)

let rec extract_constraint_ss mv ss mod_tmap tmap c1map cs2 cs_min instmap =
  match ss with
  | Qnil -> Some (((c1map, cs2), cs_min), instmap)
  | Qcons (s, st) ->
    match extract_constraint_s mv s mod_tmap tmap c1map cs2 cs_min instmap with
    | Some p ->
      let (p0, instmap') = p in
      let (p1, cs_min') = p0 in
      let (c1map', cs2') = p1 in
      extract_constraint_ss mv st mod_tmap tmap c1map' cs2' cs_min' instmap'
    | None -> None

(** val extract_constraint_s :
    int -> hfstmt -> (ftype * forient) H.t -> (ftype * forient) H.t H.t
    -> coq_Constraint1 list H_triple.t -> min_rhs list -> coq_Constraint_Min list
    -> int H.t -> (((coq_Constraint1 list H_triple.t * min_rhs list) * coq_Constraint_Min list) * int H.t) option **)

and extract_constraint_s mv s mod_tmap tmap c1map cs2 cs_min instmap =
  match s with
  | Sreg (v, reg) ->
    let pv_reg = (mv, (((Obj.magic v) : int), 0)) in
    (match reg.coq_type with
     | Gtyp gt ->
       if not_implicit gt
       then Some (((c1map, cs2), cs_min), instmap)
       else (match reg.reset with
             | NRst -> Some (((c1map, cs2), cs_min), instmap)
             | Rst (_, rst_val) ->
               (match extract_constraint_expr_mod mv rst_val mod_tmap tmap instmap with
                | Some p ->
                  let (exprs, cs2') = p in
                  let (regular_cs, cs_min') = seperate_min pv_reg exprs ([], []) in
                  (match H_triple.find pv_reg c1map with
                   | Some cs1 -> H_triple.add pv_reg (List.rev_append regular_cs cs1) c1map
                   | None -> H_triple.add pv_reg regular_cs c1map);
                  Some (((c1map, (List.rev_append cs2' cs2)), (List.rev_append cs_min' cs_min)), instmap)
                | None -> None))
     | x ->
       (match reg.reset with
        | NRst -> Some (((c1map, cs2), cs_min), instmap)
        | Rst (_, rst_val) ->
          (match rst_val with
           | Emux (_, _, _) ->
             (match extract_mux_mod mv instmap rst_val mod_tmap tmap with
              | Some p ->
                let (rhsl, cs2') = p in
                let new_c1map = Stdlib.List.fold_left (fun temp_map ref0 ->
                  match ref2pv_mod ref0 mv instmap tmap with
                  | Some pvar ->
                    (match type_of_ref ref0 mod_tmap with
                     | Some ft_ref -> extract_constraint_passive x ft_ref pv_reg pvar temp_map
                     | None -> temp_map)
                  | None -> temp_map)   
                  c1map rhsl
                in
                Some (((new_c1map, (List.rev_append cs2' cs2)), cs_min), instmap)
              | None -> None)
           | Eref ref ->
             (match ref2pv_mod ref mv instmap tmap with
              | Some pvar ->
                (match type_of_ref ref mod_tmap with
                 | Some ft_ref ->
                   let new_c1map = extract_constraint_passive x ft_ref pv_reg pvar c1map in
                   Some (((new_c1map, cs2), cs_min), instmap)
                 | None -> None)
              | None -> None)
           | _ -> None)))
  | Sinst (inst_v, inst_mv) ->
    H.add ((Obj.magic inst_v) : int) ((Obj.magic inst_mv) : int) instmap;
    Some (((c1map, cs2), cs_min), instmap)
  | Snode (v, e) ->
    let pv_node = (mv, (((Obj.magic v) : int), 0)) in
    (match H.find mv tmap with
     | Some mod_tmap0 ->
       (match H.find ((Obj.magic v) : int) mod_tmap0 with
        | Some p ->
          let (ft, _) = p in
          (match ft with
           | Gtyp _ ->
             (match extract_constraint_expr_mod mv e mod_tmap0 tmap instmap with
              | Some p0 ->
                let (exprs, cs2') = p0 in
                let (regular_cs, cs_min') = seperate_min pv_node exprs ([], []) in
                (match H_triple.find pv_node c1map with
                 | Some cs1 -> H_triple.add pv_node (List.rev_append regular_cs cs1) c1map
                 | None -> H_triple.add pv_node regular_cs c1map);
                Some (((c1map, (List.rev_append cs2' cs2)), (List.rev_append cs_min' cs_min)), instmap)
              | None -> None)
           | _ ->
             (match e with
              | Emux (_, _, _) ->
                (match extract_mux_mod mv instmap e mod_tmap0 tmap with
                 | Some p0 ->
                   let (rhsl, cs2') = p0 in
                   let new_c1map = Stdlib.List.fold_left (fun temp_map ref0 ->
                    match ref2pv_mod ref0 mv instmap tmap with
                    | Some pvar ->
                      (match type_of_ref ref0 mod_tmap0 with
                       | Some ft_ref -> extract_constraint_passive ft ft_ref pv_node pvar temp_map
                       | None -> temp_map)
                    | None -> temp_map) c1map rhsl
                  in
                  Some (((new_c1map, (List.rev_append cs2' cs2)), cs_min), instmap)
                 | None -> None)
              | Eref ref ->
                (match ref2pv_mod ref mv instmap tmap with
                 | Some pvar ->
                   (match type_of_ref ref mod_tmap0 with
                    | Some ft_ref ->
                      let new_c1map = extract_constraint_passive ft ft_ref pv_node pvar c1map in
                      Some (((new_c1map, cs2), cs_min), instmap)
                    | None -> None)
                 | None -> None)
              | _ -> None))
        | None -> None)
     | None -> None)
  | Sfcnct (r, expr) ->
    (match type_of_ref r mod_tmap with
     | Some ft ->
       (match ft with
        | Gtyp gt ->
          if not_implicit gt
          then Some (((c1map, cs2), cs_min), instmap)
          else (match ref2pv_mod r mv instmap tmap with
                | Some pv ->
                  (match extract_constraint_expr_mod mv expr mod_tmap tmap instmap with
                   | Some p ->
                     let (exprs, cs2') = p in
                     let (regular_cs, cs_min') = seperate_min pv exprs ([], []) in
                     (match H_triple.find pv c1map with
                      | Some cs1 -> H_triple.add pv (List.rev_append regular_cs cs1) c1map
                      | None -> H_triple.add pv regular_cs c1map);
                     Some (((c1map, (List.rev_append cs2 cs2')), (List.rev_append cs_min cs_min')), instmap)
                   | None -> None)
                | None -> None)
        | _ ->
          (match expr with
           | Emux (_, _, _) ->
             (match ref2pv_mod r mv instmap tmap with
              | Some pv ->
                (match extract_mux_mod mv instmap expr mod_tmap tmap with
                 | Some p ->
                   let (rhsl, cs2') = p in
                   let new_c1map = Stdlib.List.fold_left (fun temp_map ref0 ->
                    match ref2pv_mod ref0 mv instmap tmap with
                    | Some pvar ->
                      (match type_of_ref ref0 mod_tmap with
                       | Some ft_ref -> extract_constraint_passive ft ft_ref pv pvar temp_map
                       | None -> temp_map)
                    | None -> temp_map) c1map rhsl
                  in
                  Some (((new_c1map, (List.rev_append cs2' cs2)), cs_min), instmap)                 | None -> None)
              | None -> None)
           | Eref ref ->
             (match ref2pv_mod r mv instmap tmap with
              | Some pv ->
                (match ref2pv_mod ref mv instmap tmap with
                 | Some pvar ->
                   (match type_of_ref ref mod_tmap with
                    | Some ft_ref ->
                      let new_c1map = extract_constraint_non_passive ft ft_ref false pv pvar c1map in
                      Some (((new_c1map, cs2), cs_min), instmap)
                    | None -> None)
                 | None -> None)
              | None -> None)
           | _ -> None))
     | None -> None)
  | Swhen (c, ss_true, ss_false) ->
    (match extract_constraint_expr_mod mv c mod_tmap tmap instmap with
     | Some p ->
       let (ce0, ce1) = p in
       (match extract_constraint_ss mv ss_true mod_tmap tmap c1map
                (List.rev_append ce1 (List.rev_append ce0 cs2)) cs_min instmap with
        | Some p0 ->
          let (p1, instmap') = p0 in
          let (p2, cs_min') = p1 in
          let (c1map', cs2') = p2 in
          extract_constraint_ss mv ss_false mod_tmap tmap c1map' cs2' cs_min' instmap'
        | None -> None)
     | None -> None)
  | _ -> Some (((c1map, cs2), cs_min), instmap)

(** val extract_constraint_ml :
    hfmodule list -> (ftype * forient) H.t H.t -> coq_Constraint1 list
    H_triple.t -> min_rhs list -> coq_Constraint_Min list -> ((coq_Constraint1
    list H_triple.t * min_rhs list) * coq_Constraint_Min list) option **)

let rec extract_constraint_ml ml tmap c1map cs2 cs_min =
  match ml with
  | [] -> Some ((c1map, cs2), cs_min)
  | y :: tl ->
    (match y with
     | FInmod (mv, _, ss) ->
       (match H.find ((Obj.magic mv) : int) tmap with
        | Some mod_tmap ->
          (match extract_constraint_ss ((Obj.magic mv) : int) ss mod_tmap tmap c1map cs2 cs_min
                   (H.empty ()) with
           | Some p ->
             let (p0, _) = p in
             let (p1, cs_min') = p0 in
             let (c1map', cs2') = p1 in
             extract_constraint_ml tl tmap c1map' cs2' cs_min'
           | None -> None)
        | None -> None)
     | FExmod (_, _, _) -> extract_constraint_ml tl tmap c1map cs2 cs_min)

(** val extract_constraints_c :
    hfcircuit -> (ftype * forient) H.t H.t -> (coq_Constraint1 list H_triple.t
    list * min_rhs list) option **)

let extract_constraints_c c tmap =
  let Fcircuit (_, ml) = c in
  (match extract_constraint_ml ml tmap (H_triple.empty ()) [] [] with
   | Some p ->
     let (p0, cs_min) = p in
     let (c1map, cs2) = p0 in
     let group_of_mins = List.map list_Constraint_Min cs_min in
     let group_of_cs1 = cartesian_product group_of_mins in
     (match group_of_cs1 with
      | [] -> Some ((c1map :: []), cs2)
      | _ :: _ ->
        Some
          ((List.map (fun new_cs1 -> add_cs1_2_c1map new_cs1 c1map) group_of_cs1),
          cs2))
   | None -> None)

let tr_map f lst =
  let rec aux acc = function
    | [] -> Stdlib.List.rev acc 
    | h :: t -> aux (f h :: acc) t
  in
  aux [] lst

(** val extract_cs :
    TripVar.t list -> coq_Constraint1 list H_triple.t -> coq_Constraint1 list **)

let rec extract_cs ls cs1 =
  match ls with
  | [] -> []
  | hd :: tl ->
    match H_triple.find hd cs1 with
    | Some c -> List.rev_append c (extract_cs tl cs1)
    | None -> extract_cs tl cs1

(** val remove_solved : int H_triple.t -> term list -> term list * Z.t **)

let rec remove_solved values = function
| [] -> ([], Z.zero)
| t0 :: tl ->
  let (coe, var) = t0 in
  match H_triple.find var values with
  | Some val0 ->
    let (terms', cst) = remove_solved values tl in
    (terms', Z.add cst (Z.of_int (coe * val0)))
  | None ->
    let (terms', cst) = remove_solved values tl in
    ((coe, var) :: terms', cst)

(** val remove_solved_c : int H_triple.t -> coq_Constraint1 -> coq_Constraint1 **)

let remove_solved_c values c =
  let (new_terms, new_cst) = remove_solved values c.rhs_terms1 in
  match c.rhs_power with
  | [] ->
    { lhs_var1 = c.lhs_var1;
      rhs_const1 = c.rhs_const1 + (Z.to_int new_cst);
      rhs_terms1 = new_terms;
      rhs_power = [] }
  | t0 :: _ ->
    let (_, var) = t0 in
    match H_triple.find var values with
    | Some val0 ->
      { lhs_var1 = c.lhs_var1;
        rhs_const1 = c.rhs_const1 + (Z.to_int new_cst) +
                         (Z.to_int (Z.pow (Z.of_int 2) val0));
        rhs_terms1 = new_terms;
        rhs_power = [] }
    | None ->
      { lhs_var1 = c.lhs_var1;
        rhs_const1 = c.rhs_const1 + (Z.to_int new_cst);
        rhs_terms1 = new_terms;
        rhs_power = c.rhs_power }

(** val max_nl : Z.t list -> int -> int **)

let rec max_nl l init =
  match l with
  | [] -> init
  | t0 :: tl -> max_nl tl (max init t0)

(** val merge_solution :
    TripVar.t list -> int H_triple.t -> int TVM.t -> int H_triple.t option **)

let rec merge_solution tbsolved initial solution_of_tbsolved =
  match tbsolved with
  | [] -> Some initial
  | hd :: tl ->
    match TVM.find hd solution_of_tbsolved with
    | Some val0 ->
        H_triple.add hd val0 initial;   (* 原地修改哈希表 *)
        merge_solution tl initial solution_of_tbsolved
    | None -> None

(** val solve_alg :
    TripVar.t list list -> int H_triple.t -> coq_Constraint1 list H_triple.t -> int
    H_triple.t option **)

let rec solve_alg res values cs1 =
  match res with
  | [] -> Some values
  | hd :: tl ->
    let tbsolved_cs = extract_cs hd cs1 in
    let tbsolved_cs' = List.map (remove_solved_c values) tbsolved_cs in
    (match solve_scc hd tbsolved_cs' with
     | Some nv ->
       (match merge_solution hd values nv with
        | Some new_values -> solve_alg tl new_values cs1
        | None -> None)
     | None -> None)

(** val solve_alg_check :
    TripVar.t list list -> coq_Constraint1 list H_triple.t -> min_rhs list -> int
    H_triple.t option **)

let solve_alg_check res cs1 cs2 =
  match solve_alg res (H_triple.empty ()) cs1 with
  | Some value ->
    if forallb (fun c -> Z.leq (min_rhs_value value c) (Z.of_int 1)) cs2
    then Some value
    else None
  | None -> None

(** val smaller_valuation : int H_triple.t -> int H_triple.t -> int H_triple.t **)

let smaller_valuation v1 v2 =
  let result = H_triple.empty () in
  Hashtbl.iter (fun key val1 ->
    match H_triple.find key v2 with
    | Some val2 -> H_triple.add key (min val1 val2) result
    | None -> ()
  ) v1;
  result

let my_solve_helper c1map cs2 =
  let ut0 = (Unix.times()).tms_utime in 
  let cs1 = Hashtbl.fold (fun _ v acc -> rev_append v acc) c1map [] in
  let ut1 = (Unix.times()).tms_utime in 
  let dpdcg = build_graph_from_constraints cs1 in
  let ut2 = (Unix.times()).tms_utime in 
  let res = SCC.scc_list dpdcg in
  let ut3 = (Unix.times()).tms_utime in 
  let res' = tr_map (fun l -> tr_map (fun v-> nat_to_triple (G.V.label v)) l) res in
  let ut4 = (Unix.times()).tms_utime in 
  printf "fold : %f\ndraw : %f\ntarjan : %f\nnat2triple : %f\n" (Float.sub ut1 ut0) (Float.sub ut2 ut1) (Float.sub ut3 ut2) (Float.sub ut4 ut3); 
  (*print_scc_list res;*)
  solve_alg_check res' c1map cs2

let my_solve_fun c tmap =
  let ut0 = (Unix.times()).tms_utime in 
    match extract_constraints_c c tmap with
    | Some (c1maps, cs2) -> let ut1 = (Unix.times()).tms_utime in 
      let solution = Stdlib.List.fold_left (fun res c1map ->
        match res with
        | Some old_values -> 
          (match my_solve_helper c1map cs2 with
           | Some new_values -> 
              Some (smaller_valuation old_values new_values)
           | None -> res)
        | None -> my_solve_helper c1map cs2) None c1maps in
      let ut2 = (Unix.times()).tms_utime in 
      printf "extraction time : %f\ncomputation time : %f\n" (Float.sub ut1 ut0) (Float.sub ut2 ut1); solution
    | None -> None

(** val update_tmap :
    (ftype * forient) H.t H.t -> (TripVar.t * int) list ->
    (ftype * forient) H.t H.t option **)

let rec update_tmap tmap = function
| [] -> Some tmap
| (pv, w) :: tl ->
  let mod_name = fst pv in
  let var_name = fst (snd pv) in
  let offset = snd (snd pv) in
  match H.find mod_name tmap with
  | Some mod_tmap -> printf "0\n";
    (match H.find var_name mod_tmap with
     | Some (ft, ori) -> printf "1\n";
       (match update_ftype offset w ft with
        | Some nft -> printf "2\n";
          H.add var_name (nft, ori) mod_tmap;  (* 原地修改内层哈希表 *)
          update_tmap tmap tl                      (* 外层表引用不变，直接递归 *)
        | None -> None)
     | None -> None)
  | None -> None

(** val coq_InferWidths_transp :
    hfport -> (ftype * forient) H.t -> hfport option **)

let coq_InferWidths_transp p tmap =
  match p with
  | Finput (v, t0) ->
    if ftype_not_implicit t0
    then Some p
    else (match H.find ((Obj.magic v) : int) tmap with
          | Some p0 -> let (ft, _) = p0 in Some (Finput (v, ft))
          | None -> None)
  | Foutput (v, t0) ->
    if ftype_not_implicit t0
    then Some p
    else (match H.find ((Obj.magic v) : int) tmap with
          | Some p0 -> let (ft, _) = p0 in Some (Foutput (v, ft))
          | None -> None)

let my_coq_InferWidths_transps ps tmap =
  let rec loop ps acc =
    match ps with
    | [] -> Some (Stdlib.List.rev acc) 
    | p :: tl ->
        match coq_InferWidths_transp p tmap with
        | None -> None 
        | Some n -> loop tl (n :: acc)
  in
  loop ps [] 

let rec my_coq_InferWidths_transs s tmap res =
  match s with
  | HiFirrtl.Swire (v, t0) ->
    if HiEnv.ftype_not_implicit t0
    then Some (HiFirrtl.Qcons (s, res))
    else (match H.find ((Obj.magic v) : int) tmap with
          | Some p -> let (ft, _) = p in Some (HiFirrtl.Qcons (Swire (v, ft), res))
          | None -> None)
  | Sreg (v, r) ->
    if HiEnv.ftype_not_implicit r.coq_type
    then Some (HiFirrtl.Qcons (s, res))
    else (match H.find ((Obj.magic v) : int) tmap with
          | Some p ->
            let (ft, _) = p in
            Some (HiFirrtl.Qcons (Sreg (v, { coq_type = ft; clock = r.clock; reset =
            r.reset }), res))
          | None -> None)
  | Swhen (c, s1, s2) ->
    (match my_coq_InferWidths_transss s1 tmap HiFirrtl.Qnil with
     | Some n1 ->
       (match my_coq_InferWidths_transss s2 tmap HiFirrtl.Qnil with
        | Some n2 -> Some (HiFirrtl.Qcons (Swhen (c, n1, n2), res))
        | None -> None)
     | None -> None)
  | _ -> Some (HiFirrtl.Qcons (s, res))

and my_coq_InferWidths_transss sts tmap res =
  match sts with
  | HiFirrtl.Qnil -> Some res
  | HiFirrtl.Qcons (s, ss) ->
    (match my_coq_InferWidths_transs s tmap res with
    | Some n ->
      my_coq_InferWidths_transss ss tmap n
    | None -> None)

let my_coq_InferWidths_trans_m m tmap =
  match m with
  | HiFirrtl.FInmod (mv, ps, ss) ->
    (match H.find ((Obj.magic mv) : int) tmap with
     | Some mod_tmap ->
       (match my_coq_InferWidths_transps ps mod_tmap with
        | Some nps ->
          (match my_coq_InferWidths_transss ss mod_tmap HiFirrtl.Qnil with
           | Some nss -> Some (HiFirrtl.FInmod (mv, nps, Transhiast.revstmts nss HiFirrtl.Qnil))
           | None -> None)
        | None -> None)
     | None -> None)
  | FExmod (_, _, _) -> Some m

let rec my_coq_InferWidths_trans_ml ml tmap =
  match ml with
  | [] -> Some []
  | hd :: tl ->
    (match my_coq_InferWidths_trans_m hd tmap with
     | Some nhd ->
       (match my_coq_InferWidths_trans_ml tl tmap with
        | Some ntl -> Some (nhd :: ntl)
        | None -> None)
     | None -> None)

let my_coq_InferWidths_trans_c c tmap =
  let HiFirrtl.Fcircuit (c0, ml) = c in
  (match my_coq_InferWidths_trans_ml ml tmap with
   | Some nml -> Some (HiFirrtl.Fcircuit (c0, nml))
   | None -> None)

let my_coq_InferWidths_fun c =
  match circuit_tmap c with
  | Some tmap -> 
      let ut0 = (Unix.times()).tms_utime in 
      (match my_solve_fun c tmap with
      | Some solution ->
          let ut1 = (Unix.times()).tms_utime in 
          let elements = Hashtbl.fold (fun k v acc -> (k, v) :: acc) solution [] in
          printf "total time : %f\n" (Float.sub ut1 ut0);
          printf "components amount : %d\n" (Stdlib.List.length elements);
          (match update_tmap tmap elements with
          | Some newtm -> 
              (match my_coq_InferWidths_trans_c c newtm with
              | Some newc -> Some (newc, newtm)
              | None -> None)
          | None -> None)
      | None -> None)
  | None -> None

(*let print_iw_fir in_file hif_ast = 
  let oc_fir = open_out (process_string in_file "_iw.fir") in 
  (*Ast.pp_fcircuit stdout hif_ast;*)
  let ((modmap, _), map) = Transhiast_without_inline.mapcir hif_ast in 
  let fcir = Transhiast_without_inline.trans_cir hif_ast modmap map in

  (match my_coq_InferWidths_fun fcir with
  | Some (newc, newtm) -> (*Printfir.pp_fcircuit_fir oc_fir newc; Printfir.pp_fcircuit_fir stdout newc; close_out oc_fir;*)
    printf "%s width inference is finished\n" in_file;
    Printfir.pp_fcircuit_fir stdout newc;
    (*
    let string_cir = Transfast_hash.trans_cir hif_ast modmap map newtm in 
    Ast.pp_fcircuit oc_fir string_cir; close_out oc_fir*)
  | _ -> output_string stdout ("cannot be inferred\n"))*)
