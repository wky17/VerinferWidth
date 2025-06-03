open Hifirrtl_lang
open Extraction.Ssrnat
open Extraction.PeanoNat
open Extraction.Eqtype

module StringMap = Map.Make(String)

let rec make_ftype_explicit = function
| Ast.Gtyp ft' ->
  (match ft' with
   | Fuint_implicit w -> Ast.Gtyp (Fuint w)
   | Fsint_implicit w -> Gtyp (Fsint w)
   | x -> Gtyp x)
| Atyp (ft', n) -> Atyp ((make_ftype_explicit ft'), n)
| Btyp fs -> Btyp (make_ffield_explicit fs)

(** val make_ffield_explicit : ffield -> ffield_explicit **)

and make_ffield_explicit = function
| Fnil -> Fnil
| Fflips (v, ff, ft, fs') ->
  Fflips (v, ff, (make_ftype_explicit ft), (make_ffield_explicit fs'))

let rec type_of_ref r tmap =
  match r with
  | Ast.Eid v -> (*Printf.printf "\nfind node %s error\n" v;*) Some (make_ftype_explicit (StringMap.find v tmap))
  | Esubfield (r0, v) ->
    (match type_of_ref r0 tmap with
     | Some f ->
       (match f with
        | Ast.Btyp fs ->
          let rec aux = function
          | Ast.Fnil -> None
          | Fflips (v', _, t0, fxs) ->
            if (String.equal v v')
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
  | Esubaccess (_, _) -> None

let fgtyp_mux x y =
  match x with
  | Ast.Fuint wx ->
    (match y with
     | Ast.Fuint wy -> Some (Ast.Fuint (maxn wx wy))
     | _ -> None)
  | Fsint wx ->
    (match y with
     | Fsint wy -> Some (Fsint (maxn wx wy))
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
  | Ast.Gtyp tx ->
    (match y with
     | Ast.Gtyp ty ->
       (match fgtyp_mux tx ty with
        | Some f -> Some (Ast.Gtyp f)
        | None -> None)
     | _ -> None)
  | Atyp (tx, nx) ->
    (match y with
     | Atyp (ty, ny) ->
       if eq_op coq_Datatypes_nat__canonical__eqtype_Equality (Obj.magic nx)
            (Obj.magic ny)
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
             if (String.equal v1 v2)
             then (match ftype_mux' t1 t2 with
                   | Some f3 ->
                     (match ffield_mux' fs1 fs2 with
                      | Some f4 -> Some (Fflips (v1, Nflip, f3, f4))
                      | None -> None)
                   | None -> None)
             else None)))

(** val ftype_mux :
    ftype_explicit -> ftype_explicit -> ftype_explicit option **)

let ftype_mux =
  ftype_mux'

(** val type_of_hfexpr :
    hfexpr -> (ftype * forient) VM.t -> ftype_explicit option **)

let rec type_of_hfexpr e tmap =
  match e with
  | Ast.Econst (t0, bs) ->
    (match t0 with
     | Fuint_implicit _ -> Some (Ast.Gtyp (Fuint (String.length (Z.to_bits bs))))
     | Fsint_implicit _ -> Some (Gtyp (Fsint (String.length (Z.to_bits bs))))
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
              | _ -> Some (Gtyp (Fuint (Stdlib.Int.succ 0))))
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
              | _ -> Some (Gtyp (Fsint (Stdlib.Int.succ 0))))
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
              | Fuint w -> Some (Gtyp (Fuint (maxn w n)))
              | Fsint w -> Some (Gtyp (Fsint (maxn w n)))
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Ushl n ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w -> Some (Gtyp (Fuint (addn w n)))
              | Fsint w -> Some (Gtyp (Fsint (addn w n)))
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Ushr n ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w -> Some (Gtyp (Fuint (maxn (subn w n) 0)))
              | Fsint w ->
                Some (Gtyp (Fsint (maxn (subn w n) (Stdlib.Int.succ 0))))
              | _ -> None)
           | _ -> None)
        | None -> None)
     | Ucvt ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint w -> Some (Gtyp (Fsint (addn w (Stdlib.Int.succ 0))))
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
              | Fuint w -> Some (Gtyp (Fsint (addn w (Stdlib.Int.succ 0))))
              | Fsint w -> Some (Gtyp (Fsint (addn w (Stdlib.Int.succ 0))))
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
              | Fuint _ ->
                Some (Gtyp (Fuint (addn (subn n1 n2) (Stdlib.Int.succ 0))))
              | Fsint _ ->
                Some (Gtyp (Fuint (addn (subn n1 n2) (Stdlib.Int.succ 0))))
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
              | Fuint w -> Some (Gtyp (Fuint (subn w n)))
              | Fsint w -> Some (Gtyp (Fuint (subn w n)))
              | _ -> None)
           | _ -> None)
        | None -> None)
     | _ ->
       (match type_of_hfexpr e1 tmap with
        | Some f ->
          (match f with
           | Gtyp f1 ->
             (match f1 with
              | Fuint _ -> Some (Gtyp (Fuint (Stdlib.Int.succ 0)))
              | Fsint _ -> Some (Gtyp (Fuint (Stdlib.Int.succ 0)))
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
                         Some (Gtyp (Fuint
                           (addn (maxn w1 w2) (Stdlib.Int.succ 0))))
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
                         Some (Gtyp (Fsint
                           (addn (maxn w1 w2) (Stdlib.Int.succ 0))))
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
                         Some (Gtyp (Fuint
                           (addn (maxn w1 w2) (Stdlib.Int.succ 0))))
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
                         Some (Gtyp (Fsint
                           (addn (maxn w1 w2) (Stdlib.Int.succ 0))))
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
                       | Fuint w2 -> Some (Gtyp (Fuint (addn w1 w2)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint w2 -> Some (Gtyp (Fsint (addn w1 w2)))
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
                         Some (Gtyp (Fsint (addn w1 (Stdlib.Int.succ 0))))
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
                       | Fuint w2 -> Some (Gtyp (Fuint (minn w1 w2)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint w2 -> Some (Gtyp (Fsint (minn w1 w2)))
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
                       | Fuint _ -> Some (Gtyp (Fuint (Stdlib.Int.succ 0)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint _ ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint _ -> Some (Gtyp (Fuint (Stdlib.Int.succ 0)))
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
                         Some (Gtyp (Fuint
                           (subn
                             (addn
                               (expn (Stdlib.Int.succ (Stdlib.Int.succ 0)) w2)
                               w1) (Stdlib.Int.succ 0))))
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
                         Some (Gtyp (Fsint
                           (subn
                             (addn
                               (expn (Stdlib.Int.succ (Stdlib.Int.succ 0)) w2)
                               w1) (Stdlib.Int.succ 0))))
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
                       | Fuint w2 -> Some (Gtyp (Fuint (addn w1 w2)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint w2 -> Some (Gtyp (Fuint (addn w1 w2)))
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
                       | Fuint w2 -> Some (Gtyp (Fuint (maxn w1 w2)))
                       | _ -> None)
                    | _ -> None)
                 | None -> None)
              | Fsint w1 ->
                (match type_of_hfexpr e2 tmap with
                 | Some f2 ->
                   (match f2 with
                    | Gtyp f4 ->
                      (match f4 with
                       | Fsint w2 -> Some (Gtyp (Fuint (maxn w1 w2)))
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
  | Eref r -> type_of_ref r tmap

