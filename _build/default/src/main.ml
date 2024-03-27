module T = Kernel.Term
module B = Kernel.Basic
module S = Kernel.Subst
module R = Kernel.Rule
module E = Parsers.Entry
module P = Parsers.Parser
module Pp = Api.Pp.Default

(* Apply double negation to a term u *)
let add_double_neg lo n u =
  (T.mk_App 
      (T.mk_Const lo (B.mk_name (B.md n) (B.mk_ident "not"))) 
      (T.mk_App (T.mk_Const lo (B.mk_name (B.md n) (B.mk_ident "not"))) u []) 
      [])
;;

(* Transform Prf_c p into Prf (not (not p)) *)
let add_double_neg_prf lo n u l = 
  (T.mk_App 
    (T.mk_Const lo (B.mk_name (B.md n) (B.mk_ident "Prf"))) 
    (add_double_neg lo n u) 
    l)
;;

(* Transform all_c a p into all_c a (x : El a => (not (not (p x))) *)
let add_double_neg_all lo n u l = 
  let h = List.hd l in
  match h with
  | T.Lam (lo2, id, tob, t2) -> 
    T.mk_App (T.mk_Const lo (B.mk_name (B.md n) (B.mk_ident "all"))) 
    u 
    [T.mk_Lam lo2 id tob (add_double_neg lo n t2)]
  | _ -> 
    let idx = B.mk_ident "x" in 
    let x = T.mk_DB lo idx 0 in 
    T.mk_App 
      (T.mk_Const lo (B.mk_name (B.md n) (B.mk_ident "all"))) 
      u 
      [T.mk_Lam lo idx None (add_double_neg lo n (T.mk_App (S.shift 1 h) x []))]
;;

(* Transform Prf_c p and all_c in term v *)
let rec add_double_neg_term v = 
  match v with
  | T.App (t, u, l) -> 
    (match t with
    | Const (lo, n) -> 
      (if String.equal "Prf_c" (B.string_of_ident (B.id n)) 
      then add_double_neg_prf lo n (add_double_neg_term u) (List.map add_double_neg_term l)
      else 
        (if String.equal "all_c" (B.string_of_ident (B.id n)) 
        then add_double_neg_all lo n u (List.map add_double_neg_term l)
        else T.mk_App (add_double_neg_term t) (add_double_neg_term u) (List.map add_double_neg_term l)))
    | _ -> T.mk_App (add_double_neg_term t) (add_double_neg_term u) (List.map add_double_neg_term l))
  | Lam (lo, id, None, t) -> T.mk_Lam lo id None (add_double_neg_term t) 
  | Lam (lo, id, Some tob, t) -> T.mk_Lam lo id (Some (add_double_neg_term tob)) (add_double_neg_term t) 
  | Pi (lo, id, a, b) -> T.mk_Pi lo id (add_double_neg_term a) (add_double_neg_term b)
  | Kind -> T.mk_Kind
  | Type lo -> T.mk_Type lo
  | DB (lo, id, n) -> T.mk_DB lo id n
  | Const (lo, n) -> T.mk_Const lo n
;;

(* Transform Prf_c p and all_c in option term ty *)
let add_double_neg_ty ty = 
  match ty with
  | None -> None
  | Some t -> Some (add_double_neg_term t)
;;

(* Transform Prf_c p and all_c in pattern pat *)
let add_double_neg_pat pat = 
  let open R in
  Brackets (add_double_neg_term (pattern_to_term pat))
;;

(* Transform Prf_c p and all_c in rule r *)
let add_double_neg_rule (r : R.partially_typed_rule) = 
  let open R in
  {name = r.name ; 
  ctx = r.ctx ; 
  pat = add_double_neg_pat r.pat ; 
  rhs = add_double_neg_term r.rhs}
;;

(* Transform Prf_c p and all_c in entry e *)
let add_double_neg_entry e = 
  match e with
  | E.Decl (lo, id, s1, s2, t) -> E.Decl (lo, id, s1, s2, add_double_neg_term t)
  | Def (lo, id, s, io, ty, t) -> Def (lo, id, s, io, add_double_neg_ty ty, add_double_neg_term t)
  | Rules (lo, l) -> Rules (lo, List.map add_double_neg_rule l)
  | Eval (lo, cfg, t) -> Eval (lo, cfg, t)
  | Check (lo, ia, sf, t) -> Check (lo, ia, sf, t)
  | Infer (lo, cfg, t) -> Infer (lo, cfg, t)
  | Print (lo, s) -> Print (lo, s)
  | DTree (lo, op, id) -> DTree (lo, op, id)
  | Name (lo, id) -> Name (lo, id)
  | Require (lo, id) -> Require (lo, id)
;; 

Api.Pp.print_module_name := false;;
Api.Pp.print_db_enabled := false;;

(* Transform Prf_c p and all_c in the Dedukti file given in the command line *)
let usage_msg = "A tool to replace Prf_c p by Prf (not (not p)) and all_c a p by all a (x : El a => not (not (p x)))\n"
let filename = ref None
let speclist = [( "--file", Arg.String (fun s -> filename := Some s), "The file in wich to add double negations")]

let () = 
  Arg.parse speclist (fun _ -> ()) usage_msg;
  match !filename with
  | None -> Format.printf "[Error] No file given as argument\n"
  | Some f -> 
    (let parsed_file = P.(parse (input_from_file f))
    in List.iter (fun e -> Format.printf "%a" Pp.print_entry (add_double_neg_entry e)) parsed_file)
;;
