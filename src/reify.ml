(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Reify - Tools for reification

*)

(* These are necessary for grammar extensions like the one at the end 
   of the module *)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

(* $$ *)

open Term
open Util
open Names
open Tactics
open Tacticals

(** A tactic to help reification based on classes:
    factorize all variables of a particular type into a varmap. *)

let gen_constant dir s = Coqlib.gen_constant "reify" dir s
let init_constant dir s = 
  Libnames.constr_of_global (Coqlib.find_reference "reify" dir s)

let datatypes_path = ["Coq";"Init";"Datatypes"]

let coq_list_ind = lazy (init_constant datatypes_path "list")
let coq_list_nil = lazy (init_constant datatypes_path "nil")
let coq_list_cons = lazy (init_constant datatypes_path "cons")

let dynamic_path = ["Reify";"Dynamic"]
let coq_dynamic_ind = lazy (init_constant dynamic_path "dynamic")
let coq_dynamic_constr = lazy (init_constant dynamic_path "mkDynamic")
let coq_dynamic_type = lazy (init_constant dynamic_path "dynamic_type")
let coq_dynamic_obj = lazy (init_constant dynamic_path "dynamic_obj")

let coq_prod = lazy (init_constant datatypes_path "prod")
let coq_pair = lazy (init_constant datatypes_path "pair")

let coq_List_nth = lazy (gen_constant ["Lists"; "List"] "nth")

let freevars c =
  let rec frec acc c = match kind_of_term c with
    | Var id       -> Idset.add id acc
    | _ -> fold_constr frec acc c
  in
  frec Idset.empty c

let coq_zero = lazy (gen_constant ["Init"; "Datatypes"] "O")
let coq_succ = lazy (gen_constant ["Init"; "Datatypes"] "S")
let coq_nat = lazy (gen_constant ["Init"; "Datatypes"] "nat")

let rec coq_nat_of_int = function
  | 0 -> Lazy.force coq_zero
  | n -> mkApp (Lazy.force coq_succ, [| coq_nat_of_int (pred n) |])

(* let varify_constr_list ty def varh c = *)
(*   let vars = Idset.elements (freevars c) in *)
(*   let mkaccess i = *)
(*     mkApp (Lazy.force coq_List_nth, *)
(* 	  [| ty; coq_nat_of_int i; varh; def |]) *)
(*   in *)
(*   let l = List.fold_right (fun id acc -> *)
(*     mkApp (Lazy.force coq_List_cons, [| ty ; mkVar id; acc |])) *)
(*     vars (mkApp (Lazy.force coq_List_nil, [| ty |])) *)
(*   in *)
(*   let subst = *)
(*     list_map_i (fun i id -> (id, mkaccess i)) 0 vars *)
(*   in *)
(*     l, replace_vars subst c *)

let quote_path = ["quote";"Quote"]
let coq_varmap_empty = lazy (gen_constant quote_path "Empty_vm")
let coq_varmap_node = lazy (gen_constant quote_path "Node_vm")
let coq_varmap_lookup = lazy (gen_constant quote_path "varmap_find")

let coq_varmap_add = lazy (init_constant ["Reify";"Reify"] "varmap_add")

let coq_index_left = lazy (gen_constant quote_path "Left_idx")
let coq_index_right = lazy (gen_constant quote_path "Right_idx")
let coq_index_end = lazy (gen_constant quote_path "End_idx")

let rec split_interleaved l r = function
  | hd :: hd' :: tl' ->
      split_interleaved (hd :: l) (hd' :: r) tl'
  | hd :: [] -> (List.rev (hd :: l), List.rev r)
  | [] -> (List.rev l, List.rev r)

let rec mkidx i p =
  if i / 2 = 0 then
    if i = 0 then mkApp (Lazy.force coq_index_left, [|Lazy.force coq_index_end|])
    else mkApp (Lazy.force coq_index_right, [|Lazy.force coq_index_end|])
  else if i mod 2 = 0 then mkApp (Lazy.force coq_index_left, [|mkidx (i / 2) p|])
  else mkApp (Lazy.force coq_index_right, [|mkidx (i / 2) 0|])

let varify_constr_varmap ty def varh c =
  let vars = Idset.elements (freevars c) in
  let mkaccess i =
    mkApp (Lazy.force coq_varmap_lookup,
	  [| ty; def; i; varh |])
  in
  let rec vmap_aux l cont =
    match l with
    | [] -> [], mkApp (Lazy.force coq_varmap_empty, [| ty |])
    | hd :: tl ->
	let left, right = split_interleaved [] [] tl in
	let leftvars, leftmap = vmap_aux left (fun x -> cont (mkApp (Lazy.force coq_index_left, [| x |]))) in
	let rightvars, rightmap = vmap_aux right (fun x -> cont (mkApp (Lazy.force coq_index_right, [| x |]))) in
	  (hd, cont (Lazy.force coq_index_end)) :: leftvars @ rightvars,
	mkApp (Lazy.force coq_varmap_node, [| ty; hd; leftmap ; rightmap |])
  in
  let subst, vmap = vmap_aux (def :: List.map (fun x -> mkVar x) vars) (fun x -> x) in
  let subst = List.map (fun (id, x) -> (destVar id, mkaccess x)) (List.tl subst) in
    vmap, replace_vars subst c


TACTIC EXTEND varify
  [ "varify" ident(varh) ident(h') constr(ty) constr(def) constr(c) ] -> [
    let vars, c' = varify_constr_varmap ty def (mkVar varh) c in
      tclTHEN (letin_tac None (Name varh) vars None allHyps)
	(letin_tac None (Name h') c' None allHyps)
  ]
END

let hashtbl_elements h = Hashtbl.fold (fun x y l -> (x,y)::l) h []

let varmap_of_vars ty def v = 
  List.fold_left
    (fun vmap (i, idx, c) ->
       mkApp (Lazy.force coq_varmap_add, [| ty; c; vmap; idx |]))
    (mkApp (Lazy.force coq_varmap_empty, [| ty |])) v
    
let varify_constr_varmap map ty def varh evar c =
  let tbl = Hashtbl.create 1000 in
  let rec aux c =
    try mkApp (evar, [| pi2 (Hashtbl.find tbl c) |])
    with Not_found ->
      try Hashtbl.find map c
      with Not_found -> 
	try 
	  (match kind_of_term c with
	   | App (f, args) -> 
	       mkApp (Hashtbl.find map f, Array.map aux args)
	   | _ -> raise Not_found)
	with Not_found ->
	  let l = Hashtbl.length tbl in
	  let l' = succ l in
	  let idx = mkidx l' 0 in
	    Hashtbl.add tbl c (l', idx, c); 
	    mkApp (evar, [| idx |])
  in
  let c' = aux c in
  let vars = 
    List.sort (fun x y -> Pervasives.compare (pi1 (snd x)) (pi1 (snd y))) 
      (hashtbl_elements tbl) 
  in
  let vars = List.map snd vars in
    varmap_of_vars ty def vars, c'  

type reify_map = (constr * constr) list

let coq_constrs_list = lazy 
(*   (mkApp (Lazy.force coq_list_ind,  *)
(* 	  [|  *)
  (mkApp (Lazy.force coq_prod, [| Lazy.force coq_dynamic_ind;
				 Lazy.force coq_dynamic_ind |]))

let terms_of_dynamic c =
  match kind_of_term c with
  | App (f, args) when f = Lazy.force coq_dynamic_constr ->
      (args.(1), args.(0))
  | _ -> raise (Invalid_argument "term_of_dynamic")
  
let rec constrs_of_coq_dynamic_list c tbl = 
  match kind_of_term c with
  | App (f, args) when f = Lazy.force coq_list_nil -> tbl
  | App (f, args) when f = Lazy.force coq_list_cons && 
      eq_constr args.(0) (Lazy.force coq_constrs_list) && 
      Array.length args = 3 -> 
      (match kind_of_term args.(1) with
       | App (f, args') when f = Lazy.force coq_pair &&
	   Array.length args' = 4 ->
	   Hashtbl.add tbl (fst (terms_of_dynamic args'.(2))) (fst (terms_of_dynamic args'.(3)));
	     constrs_of_coq_dynamic_list args.(2) tbl
       | _ -> raise (Invalid_argument "constrs_of_coq_dynamic_list"))
  | _ -> raise (Invalid_argument "constrs_of_coq_dynamic_list")
      
(* let reify map c = *)
(*   let rec aux c = *)
(*     try List.assoc c map  *)
(*     with Not_found -> map_constr aux c *)
(*   in aux c *)

(* TACTIC EXTEND reify *)
(* [ "reify" ident(varh) ident(h') constr(ty) constr(def) constr(list) constr(evar) constr(c) ] -> [ *)
(*   let assoc = constrs_of_coq_dynamic_list list (Hashtbl.create 42) in *)
(*   let vars, c' = varify_constr_varmap evar assoc ty def (mkVar varh) c in *)
(*   let c'' = reify assoc c' in *)
(*     tclTHEN (letin_tac None (Name varh) vars None allHyps) *)
(*       (letin_tac None (Name h') c'' None allHyps) *)
(* ] *)
(* END *)

TACTIC EXTEND reify
[ "reify" ident(varh) ident(h') constr(ty) constr(def) constr(list) constr(evar) constr(c) ] -> [
  let assoc = constrs_of_coq_dynamic_list list (Hashtbl.create 42) in
  let vars, c' = varify_constr_varmap assoc ty def (mkVar varh) evar c in
    tclTHEN (letin_tac None (Name varh) vars None allHyps)
      (letin_tac None (Name h') c' None allHyps)
]
END

