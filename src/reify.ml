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

let gen_constant dir s = Coqlib.gen_constant "typeclass_tactics" dir s
let coq_List_nth = lazy (gen_constant ["Lists"; "List"] "nth")
let coq_List_cons = lazy (gen_constant ["Lists"; "List"] "cons")
let coq_List_nil = lazy (gen_constant ["Lists"; "List"] "nil")

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

let varify_constr_list ty def varh c =
  let vars = Idset.elements (freevars c) in
  let mkaccess i =
    mkApp (Lazy.force coq_List_nth,
	  [| ty; coq_nat_of_int i; varh; def |])
  in
  let l = List.fold_right (fun id acc ->
    mkApp (Lazy.force coq_List_cons, [| ty ; mkVar id; acc |]))
    vars (mkApp (Lazy.force coq_List_nil, [| ty |]))
  in
  let subst =
    list_map_i (fun i id -> (id, mkaccess i)) 0 vars
  in
    l, replace_vars subst c

let coq_varmap_empty =  lazy (gen_constant ["quote"; "Quote"] "Empty_vm")
let coq_varmap_node =  lazy (gen_constant ["quote"; "Quote"] "Node_vm")
let coq_varmap_lookup =  lazy (gen_constant ["quote"; "Quote"] "varmap_find")

let coq_index_left =  lazy (gen_constant ["quote"; "Quote"] "Left_idx")
let coq_index_right =  lazy (gen_constant ["quote"; "Quote"] "Right_idx")
let coq_index_end =  lazy (gen_constant ["quote"; "Quote"] "End_idx")

let rec split_interleaved l r = function
  | hd :: hd' :: tl' ->
      split_interleaved (hd :: l) (hd' :: r) tl'
  | hd :: [] -> (List.rev (hd :: l), List.rev r)
  | [] -> (List.rev l, List.rev r)

let rec mkidx i p =
  if i mod 2 = 0 then
    if i = 0 then mkApp (Lazy.force coq_index_left, [|Lazy.force coq_index_end|])
    else mkApp (Lazy.force coq_index_left, [|mkidx (i - p) (2 * p)|])
  else if i = 1 then mkApp (Lazy.force coq_index_right, [|Lazy.force coq_index_end|])
  else mkApp (Lazy.force coq_index_right, [|mkidx (i - p) (2 * p)|])

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
