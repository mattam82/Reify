Require Import Coq.quote.Quote.
Require Import Reify Bvector.
Require Import List.
Notation dyn x := (@mkDynamic _ x).
Require Import Program.
Print End_idx.
Inductive prop : Set :=
| prop_true | prop_false | prop_conj (A B : prop) | prop_disj (A B : prop)
| prop_impl (A B : prop) | prop_var (n : index).

Definition prop_map :=
  [(dyn True, dyn prop_true);
   (dyn False, dyn prop_false);
   (dyn and, dyn prop_conj);
   (dyn or, dyn prop_disj);
   (dyn impl, dyn prop_impl)
  ].

Fixpoint interp (v : varmap Prop) (p : prop) : Prop :=
  match p with
    | prop_true => True
    | prop_false => False
    | prop_conj P Q => and (interp v P) (interp v Q)
    | prop_disj P Q => or (interp v P) (interp v Q)
    | prop_impl P Q => impl (interp v P) (interp v Q)
    | prop_var idx => varmap_find True idx v
  end.


Goal forall P : Prop, P /\ not P.
intros P.
match goal with
  |- ?T => 
    let l := eval cbv delta [prop_map] in prop_map in
      reify vars goal Prop True l prop_var T ; change (interp vars goal); subst goal
end.
  admit.
Defined.

Require Import ZArith.
Inductive expr : Set :=
| Evar (i : index)
| Emult (e e' : expr)
| Eplus (e e' : expr)
| Ecst (z : Z).

Open Scope Z_scope.

Fixpoint interpe (v : varmap Z) (p : expr) : Z :=
  match p with
    | Evar i => varmap_find 0 i v
    | Emult e e' => (interpe v e) * (interpe v e')
    | Eplus e e' => (interpe v e) + (interpe v e')
    | Ecst z => z
  end.

Definition expr_map :=
  [(dyn Z, dyn expr);
   (dyn (@eq), dyn (@eq));
   (dyn Z0, dyn (Ecst Z0));
   (dyn Zmult, dyn Emult);
   (dyn Zplus, dyn Eplus);
   (dyn 2, dyn (Ecst 2))
  ].

Ltac reifye :=
  match goal with
    |- ?T => 
      let vars := fresh "vars" in let goal' := fresh "goal'" in
      let l := eval cbv delta [expr_map] in expr_map in
        idtac "start reify"; 
        reify vars goal' Z 0 l Evar T;
        idtac "end reify" ;
          let reif := eval red in goal' in
          match reif with
            ?x = ?y => change (interpe vars x = interpe vars y); subst goal'
          end
  end.

Goal forall x y, x * y = x * y. 
intros. reifye.
reflexivity.
Qed.

Fixpoint test (zs : list Z) : Z :=
  match zs with
    | nil => 2
    | x :: l => let y := test l in
      (x * y) + (y * x)
  end.

Goal forall x1 x2 x3, test (x1 :: x2 :: x3 :: nil) = test (x3 :: x2 :: x1 :: nil).
Proof.
  intros. unfold test.
  Time reifye. 
Admitted.

Goal forall x1 x2 x3 x4 x5, test (x1 :: x2 :: x3 :: x4 :: x5 :: nil) = 
test (x5 :: x4 :: x3 :: x2 :: x1 :: nil).
Proof.
  intros. unfold test.
  Time reifye.
Admitted.


Goal forall x1 x2 x3 x4 x5 x1' x2' x3' x4' x5', 
  test (x1 :: x2 :: x3 :: x4 :: x5 :: x1' :: x2' :: x3' :: x4' :: x5' :: nil) = 
test (x5' :: x4' :: x3' :: x2' :: x1' :: x5 :: x4 :: x3 :: x2 :: x1 :: nil).
Proof.
  Set Printing Depth 14. 
  intros. unfold test.
  Time (reifye).
Admitted.

Goal forall x1 x2 x3 x4 x5 x1' x2' x3' x4' x5' x1'' x2'' x3'' x4'' x5'',
  test (x1 :: x2 :: x3 :: x4 :: x5 :: x1' :: x2' :: x3' :: x4' :: x5' :: x1'' :: x2'' :: x3'' :: x4'' :: x5'' :: nil) =
  test (x5'' :: x4'' :: x3'' :: x2'' :: x1'' :: x5' :: x4' :: x3' :: x2' :: x1' :: x5 :: x4 :: x3 :: x2 :: x1 :: nil).
Proof.
  intros. unfold test.
  Set Printing Depth 5.
  Time (reifye).
Admitted.
