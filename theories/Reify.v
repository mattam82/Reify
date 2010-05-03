Require Export Reify.Dynamic.
Require Import Quote.

Declare ML Module "reify_plugin".

Fixpoint varmap_add (A:Type) (a:A) (v:varmap A) (i:index) : varmap A :=
  match v, i with
    | Empty_vm, End_idx => Node_vm a (Empty_vm _) (Empty_vm _)
    | Empty_vm, Left_idx i =>
      Node_vm a (varmap_add A a (Empty_vm _) i) (Empty_vm _)
    | Empty_vm, Right_idx i =>
      Node_vm a (Empty_vm _) (varmap_add A a (Empty_vm _) i)
    | Node_vm a' l r, End_idx => Node_vm a l r
    | Node_vm a' l r, Left_idx i => Node_vm a' (varmap_add A a l i) r
    | Node_vm a' l r, Right_idx i => Node_vm a' l (varmap_add A a r i)
  end.
