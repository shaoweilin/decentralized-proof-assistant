From mathcomp Require Import all_ssreflect.

(* sorry i'm using an older version of coq 
and ssreflect as i'm too lazy to update *)

(* note that i'm working with non-empty trees
to make things simpler but it is not hard to
add considerations for empty trees *)



(* lift of list nat*)
Inductive bin_tree :=
| bt_one  : nat -> bin_tree
| bt_cons : bin_tree -> bin_tree -> bin_tree.

(* lift of hd *)
Fixpoint bt_head (t : bin_tree) : nat :=
match t with
| bt_one x => x
| bt_cons l r => bt_head l
end.

Print bt_head.

(* lift of last *)
Fixpoint bt_tail (t : bin_tree) : nat :=
match t with
| bt_one x => x
| bt_cons l r => bt_tail r
end. 

(* lift of sorted leq *)
Fixpoint bt_sorted (t : bin_tree) : bool :=
match t with
| bt_one x => true
| bt_cons l r => 
    leq (bt_tail l) (bt_head r)
    && bt_sorted r && bt_sorted l
end.

(* lift of count_mem *)
Fixpoint bt_count_mem (x : nat) (t : bin_tree) : nat :=
match t with
| bt_one y => if x == y then S O else O
| bt_cons l r => bt_count_mem x l + bt_count_mem x r
end.

(* lift of all *)
Fixpoint bt_all (p : pred nat) (t : bin_tree) : bool :=
match t with
| bt_one x => p x
| bt_cons l r => bt_all p l && bt_all p r
end.

(* lift of perm_eq *)
Definition bt_perm_eq (s : bin_tree) (t : bin_tree) : bool :=
bt_all (fun x => bt_count_mem x s == bt_count_mem x t) (bt_cons s t).

Theorem bt_sort_spec : forall (s : bin_tree),
{t : bin_tree & bt_sorted t & bt_perm_eq s t}.
Proof.
intro s.
induction s.
- exists (bt_one n). auto. 
-- unfold bt_perm_eq. unfold bt_all. simpl. destruct (n==n). auto. auto.
Admitted.

