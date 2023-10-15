From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* trect is the recursor or     *)
(* eliminator for the tree sort *)
Structure treeType : Type := {
  sort  :> Type; 
  type  :  Type;
  tnil  :  sort;
  tone  :  type -> sort;
  tcon  :  sort -> sort -> sort;
  trect :  forall P : sort -> Type,
           P tnil ->
           (forall t : type, P (tone t)) ->
           (forall s0 : sort,
            P s0 -> forall s1 : sort, P s1 -> P (tcon s0 s1)) ->
           forall s : sort, P s }.

Section TreeProp.

Variable A : treeType.

Definition S := sort A.
Definition T := type A.

(* lift of head from seq.v library.    *)
(* here, P would have been an implicit *)
(* but I had to declare it explicitly. *)
Definition bt_head (x0 : T) (s : S) : T :=
  trect (P := fun _ => T)
        x0
        (fun t => t) 
        (fun s0 h0 s1 h1 => h0) s.

End TreeProp.

Definition seq_one {T : Type} (t : T) := cons t nil.

Definition seq_rect (T : Type)
                    (P : seq T-> Type)
                    (p0 : P nil)
                    (p1 : forall t : T, P (seq_one t))
                    (p2 : forall s0 : seq T,
                     P s0 -> forall s1 : seq T, P s1 -> P (app s0 s1)) :=
  list_rect (A := T) P p0
            (fun t l p => p2 (seq_one t) (p1 t) l p). 


(* Build_treeType has a bunch of implicits,   *)
(* which is good. Only need to provide trect. *)
(* Note that I have to explicitly provide     *)
(* implicit argument T for mlist_rect.        *)
Definition listnat_treeType (T : Type) := 
  Build_treeType (seq_rect (T:=T)).
