Inductive ch : Type :=
    var_ch : nat -> ch.

Coercion var_ch : nat >-> ch.

Inductive proc : Type :=
  | EndP : proc
  | WaitP : ch -> proc -> proc
  | CloseP : ch -> proc -> proc
  | ResP : proc -> proc
  | ParP : proc -> proc -> proc
  | InSP : ch -> proc -> proc
  | DelP : ch -> ch -> proc -> proc.

Notation "∅" := EndP .
Infix "∥" := ParP (at level 48, left associativity).
Notation "α ? ․ p" := (InSP α p ) (at level 44, right associativity).
Notation "x ! y ․ p" := (DelP x y p ) (at level 44, right associativity).
Notation "(ν) p " := (ResP p) (at level 44, right associativity).
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Arith. 
(* write a function update of type (n : nat) (Delta : list X) (T : X): list X that updates the nth element of Delta with T *)
Fixpoint update {X : Type} (n : nat) (Delta : list X) (T : X) : list X :=
  match Delta with
  | [] => []
  | h :: t => if  n  =? 0 then T :: t else h :: update (n - 1) t T
  end.

(* write a function lookup of type (n : nat) (Delta : list X) : X that returns the nth element of Delta *)From Coq Require Import List.
