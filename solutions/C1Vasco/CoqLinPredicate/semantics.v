From mathcomp Require Import all_ssreflect.
Require Export LinearityPredicates.syntax.
Require Export LinearityPredicates.unscoped.
From Coq Require Import Lists.List.
Import ListNotations.


Definition shift_up := subst_proc (fun (x:nat) => var_ch (x.+1)).

Definition swap_ch (n1 n2 : nat) :=
  fun n => var_ch (if n == n1 then n2 else if n == n2 then n1 else n).
    
Inductive struct_eq  : proc -> proc -> Prop :=

| SC_Par_Com P Q     : struct_eq (ParP P Q) (ParP Q P) 

| SC_Par_Assoc P Q R : struct_eq (ParP (ParP P Q) R) 
                         (ParP P (ParP Q R))

| SC_Par_Inact P     : struct_eq (ParP P EndP) P

| SC_Res_Scope P Q   : struct_eq (ParP (ResP P) Q) 
                         (ResP (ParP  P (shift_up (shift_up Q))))

| SC_Res_Inact       : struct_eq (ResP EndP) EndP

| SC_Res_SwapC P     : struct_eq (ResP P ) (ResP (subst_proc (swap_ch 0 1) P))

| SC_Res_SwapB P     : struct_eq (ResP (ResP P )) 
                         (ResP (ResP (subst_proc (swap_ch 1 3) 
                                        (subst_proc (swap_ch 0 2) P)) ))

(* equivalence rules *) 
| SC_Refl P          : struct_eq P P
| SC_Sym P Q         : struct_eq P Q -> struct_eq Q P
| SC_Trans P Q R     : struct_eq P Q -> struct_eq Q R -> struct_eq P R

 (* congruence rules*)
| SC_Cong_Par P P' Q Q'  : struct_eq P P' -> struct_eq Q Q' -> struct_eq (ParP P Q) (ParP P' Q')
| SC_Cong_Res P P'       : struct_eq P P' -> struct_eq (ResP P) (ResP P')
| SC_Cong_Close P P' x   : struct_eq P P' -> struct_eq (CloseP x P) (CloseP x P')
| SC_Cong_Wait P P' x    : struct_eq P P' -> struct_eq (WaitP x P) (WaitP x P')
| SC_Cong_OutS P P' x  y : struct_eq P P' -> struct_eq (DelP x y P) (DelP x y P')
| SC_Cong_InsP P P' x    : struct_eq P P' -> struct_eq (InSP x  P) (InSP x  P')

.

Notation   "P '≅' Q" := (struct_eq P Q) (at level 60, right associativity).

(* MARCO: DOESN't COMPILE *)
(* (** setoid registration, perhaps redundant with ssr *) *)
(* Theorem Congoid : Setoid_Theory _ struct_eq. *)
(*  split. *)
(*  exact SC_Refl. *)
(*  exact SC_Sym. *)
(*  exact SC_Trans. *)
(* Qed. *)

(* Add Setoid proc  struct_eq Congoid as Cong_register. *)

Inductive reduce : proc -> proc -> Prop :=
| R_Res P Q          : reduce P Q ->
                       reduce (ResP P) (ResP Q)

| R_Par P Q R        : reduce P Q ->
                       reduce (ParP P R) (ParP Q R)

| R_Struct P P' Q Q' : struct_eq P P' ->
                       reduce P' Q' ->
                       struct_eq Q' Q ->
                       reduce P Q 

| R_Close P Q:        
  reduce (ResP (ParP (CloseP (var_ch 1) P) 
                  (WaitP (var_ch 0)   Q) ))
    (ResP (ParP P Q))

| R_Del x P Q:        
  reduce (ResP (ParP (DelP (var_ch 1) x P) 
                  (InSP (var_ch 0)   Q) ))
    (ResP (ParP P (subst_proc (scons x ids) Q) ))
.


Notation " P '⇛' Q " := (reduce P Q) (at level 50, left associativity).  
