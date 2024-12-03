From mathcomp Require Import all_ssreflect. 
From HB Require Import structures. 
From Coq Require Import Utf8.
From deriving Require Import deriving.  
(* start *)
Inductive sType : Type :=
| CloseT : sType
| WaitT  : sType
| InST   : sType -> sType -> sType
| OutST  : sType -> sType -> sType.

Notation "? T  ․ U" := (InST T U) (at level 44, right associativity).
Notation "! T  ․ U" := (OutST T U) (at level 44, right associativity).
(* end *)



Definition sType_indDef := [indDef for sType_rect].
Canonical sType_indType := IndType sType sType_indDef.

Definition sType_hasDecEq := [derive hasDecEq for sType].
HB.instance Definition _ := sType_hasDecEq.

Fixpoint dual t :=
  match t with 
  | CloseT => WaitT
  | WaitT => CloseT
  | InST  s' s => OutST s' (dual s)
  | OutST s' s => InST  s' (dual s)
  end. 

Lemma dual_dual_is_identinty : forall S, dual (dual S) = S. 
Proof.
  move => S; elim: S => //.
  move => S' H' S H /= ; by rewrite H. 
  move => S' H' S H /= ; by rewrite H. 
Qed. 

Lemma dual_inversion : forall S1 S2,
    dual S2 = S1  -> dual S1 = S2.
Proof.
  move => S1 S2 H.
  by rewrite -H dual_dual_is_identinty. 
Qed. 
