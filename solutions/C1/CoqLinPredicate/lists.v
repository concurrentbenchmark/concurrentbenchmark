From mathcomp Require Import all_ssreflect.
From Coq Require Import Lists.List.


(* ————–—— Lists —–————–————–————–————– *)
Definition map_predn_filter :=
  fun l => (map predn) (filter (fun n => n > 0) l).

(* thanks to Alessandro Bruni for the proof *)
Lemma in_predn : forall (n : nat) (l : seq.seq nat),
    n.+1 \in l <-> n \in map predn (filter [eta leq 1] l).
Proof.
  move => n l.
  elim: l => [//|a l] => IH /=.
  case: ifP => a0; rewrite !inE; split.
  by move => /orP [/eqP <-|/=]; rewrite ?IH ?eq_refl// => ->; rewrite orbT.
  by move => /orP [/eqP ->|/=]; rewrite -?IH ?prednK ?eq_refl// => ->; rewrite orbT.
  by move: a0 => /[swap] /orP [/eqP <-|]; rewrite ?ltn0Sn// IH => ->.
  by rewrite -IH => ->; rewrite orbT.
Qed.

Lemma in_prednR : forall (n : nat) (l : seq.seq nat),
    n.+1 \in l -> n \in map predn (filter [eta leq 1] l).
Proof. 
  apply in_predn.
Qed. 

Lemma in_prednL : forall (n : nat) (l : seq.seq nat),
    n \in map predn (filter [eta leq 1] l) -> n.+1 \in l.
Proof. 
  apply in_predn.
Qed. 


Lemma not_in_prednR : forall (n : nat) (l : seq.seq nat),
    n.+1 \notin l -> 
    n \notin map predn (filter [eta leq 1] l).
Proof.
  move => n l.
  apply/contra => Hyp. 
  by apply/in_predn. 
Qed. 

Lemma not_in_prednL : forall (n : nat) (l : seq.seq nat),
    n \notin map predn (filter [eta leq 1] l) -> 
      n.+1 \notin l .
Proof.
  move => n l.
  apply/contra => Hyp. 
  by apply/in_predn. 
Qed. 
