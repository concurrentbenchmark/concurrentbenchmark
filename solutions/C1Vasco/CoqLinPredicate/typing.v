From mathcomp Require Import all_ssreflect.
Require Export linearity_predicate.
Require Export types.
Require Export syntax.
(* Require Export env. *)
From HB Require Import structures.
From deriving Require Import deriving. 
From Coq Require Import Lists.List. 
From mathcomp Require Import seq. 

(* Environment business *) 
Definition env := seq sType.

Definition lookup (n : nat) (Delta : env) : option sType :=
  nth None (map some Delta) n.

Definition upd (n : nat) (Delta : env) (T : sType) : env :=
  take n Delta ++ [:: T] ++ drop n.+1 Delta.

Fixpoint update_seq {X : Type} (n : nat) (Delta : seq X) (T : X) : seq X :=
  match Delta with
  | [::] => [::]
  | h :: t => if n == 0 then T :: t else h :: update_seq (n.-1) t T
  end.


(* Typing judgement *) 
Inductive OFT : env -> proc -> Prop :=
| TEndP Delta       : 
  OFT Delta EndP
| TWaitP Delta x P  : 
  lookup (ch_index x) Delta = Some (WaitT) -> 
  OFT Delta P -> 
  OFT Delta (WaitP x P)
| TCloseP Delta x P : 
  lookup (ch_index x) Delta = Some (CloseT) -> 
  OFT Delta P -> 
  OFT Delta (CloseP x P)
| TParP Delta P1 P2  : 
  OFT Delta P1 ->
  OFT Delta P2 ->
  OFT Delta (ParP P1 P2)
| TResP Delta (S:sType) P : 
  lin (var_ch 0) P ->
  lin (var_ch 1) P ->
  OFT (S::(dual S)::Delta) P -> 
  OFT Delta (ResP P)
| TInSP Delta (x:ch) (S:sType) (T:sType) P :
  lookup (ch_index x) Delta = Some (InST T S) -> 
  lin (var_ch 0) P -> 
  OFT (T::(upd (ch_index x) Delta S)) P -> 
  OFT Delta (InSP x P)
| TDelP Delta x (S:sType) y (T:sType) P : 
  lookup (ch_index x) Delta = Some (OutST T S) -> 
  lookup (ch_index y) Delta = Some T -> 
  OFT (upd (ch_index x) Delta S) P -> 
  OFT  Delta (DelP x y P).

Notation "Γ ⊢ P" := (OFT Γ P) (at level 40).

(* Substitution *)

Definition is_perm sigma Delta1 Delta2 := forall n, 
    n < length Delta1 ->
    lookup n Delta1 = lookup (ch_index(sigma n)) Delta2.


Lemma lookup_subst : forall m sigma Delta1 Delta2,
    m < length Delta1 -> 
    is_perm sigma Delta1 Delta2 -> 
    lookup m Delta1 = lookup (ch_index (sigma m)) Delta2.
Proof.
  move => m sigma Delta1 Delta2 H.
  by apply.
Qed. 



Lemma substitution : forall sigma Delta1 Delta2 P,
    is_perm sigma Delta1 Delta2 -> 
    OFT Delta1 P ->
    OFT Delta2 (subst_proc sigma P). 
Proof.
  move => sigma Delta1 Delta2 P; elim: P sigma Delta1 Delta2.
  - constructor.
  - move => [m] P IH sigma Delta1 Delta2 H1 H2 /=.
    inversion H2; subst.
    apply/TWaitP.
    rewrite -(lookup_subst _ _ Delta1). 
    by rewrite -H4.

    admit. (* needed a substitution lemma for contexts *)
    apply/(IH _ Delta1) => //.
  - move => [m] P IH sigma Delta1 Delta2 H1 H2 /=.
    inversion H2; subst.
    apply/TCloseP.
    admit. (* needed a substitution lemma for contexts *)
    apply/(IH _ Delta1) => //.
  - move => P IH sigma Delta1 Delta2 H1 H2 /=.
    inversion H2; subst.
    apply/(TResP _ S).
    admit.
    admit.
    apply/(IH); last first.
    apply/H5.
    admit. (* here substitution for is_perm *)
  - move => P IH1 Q IH2 sigma Delta1 Delta2 H1 H2 /=.
    inversion H2; subst. 
    apply/TParP. 
    apply/(IH1 _ Delta1) => //.
    apply/(IH2 _ Delta1) => //.
  - move => [m] P IH sigma Delta1 Delta2 H1 H2 /=.
    inversion H2; subst.
    apply/(TInSP _ _ T S) => //.
    admit. (* needed a substitution lemma for contexts *)
    apply/(lin_subst 0) => //.
    apply/injectiveNS_up_ch_ch_0.
    apply/IH; last first. 
    apply/H6.
    admit. 
  - move => c c0 P IH sigma Delta1 Delta2 H1 H2 /=.
    inversion H2; subst. 
    apply/TDelP; last first. 
    apply/IH; last first. 
    apply/H7.
    admit. 
    admit. 
    admit. 
    




    



(* Lemma substitution : forall (T:sType) Delta P, *)
(*     OFT Delta P -> OFT (T::Delta) (shift_up P). *)
(* Proof. *)
(*   move => T Delta P; elim: P T Delta. *)
(*   - constructor. *)
(*   - move => [m] P IH T Delta H. *)
(*     inversion H; subst. *)
(*     rewrite/shift_up => /=. *)
(*     apply/TWaitP.  *)
(*     admit.  *)
(*     by apply/IH. *)
(*   - admit.  *)

(*   - move => P IH T Delta H. *)
(*     inversion H; subst. *)
(*     rewrite/shift_up => /=. *)
(*     apply/(TResP _ S).  *)
(*     admit. *)
(*     admit.  *)
(*     asimpl.  *)
(*     rewrite/core.funcomp/shift/scons. simpl. *)
(*     have fact: subst_proc (fun n =>  *)
(*                              match n with *)
(*                              | 0 => var_ch 0 *)
(*                              | 1 => var_ch 1 *)
(*                              | n1.+2 => var_ch n1.+3 *)
(*                              end) P *)
(*                =  *)

(*     constructor => //. *)
    
(*     apply/IH => //. *)
(*     move:H2. *)
(*     by rewrite in_cons negb_or => /andP; case. *)
(*   - move => [m] P IH T Delta => /= => H1 H2. *)
(*     inversion H1; subst. *)
(*     rewrite/shift_up => /=. *)
(*     constructor => //. *)
(*     apply/IH => //. *)
(*     move:H2. *)
(*     by rewrite in_cons negb_or => /andP; case. *)
(*   - move => P IH T Delta Hyp1 /=.  *)
(*     inversion Hyp1; subst. *)
(*     move/not_in_prednL/not_in_prednL => Hyp2.  *)
(*     rewrite/shift_up => /=.  *)
(*     apply/(TResP _ S). *)
(*     apply/lin_subst.  *)
(*     apply/H0. *)
(*     apply/injectiveNS_up_ch_ch_0. *)
(*     auto. *)
(*     apply/lin_subst.  *)
(*     apply/H1. *)
(*     apply/injectiveNS_up_ch_ch_1. *)
(*     auto. *)
 
(*     asimpl. *)
(*     rewrite/core.funcomp/scons/shift => /=.  *)
    
    
    


Theorem subject_congruence : forall P Q Delta,
    struct_eq P Q -> OFT Delta P <-> OFT Delta Q. 
Proof.
  move => P Q Delta H; elim: H Delta.
  - split.
    move => H.
    inversion H; subst. 
    constructor => //. 
    move => H. 
    inversion H; subst. 
    constructor =>//. 
  - split.
    move => H. 
    inversion H; subst.
    inversion H3; subst. 
    constructor =>//. 
    constructor =>//. 
    move => H. 
    inversion H; subst.
    inversion H4; subst. 
    constructor =>//. 
    constructor =>//. 
  - split.
    move => H; inversion H =>//.
    move => H. 
    constructor => //. 
    constructor. 
  - split.
    { move => H'.
      inversion H'; subst => {H'}. 
      inversion H2; subst => {H2}.
      apply/(TResP _ S). 
      + apply/LParPL =>//=.
        apply/free_ch_0_shift.
      + apply/LParPL =>//=.
        apply/free_ch_1_shift.
      + apply/TParP => //.
        * rewrite/shift_up.
          asimpl. 
          rewrite/core.funcomp. 
          asimpl.
          apply/weakening. 
          

          rewrite/shift_up.
          asimpl. 
          rewrite/core.funcomp. 
          asimpl.
          apply/weakening. 
          apply/weakening.
          apply/substitution_aux => //.
          move: (free_ch_1_shift Q0).
          rewrite/shift_up.
          asimpl.
          rewrite/funcomp.
          by asimpl.
          move: (free_ch_0_shift (shift_up Q0)).
          rewrite/shift_up.
          asimpl.
          rewrite/funcomp.
          by asimpl. 
    }
    { 
      move => H'.
      inversion H'; subst => {H'}. 
      inversion H4; subst => {H4}.
      apply/TPar. 
      + apply/(TRes _ _ S). 
        * inversion H0; subst => //.
          by apply/not_in_fn_linear. 
        * inversion H1; subst => //.
          by apply/not_in_fn_linear. 
        * apply/H6.
      + apply weakening_inv in H7.
        apply weakening_inv in H7.
        move:H7.
        rewrite/shift_up.
        asimpl => /=.
        rewrite/funcomp; asimpl.
        set incr2 := (fun x => var_ch (x.+2)) => H.
        apply/(substitution_inv _ _ _ _ incr2).
        apply/injective_incr2. 
        apply/H.
        auto.
        apply/free_ch_1_shift. 
        apply/free_ch_0_shift. 
    }
  - split. 
    constructor.
    move => H. 
    apply/(TRes _ _ EndT). 
    constructor. 
    constructor. 
    constructor. 
  - by [].
  - move => P0 Q0 Heq IH Gamma Delta.
    by apply iff_sym.
  - move => P0 Q0 R Heq1 H1 Heq2 H2 Gamma Delta.
    move: (H1 Gamma Delta) (H2 Gamma Delta); apply iff_trans.
Qed. 


Lemma OFT_resbound_lin: forall P Gamma Delta,
    OFT Gamma Delta P -> all_bound_lin P.
Proof. 
  move => P; elim: P. 
  - constructor. 
  - move => P IH Gamma Delta H. 
    inversion H; subst; constructor => //; apply/IH/H5.
  - move => P IH1 Q IH2 Gamma Delta H.    
    inversion H; subst; constructor. 
    * apply/IH1/H4.
    * apply/IH2/H5.
  - move => c P IH Gamma Delta H. 
    inversion H; subst; constructor; apply/IH/H5.
  - move => c v P IH Gamma Delta H. 
    inversion H; subst; constructor; apply/IH/H7.
  - move => c P IH Gamma Delta H. 
    inversion H; subst; constructor.
    apply/IH/H6. 
    apply/H5.
  - move => c c0 P IH Gamma Delta H. 
    inversion H; subst; constructor.
    apply/IH/H7. 
Qed.

Lemma subject_reduction_R_Com1: 
  forall v P Q Gamma Delta, 
    OFT Gamma Delta
      (ResP
         (ParP (OutP (var_ch 1) v P) 
            (InP (var_ch 0) Q))) ->
    OFT Gamma Delta
      (ResP (ResP (ParP P (subst_val0 v Q)))). 
Proof.
  move => v P Q Gamma Delta H. 
  inversion H; subst. 
  apply/(TRes _ _ S).
  (* prove lin 0 (ResP ( P  || Q[v/0])) *)
  - constructor => /=.
    inversion H1;subst.      
    (* Linear ParL *)
    + apply/LParL. 
      inversion H6; subst. 
      apply/H10.
      move:H7 => //.
    (* Linear ParR *)
    + apply/LParR. 
      * move:H6 => /=.
        rewrite seq.in_cons Bool.negb_orb => /=.
        by move/not_in_prednL/not_in_prednL.
      * inversion H7;subst. 
        apply/lin_subst_val. 
        move: H3 =>  //=. 
        apply/not_in_fn_linear.
        move:H8; rewrite/not => //. 
  (* prove lin 1 (ResP ( P  || Q[v/0])) *)
  - constructor => /=.
    inversion H2;subst. 
    (* Linear ParL *) 
    + apply/LParL.
      * inversion H6;subst. 
        move:H4 => /=.
        apply/not_in_fn_linear.
        move:H8; rewrite/not => //.
      * move:H7 => /=.
        rewrite seq.in_cons Bool.negb_orb => /=. 
        move/not_in_prednL/not_in_prednL. 
        by rewrite free_ch_subst_val_inv. 
    + apply/LParR. 
      * by move:H6 => /=.
      * inversion H7;subst.
        by move:H8; rewrite/not.
  (* prove ResP ( P Q[v/0]) is typable *)
  - inversion H5; subst => {H5}.
    inversion H7; subst => {H7}.
    inversion H8; subst => {H8}.    
    have fact: S = InT S1. 
    { move: H6. 
      rewrite seq.in_cons.
      move/orP.
      case. 
      move/eqP.
      by case. 
      rewrite seq.in_cons; move/orP; case.
      discriminate. 
      by move/sEnv_0_not_in_shift_up. }      
    subst. 
    have fact: S0 = dual S1. 
    { move: H10. 
      rewrite seq.in_cons.
      move/orP.
      case. 
      move/eqP.
      by case. 
      rewrite seq.in_cons; move/orP; case.
      move/eqP.
      by case. 
      by move/sEnv_1_not_in_shift_up. }      
    subst. 
    apply/(TRes _ _ S1).
    {
      inversion H1;subst => {H1}.
      - inversion H5; subst => {H5}.
        move:H4; by rewrite/not.
      - inversion H2; subst => {H2}.
        + inversion H8; subst => {H8}.
          apply/LParR. 
          inversion H4; subst => {H4}. 
          apply/H15.
          move:H14; by rewrite/not. 
          by apply/lin_subst_val.
          move:H3; by rewrite/not.
        + inversion H12; subst => {H12}.
          move:H3; by rewrite/not. 
    }
    {
      inversion H2;subst => {H2}.
      - inversion H1; subst => {H1}.
        + inversion H4; subst => {H4}.
          move:H3; by rewrite/not. 
          apply/LParL => {H8 H4}. 
          inversion H5; subst => {H5} //. 
          inversion H12; subst => {H12} => /=.
          by rewrite free_ch_subst_val_inv.
          move:H3; by rewrite/not.
      - inversion H8; subst => {H8}.
        move:H4; by rewrite/not.
    }
    {
      apply/TPar. 
      - move:H11.
        rewrite dual_dual_is_identinty.
        apply.
      - apply/(dEnv_like_a_set v) => //.
        move:H7.
        rewrite/subst_val0.        
        have fact: 
            [:: v] ++ Gamma = 
              subst_dEnv (scons v var_val) 
                ([:: var_val 0] ++
                   subst_dEnv 
                   (fun n => var_val (n.+1)) Gamma).
        simpl.
        f_equal.
        by rewrite subst_dEnv_scons_id.
        rewrite fact. 
        apply/substitution_val.
    }
Qed.

Lemma subject_reduction_R_Com2: 
  forall v P Q Gamma Delta, 
    OFT Gamma Delta
      (ResP
         (ParP (OutP (var_ch 0) v P) 
            (InP (var_ch 1) Q))) ->
    OFT Gamma Delta
      (ResP (ResP (ParP P (subst_val0 v Q)))). 
Proof.
  move => v P Q Gamma Delta H. 
  inversion H;subst. 
  apply/(TRes _ _ S).
  (* prove lin 0 (ResP ( P  || Q[v/0])) *)
  - constructor => /=.
    inversion H1;subst.      
    (* Linear ParL *)
    + apply/LParL. 
      inversion H6; subst. 
      move:H4 => /=.
      apply/not_in_fn_linear.
      move:H8 => //.
      move:H7 => /=.
      rewrite seq.in_cons Bool.negb_orb => /=.
      move/not_in_prednL/not_in_prednL.
      by rewrite  free_ch_subst_val_inv.
    (* Linear ParR *)
    + apply/LParR. 
      * by move:H6 => /=.
      * inversion H7;subst. 
        apply/lin_subst_val. 
        move: H9; rewrite/ch_shift_up => //=; rewrite !addn1. 
  (* prove lin 1 (ResP ( P  || Q[v/0])) *)
  - constructor => /=.
    inversion H2;subst. 
    (* Linear ParL *) 
    + apply/LParL.
      * inversion H6;subst. 
        move:H8 => //. 
      * move:H7 => //=.
    + apply/LParR. 
      * move:H6 => /=.
      rewrite seq.in_cons Bool.negb_orb => /=.
      by move/not_in_prednL/not_in_prednL.
      * inversion H7;subst.
        apply/lin_subst_val.
        move:H3 => /=.
        apply/not_in_fn_linear.
        move:H8 => //.
  (* prove ResP ( P Q[v/0]) is typable *)
  - inversion H5; subst => {H5}.
    inversion H7; subst => {H7}.
    inversion H8; subst => {H8}.    
    have fact: dual S = InT S1. 
    { 
      move: H6 => /=. 
      rewrite seq.in_cons.
      move/orP.
      case. 
      move/eqP.
      by case. 
      rewrite seq.in_cons; move/orP; case.
      move/eqP => Hyp.
      inversion Hyp => //.
      by move/sEnv_1_not_in_shift_up. }      
    move:fact.
    move/dual_inversion => fact.
    subst.
    have fact: S0 = dual S1. 
    { move: H10. 
      rewrite seq.in_cons.
      move/orP.
      case. 
      move/eqP.
      by case. 
      rewrite seq.in_cons; move/orP; case.
      move/eqP.
      by case.
      by move/sEnv_0_not_in_shift_up. }      
    subst. 
    apply/(TRes _ _ S1).
    {
      inversion H1;subst => {H1 H H9 H7 H6 H10 H11 S1 Gamma Delta}.
      - inversion H2; subst => {H2}.
        + inversion H3; subst => {H3}.
          move:H2 => //.
        + inversion H5; subst => {H5}.
          apply/LParR. 
          by apply H6.
          inversion H4; subst => {H4}. 
          by apply/lin_subst_val.
          move:H5 => //.
          move:H2 => //.
      - inversion H8;subst => {H8}.
        move:H3 => //. 
    }
    {
      inversion H2; subst => {H H9 S1 H7 H6 H10 H11 Gamma Delta}.
      - inversion H5; subst.
        move: H4 => //.
      - inversion H1; subst => {H1}.
        + inversion H8; subst => {H8}.
          inversion H4; subst => {H4}.
          apply/LParL => //=.
          by rewrite free_ch_subst_val_inv.
          move:H9 => //.
          move: H3 => //.
        + inversion H6.
          move:H3 => //.
    }
    {
      apply/TPar. 
      - move:H11.
        rewrite dual_dual_is_identinty.
        apply.
      - apply/(dEnv_like_a_set v) => //.
        move:H7.
        rewrite/subst_val0.        
        have fact: 
          [:: v] ++ Gamma = 
            subst_dEnv (scons v var_val) 
              ([:: var_val 0] ++
                 subst_dEnv 
                 (fun n => var_val (n.+1)) Gamma).
        simpl.
        f_equal.
        by rewrite subst_dEnv_scons_id.
        rewrite fact. 
        apply/substitution_val.
    }
Qed. 

Lemma lin_reduction_R_Del1_0: forall x P Q,
    lin (var_ch 0) (ParP (DelP (var_ch 1) x P) (InSP (var_ch 0) Q)) 
    -> 
      lin (var_ch 2) (ParP P (subst_ch2 x Q)).
Proof. 
  move => [n] P Q H. 
  inversion H; subst. 
  - (* LParL *)  
    move:H4 => /=; discriminate. 
  - (* LParR *)  
    move:H3 => /=.
    rewrite seq.in_cons Bool.negb_orb seq.in_cons Bool.negb_orb.
    move/andP; case => _; move/andP; case => MyH1. 
    (repeat move/not_in_prednL) => MyH2. 
    apply/LParR => //.
    inversion H4; subst. 
    * rewrite/subst_ch2/scons2; asimpl.
      apply/(lin_subst 3).
      apply/not_in_fn_linear => //.
      by apply/injectiveNS_scons2_n.
      auto.
    * by move: H3; case.
Qed. 

Lemma lin_reduction_R_Del1_1: forall x P Q,
    lin (var_ch 1) (ParP (DelP (var_ch 1) x P) (InSP (var_ch 0) Q)) 
    -> 
      lin (var_ch 3) (ParP P (subst_ch2 x Q)).
Proof. 
  move => [n] P Q H. 
  inversion H; subst. 
  - (* LParL *)
    apply/LParL. 
    * inversion H3;subst. 
      by apply/not_in_fn_linear. 
      move:H5 => //; move:H6 => //.
      move:H6 => //.
    * inversion H3; subst. 
      + move:H4 => /=.
        rewrite seq.in_cons Bool.negb_orb.
        move/andP; case => _. 
        repeat move/not_in_prednL.
        apply/contra => Hyp; apply/free_ch_subst.
        apply/Hyp.
        apply/injectiveNS_scons2_n.
        move:H2 => /eqP => //.
      + move:H5 => //.
      + move:H6 => //.
  - (* LParR *)
    apply/LParR => //. 
Qed. 

Lemma lin_reduction_R_Del2_0: forall x P Q,
    lin (var_ch 0) (ParP (DelP (var_ch 0) x P) (InSP (var_ch 1) Q)) 
    -> lin (var_ch 2) (ParP P (subst_ch2 x Q)).
Proof. 
  move => [n] P Q H. 
  inversion H; subst. 
  - (* LParL *)  
    apply/LParL.
    * inversion H3;subst. 
      by apply/not_in_fn_linear. 
      move:H5 => //; move:H6 => //.
      move:H6 => //.
    * inversion H3; subst. 
      + move:H4 => /=.
        rewrite seq.in_cons Bool.negb_orb.
        move/andP; case => _. 
        repeat move/not_in_prednL.
        apply/contra => Hyp; apply/free_ch_subst.
        apply/Hyp.
        apply/injectiveNS_scons2_n.
        move:H2 => /eqP => //.
      + move:H5 => //.
      + move:H6 => //.
  - (* LParR *)
    apply/LParR => //. 
Qed. 

Lemma lin_reduction_R_Del2_1: forall x P Q,
    lin (var_ch 1) (ParP (DelP (var_ch 0) x P) (InSP (var_ch 1) Q)) 
    -> lin (var_ch 3) (ParP P (subst_ch2 x Q)).
Proof. 
  move => x P Q H. 
  inversion H; subst. 
  - (* LParL *)  
    move:H4 => /=; discriminate. 
  - (* LParR *)  
    destruct x. 
    move:H3 => /=.
    rewrite seq.in_cons Bool.negb_orb seq.in_cons Bool.negb_orb.
    move/andP; case => _; move/andP; case => MyH1. 
    (repeat move/not_in_prednL) => MyH2. 
    apply/LParR => //.
    inversion H4; subst. 
    * apply/(lin_subst 4).
      move:H1 => /=.
      apply/not_in_fn_linear => //.
      by apply/injectiveNS_scons2_n.
      auto.
    * by move: H3; case.
Qed. 

Lemma subject_reduction_R_Del1: forall x P Q Gamma Delta, 
    OFT Gamma Delta
      (ResP (ParP (DelP (var_ch 1) x P) (InSP (var_ch 0) Q))) ->
    OFT Gamma Delta (ResP (ResP (ParP P (subst_ch2 x Q)))). 
Proof.
  move => [n] P Q Gamma Delta H. 
  inversion H; subst. 
  apply/(TRes _ _ S).
  - by constructor; apply/lin_reduction_R_Del1_0.
  - by constructor; apply/lin_reduction_R_Del1_1.
  - inversion H5; subst => {H H5}. 
    inversion H7; subst => {H7}. 
    inversion H8; subst => {H8}.
    have fact: S = InST T0 S1.
    { move:H3;rewrite seq.in_cons; move/orP;case. 
      by move/eqP; case.
      rewrite seq.in_cons; move/orP; case => //.
      by move/sEnv_0_not_in_shift_up. }
    subst.  
    have fact: S0 = dual S1. 
    { move: H6;rewrite seq.in_cons;  move/orP; case.  
      by move/eqP; case.  
      rewrite seq.in_cons; move/orP; case. 
      by move/eqP; case.  
      by move/sEnv_1_not_in_shift_up. }       
    subst.  
    have fact: T = T0. 
    { move: H6;rewrite seq.in_cons;  move/orP; case.  
      by move/eqP; case.  
      rewrite seq.in_cons; move/orP; case. 
      by move/eqP; case.  
      by move/sEnv_1_not_in_shift_up. }       
    subst.  
    apply/(TRes _ _ S1). 
    * inversion H1; subst=>{H1 S1 T0 H3 H10 H9 H6 H11 Gamma Delta}.
     + move:H8 => //.
     + move:H5 => /=.
       rewrite seq.in_cons Bool.negb_orb seq.in_cons Bool.negb_orb.
       move/andP; case => _; move/andP; case => Hneq. 
       (repeat move/not_in_prednL) => Hyp. 
       inversion H8;subst => {H8}. 
       inversion H2;subst => {H2}.
       inversion H6;subst => {H6}.
       apply/LParR.
       apply/H10.
       apply/(lin_subst 0) => //.
       apply/injectiveNS_scons2_0.
       move:H5 => //.
       move:H9 => //.
       move:H6 => //.
       move:H3 => //. 
    * inversion H2;subst=>{H2 S1 T0 H3 H10 H9 H6 H11 Gamma Delta}.
     + inversion H5;subst => {H5}.
       inversion H1;subst => {H1}.
       apply/LParL => //=.
       apply/LParL => //=.
       inversion H10;subst => {H10}.
       have fact:  forall n y sigma P,  (* reformulate free_ch_subst *)
           injectiveNS n (free_ch P) sigma -> 
           n \notin free_ch P -> 
           y = ch_index (sigma n) ->
           y \notin free_ch (subst_proc var_val sigma P). 
       { move => n0 y sigma P0 Hfact1 Hfact Hfact2.
         move:Hfact.
         apply/contra => Hfact.
         apply/free_ch_subst; subst.
         apply/Hfact.
         apply/Hfact1. 
       }
       apply/(fact 1). 
       apply/injectiveNS_scons2_1.
       apply/H1.
       by asimpl;auto.
       move:H4 => //.
       move:H3 => //.
       move:H4 => //.
     + move:H5 => //.
    * move => {H1 H2 H7}. (* cleaning up *)
      apply/TPar. 
      + by move:H10; rewrite dual_dual_is_identinty.
      + move: H11 => /= => Hyp.
        apply/(sessEnv_like_a_set_2 (var_ch n.+2) T0). 
        move:H9.
        rewrite !seq.in_cons. 
        move/orP; case.
        move/eqP; case => H' H''; subst.
        apply/orP; right; apply/orP; right; apply/orP; left.
        apply/eqP; f_equal => //.
        move/orP; case.
        move/eqP; case => H' H''; subst.
        apply/orP;right;apply/orP;right;apply/orP;right;apply/orP;left.
        apply/eqP; f_equal => //.
        move => H {Hyp H6 H10 H3}. 
        apply/orP;right;apply/orP;right;apply/orP;right;apply/orP;right.
        have fact: forall c c' sT sigma Delta, 
            (c, sT) \in Delta -> c' = subst_ch sigma c -> 
            (c', sT) \in subst_sEnv sigma Delta.
        move => c c' sT sigma Env Hyp1 Hyp2. 
        by subst; apply/sEnv_subst.
        apply/fact. 
        apply/H.
        by simpl.
        apply/(exchange _ _ _ []) => /=. 
        apply/(exchange _ _ _ [(var_ch 0, S1)]) => /=. 
        apply/substitution.
        apply/Hyp.
        simpl.
        f_equal; f_equal; f_equal; f_equal; f_equal.
        move => {Hyp H9 H6 H10 H3}.
        elim:Delta => //.
        move => [[k] s] l IH => /=. 
        by f_equal.
Qed.        

Lemma subject_reduction_R_Del2: forall x P Q Gamma Delta, 
    OFT Gamma Delta 
      (ResP (ParP (DelP (var_ch 0) x P) (InSP (var_ch 1) Q)))
    ->
      OFT Gamma Delta (ResP (ResP (ParP P (subst_ch2 x Q)))). 
Proof.
  move => [n] P Q Gamma Delta H. 
  inversion H; subst. 
  apply/(TRes _ _ S).
  - by constructor; apply/lin_reduction_R_Del2_0.
  - by constructor; apply/lin_reduction_R_Del2_1.
  - inversion H5; subst => {H H5}. 
    inversion H7; subst => {H7}. 
    inversion H8; subst => {H8}.
    have fact: S = OutST T S0.
    { move:H6;rewrite seq.in_cons; move/orP;case.
      by move/eqP; case.
      rewrite seq.in_cons; move/orP; case => //.
      by move/sEnv_0_not_in_shift_up. }
    subst.
    have fact: S0 = dual S1.
    { move: H3;rewrite seq.in_cons;  move/orP; case.
      by move/eqP; case.
      rewrite seq.in_cons; move/orP; case.
      move/eqP; case => _ Hyp'; subst. 
      by rewrite dual_dual_is_identinty.
      by move/sEnv_1_not_in_shift_up.
    }
    subst.
    have fact: T = T0.
    { move: H3;rewrite seq.in_cons;  move/orP; case.
      by move/eqP; case.
      rewrite seq.in_cons; move/orP; case.
      by move/eqP; case.
      by move/sEnv_1_not_in_shift_up. }
    subst.
    apply/(TRes _ _ S1). 
    (* Prove lin 0 (P || Q[n/0]) *)
    * inversion H1; subst=>{H1 S1 T0 H3 H6 H9 H10 H11 Gamma Delta}.
      + inversion H5; subst. 
        apply/LParR => //.
        apply/(lin_subst 0 (var_ch 0)). 
        inversion H2; subst => {H2}. 
        by move:H11 => //.
        inversion H11;subst => //.
        asimpl. 
        apply/injectiveNS_scons2_0.
        by asimpl => /=.
        move:H3 => //.
        move:H4 => //.
      + move:H5 => //.
    (* Prove lin 1 (P || Q[n/0]) *)
    * inversion H2; subst=>{H2 S1 T0 H3 H6 H9 H10 H11 Gamma Delta}.
      + move:H8 => //.
      + inversion H8;subst. 
        apply/LParL => //.
        inversion H1; subst => {H1}. 
        by inversion H9; subst. 
        move:H9 => //.
        have fact:  forall n y sigma P,  (* reformulate free_ch_subst *)
            injectiveNS n (free_ch P) sigma -> 
            n \notin free_ch P -> 
            y = ch_index (sigma n) ->
            y \notin free_ch (subst_proc var_val sigma P). 
        { move => n0 y sigma P0 Hfact1 Hfact Hfact2.
          move:Hfact.
          apply/contra => Hfact.
          apply/free_ch_subst; subst.
          apply/Hfact.
          apply/Hfact1. 
        }
        apply/(fact 1). 
        apply/injectiveNS_scons2_1.
        apply/H2. 
        by asimpl;auto.
        move:H3 => //.
    (* Prove final typing judgement (TRes premise) *) 
    * move => {H1 H2 H7}. (* cleaning up *)
      apply/TPar. 
      + by move:H10; rewrite dual_dual_is_identinty.
      + move: H11 => /= => Hyp.
        apply/(sessEnv_like_a_set_2 (var_ch n.+2) T0). 
        move:H9.
        rewrite !seq.in_cons. 
        move/orP; case.
        move/eqP; case => H' H''; subst.
        apply/orP; right; apply/orP; right; apply/orP; left.
        apply/eqP; f_equal => //.
        move/orP; case.
        move/eqP; case => H' H''; subst.
        apply/orP;right;apply/orP;right;apply/orP;right;apply/orP;left.
        apply/eqP; f_equal => //.
        move => H {Hyp H6 H10 H3}. 
        apply/orP;right;apply/orP;right;apply/orP;right;apply/orP;right.
        have fact: forall c c' sT sigma Delta, 
            (c, sT) \in Delta -> c' = subst_ch sigma c -> 
            (c', sT) \in subst_sEnv sigma Delta.
        move => c c' sT sigma Env Hyp1 Hyp2. 
        by subst; apply/sEnv_subst.
        apply/fact. 
        apply/H.
        by simpl.
        apply/(exchange _ _ _ []) => /=. 
        apply/(exchange _ _ _ [(var_ch 0, S1)]) => /=. 
        apply/substitution.
        apply/Hyp.
        simpl.
        f_equal; f_equal; f_equal; f_equal; f_equal.
        move => {Hyp H9 H6 H10 H3}.
        elim: Delta => //. 
        move => [[k] s] l IH => /=. 
        by f_equal.
Qed.

Theorem subject_reduction : forall P Q Gamma Delta,
    reduce P Q -> OFT Gamma Delta P -> OFT Gamma Delta Q. 
Proof.
  move => P Q Gamma Delta H.
  elim: H Gamma Delta. 
  - move => P0 Q0 Hred IH Gamma Delta H. 
    inversion H; subst. 
    apply/(TRes _ _ S). 
    apply/(lin_reduction _ P0 Q0).
    apply/OFT_resbound_lin/H5.
    apply/Hred.
    apply/H1.
    apply/lin_reduction. 
    apply/OFT_resbound_lin/H5.
    apply/Hred.
    apply/H2.
    by apply/IH.
  - move => P0 Q0 R Hred IH Gamma Delta H.
    inversion H;subst. 
    apply/TPar. 
    by apply/IH. 
    auto.
  - move => P0 P' Q0 Q' Hstruct1 Hred IH Hstruct2 Gamma Delta H.
    apply/subject_congruence. 
    apply/SC_Sym. 
    apply/Hstruct2. 
    apply/IH.
    apply/subject_congruence. 
    apply/SC_Sym. 
    by apply/Hstruct1. 
    auto.
  - apply/subject_reduction_R_Com1.
  - apply/subject_reduction_R_Com2.
  - apply/subject_reduction_R_Del1.
  - apply/subject_reduction_R_Del2.
Qed.
