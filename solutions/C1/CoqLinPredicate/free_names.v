From mathcomp Require Import all_ssreflect.
Require Export lists.
Require Export syntax.
Require Import core unscoped.
Require Export semantics.
Require Import Lia.

(* channels, substitutions, and nat *) 
Definition ch_index (x:ch):=
  match x with
    var_ch n => n
  end.

Lemma ch_index_injective : injective ch_index. 
Proof.
  move => [n1] [n2] => /= => H; subst => //.
Qed. 

Lemma id_ch : forall x,
    var_ch (ch_index x) = x.
Proof.
  by induction x.
Qed. 

Definition injectiveNS n (S: seq.seq nat) := 
  fun (f : nat -> ch) =>
    forall x: nat, x\in S -> f n = f x -> n = x.

Lemma injective_injectiveNS : forall n S sigma,
    injective sigma -> injectiveNS n S sigma. 
Proof. 
  rewrite/injectiveNS. 
  move => n S sigma HInj x H1 H2. 
  by apply/HInj.
Qed.

Lemma injective_incr2 : 
    injective (fun x => var_ch x.+2).
Proof. 
  rewrite/injective => x1 x2 H. 
  by inversion H.
Qed.

Lemma injectiveNS_incr2 : forall n S,
    injectiveNS n S (fun x => var_ch x.+2).
Proof. 
  move => n S.
  apply/injective_injectiveNS.
  apply/injective_incr2.
Qed.

Lemma injectiveNS_catL : forall n S1 S2 sigma,
    injectiveNS n (S1 ++ S2) sigma -> injectiveNS n S1 sigma.
Proof.
  move => n S1 S2 sigma. 
  rewrite/injectiveNS => H x Hset Heq.
  apply/H.
  rewrite mem_cat.
  apply/orP.
  by left. 
  apply/Heq.
Qed. 

Lemma injectiveNS_catR : forall n S1 S2 sigma,
    injectiveNS n (S1 ++ S2) sigma -> injectiveNS n S2 sigma.
Proof.
  move => n S1 S2 sigma. 
  rewrite/injectiveNS => H x Hset Heq.
  apply/H.
  rewrite mem_cat.
  apply/orP.
  by right. 
  apply/Heq.
Qed. 

Lemma injectiveNS_cons : forall n a S sigma,
    injectiveNS n (a:: S) sigma -> 
    injectiveNS n S sigma.
Proof.
  move => n a S sigma. 
  rewrite/injectiveNS => H x Hset Heq.
  apply/H.
  rewrite seq.in_cons.
  apply/orP.
  by right. 
  apply/Heq.
Qed. 

Lemma injectiveNS_up_ch_ch : forall n S sigma,
    injectiveNS n (map_predn_filter S) sigma -> 
    injectiveNS (n.+1) S (up_ch_ch sigma).
Proof.
  asimpl.
  rewrite/scons/funcomp/subst_ch/shift/injectiveNS => 
           n S sigma injSigma x.
  destruct x. 
  destruct (sigma n); discriminate. 
  move => H1 H2.
  f_equal.
  apply/injSigma => //.
  by apply/in_prednR. 
  move:H2.
  case (sigma x).
  case (sigma n) => n0 n1.
  case => H.
  by subst. 
Qed.

Lemma injectiveNS_up_ch_ch_0 : forall S sigma,
    injectiveNS 0 S (up_ch_ch sigma).
Proof.
  move => S sigma; asimpl.
  rewrite/injectiveNS/scons/funcomp/subst_ch => x Hyp. 
  destruct x => //; destruct (sigma x) => //.
Qed. 

Lemma injectiveNS_up_ch_ch_1 : forall S sigma,
    injectiveNS 1 S (up_ch_ch (up_ch_ch sigma)).
Proof.
  move => S sigma; asimpl.
  rewrite/injectiveNS/up_ch_ch/scons/funcomp => x Hyp.
  destruct x => //; destruct x => //; destruct (sigma x) => //.
Qed. 

Lemma injectiveNS_scons_n: forall n m S,
    n.+2!=m -> injectiveNS n.+3 S (scons (var_ch m) ids).
Proof.
  move => n m P H1. 
  rewrite/injectiveNS => x _.
  case: x. 
  asimpl; case => H; subst. 
  move:H1 => /eqP. 
  by case. 
  move => n0.
  asimpl.
  by case => Hyp; subst. 
Qed. 

Lemma injectiveNS_scons_0: forall m S,
    m.+3 \notin S -> injectiveNS 0 S (scons (var_ch m.+2) ids).
Proof.
  rewrite/injectiveNS; asimpl => m S HSet /=. 
  case => //=.
  move => n Hyp1; case => Hyp2; subst. 
  by move: Hyp1 HSet ->.
Qed. 

Lemma injective_swap : forall x y,
    injective (swap_ch x y). 
Proof. 
  rewrite/injective => x y n1 n2. 
  case; case: ifP. 
  move/eqP => H; subst. 
  case: ifP. 
  move/eqP => H; subst => //. 
  move/eqP => H. 
  case: ifP. 
  move/eqP => H1 H2; subst => //.
  move/eqP => H1 H2; subst => //.
  move/eqP => H. 
  case: ifP. 
  move/eqP => H1; subst => //.
  case: ifP. 
  move/eqP => H1; subst => //.
  move/eqP => H1. 
  case: ifP.
  by move/eqP. 
  move/eqP => H2 H3; subst => //. 
  move/eqP => H1. 
  case: ifP. 
  move/eqP => H2 H3; subst => //.
  move/eqP => H2. 
  case: ifP. 
  move/eqP => H3 H4; subst => //.
  move/eqP => H3 => //. 
Qed. 

Lemma injectiveNS_swap : forall n S x y,
    injectiveNS n S (swap_ch x y). 
Proof. 
  move => n S x y. 
  apply/injective_injectiveNS.
  apply/injective_swap. 
Qed. 

(* Notion of free channel and properties *)
Fixpoint free_ch (P : proc) :=
  match P with
  | EndP        => nil
  | WaitP y P'  => ch_index y :: free_ch P'
  | CloseP y P' => ch_index y :: free_ch P'
  | ResP P'     => map_predn_filter (map_predn_filter (free_ch P'))
  | ParP P1 P2  => free_ch P1 ++ free_ch P2
  | InSP  y P'  => ch_index y :: map_predn_filter(free_ch P')
  | DelP y x P' => ch_index y :: ch_index x :: free_ch P'
  end.

Lemma free_ch_subst : forall n sigma P,  
    ch_index (sigma n)
      \in free_ch (subst_proc sigma P) 
          -> injectiveNS n (free_ch P) sigma
          -> n \in free_ch P.
Proof.
  move => n sigma P; elim: P n sigma => //=.
  (* WaitP *)
  - move => c P IH n sigma => //=; asimpl.
    rewrite !seq.in_cons.
    move /orP => [H0 | H1] Inj; apply/orP.
    + left; apply/eqP; apply/Inj. 
      rewrite in_cons. 
      apply/orP.
      by left.
      move:H0.
      case (sigma n) => n0.
      case c => n1 /=.
      case (sigma n1) => n2 /=.
      move/eqP => H.
      by subst. 
    + right.
      apply/(IH n sigma) => //.
      apply/injectiveNS_cons; apply/Inj.
  (* CloseP *)
  - move => c P IH n sigma => //=; asimpl.
    rewrite !seq.in_cons.
    move /orP => [H0 | H1] Inj; apply/orP.
    + left; apply/eqP; apply/Inj. 
      rewrite in_cons. 
      apply/orP.
      by left.
      move:H0.
      case (sigma n) => n0.
      case c => n1 /=.
      case (sigma n1) => n2 /=.
      move/eqP => H.
      by subst. 
    + right.
      apply/(IH n sigma) => //.
      apply/injectiveNS_cons; apply/Inj.
  (* ResP *)
  - move => P IH n sigma /in_prednL /in_prednL H Inj.
    repeat apply/in_prednR.
    apply: (IH (n.+2) (up_ch_ch (up_ch_ch sigma))); last first.
    by repeat apply (injectiveNS_up_ch_ch).
    move: H.
    by asimpl; rewrite/ch_index/scons/funcomp/shift; elim: (sigma n).
  (* ParP *)
  - move => P IH1 Q IH2 n sigma =>/=. 
    rewrite !mem_cat.
    move/orP => [H0 | H1] Inj; apply /orP.
    + left; apply/(IH1 _ _ H0).
      apply/injectiveNS_catL.
      apply/Inj.
      right; apply/(IH2 _ _ H1). 
      apply/injectiveNS_catR.
      apply/Inj.
  (* InSP *)
  - move => c P IH n sigma => //=; asimpl.
    rewrite !seq.in_cons.
    move /orP => [H0 | /in_prednL H1] Inj; apply/orP.
    + left; apply/eqP; apply/Inj.
      move: H0 => /eqP.
      rewrite/subst_ch/ch_index.
      destruct c; destruct (sigma n); destruct (sigma n1).
      destruct (sigma n0) => Heq; subst. 
      rewrite seq.in_cons. 
      apply/orP.
      by left. 
      move:H0.
      case (sigma n) => n0.
      case c => n1 /=.
      case (sigma n1) => n2 /=.
      move/eqP => H.
      by subst. 
    + right.
      apply/in_prednR.
      apply: (IH (n.+1) (up_ch_ch sigma)); last first.
      repeat apply/injectiveNS_up_ch_ch.
      apply/injectiveNS_cons.
      apply/Inj.
      move: H1.
      asimpl; rewrite/ch_index/scons/funcomp/shift.
      by destruct (sigma n) => /=.
  (* DelP *)
  - move => c c0 P IH n sigma => //=; asimpl.
    rewrite !seq.in_cons.
    move /orP => [H0 | H1] Inj; apply/orP.
    + left; apply/eqP; apply/Inj.
      move: H0 => /eqP.
      rewrite/subst_ch /ch_index.
      destruct c; destruct (sigma n); destruct (sigma n1).
      destruct (sigma n0) => Heq; subst. 
      rewrite seq.in_cons. 
      apply/orP.
      by left. 
      move:H0.
      case (sigma n) => n0; case c => n1 /=; case (sigma n1) => n2 /=.
      move/eqP => H.
      by subst. 
    + right.
      move:H1 => /orP.
      case => [H0 | H1]; apply/orP.
      * left; apply/eqP; apply/Inj.
        move: H0 => /eqP.
        rewrite/subst_ch /ch_index.
        destruct c; destruct (sigma n); destruct c0.
        destruct (sigma n2) => Heq; subst. 
        rewrite seq.in_cons; apply/orP; right.
        by rewrite seq.in_cons; apply/orP; left.
        move:H0.
        case (sigma n); case c => n1; case c0 => n2 => n0 /=. 
        case (sigma n2) => n3 /=.
        move/eqP => H.
        by subst. 
      * right.
        apply: (IH n sigma); last first.
        apply/injectiveNS_cons; apply/injectiveNS_cons.
        apply/Inj.
        move: H1.
        asimpl; rewrite/ch_index/scons/funcomp/shift.
        by destruct (sigma n).
Qed.

Lemma free_ch_subst_inv : forall (n m : nat) (sigma : nat -> ch) P,  
    n \in free_ch P -> 
          m = ch_index (sigma n) ->
          m \in free_ch (subst_proc sigma P). 
Proof.
  move => n m sigma P; elim: P n m sigma => //=. 
  (* WaitP *)
  - move => c P IH n m sigma => //=.
    rewrite !seq.in_cons.
    move/orP => [/eqP H0 | H1] HSubst; apply/orP. 
    + subst; left; apply/eqP.
      by destruct c => /=.
    + right. 
      by subst; apply/(IH n).
  (* CloseP *)
  - move => c P IH n m sigma => //=.
    rewrite !seq.in_cons.
    move/orP => [/eqP H0 | H1] HSubst; apply/orP. 
    + subst; left; apply/eqP.
      by destruct c => /=.
    + right. 
      by subst; apply/(IH n).
  (* Res *)
  - move => P IH n m sigma /in_prednL/in_prednL H Hsubst; subst.
    repeat apply/in_prednR.
    apply/(IH n.+2) => //.
    by asimpl; rewrite/ch_index/scons/funcomp/shift; elim: (sigma n).
  (* ParP *)
  - move => P IH1 Q IH2 n m sigma =>/=.     
    rewrite !mem_cat.
    move/orP => [H0 | H1] Hsubst; apply /orP.
    by left; apply/(IH1 _ _ _ H0).
    by right; apply/(IH2 _ _ _ H1). 
  (* InSP *)
  - move => c P IH n m sigma => //=.
    rewrite !seq.in_cons.
    move /orP => [H0 | /in_prednL H1] Hsubst; apply/orP.
    + left; apply/eqP.
      move: H0 => /eqP => H0.
      subst.
      by destruct c => /=.
    + right. 
      repeat apply/in_prednR.
      asimpl.
      apply/IH.
      move:H1. 
      apply. 
      move: H1.
      asimpl; rewrite/ch_index/scons/funcomp/shift.
      by subst;destruct (sigma n).
  (* DelP *)
  - move => c c0 P IH n m sigma => //=.
    rewrite !seq.in_cons.
    move /orP => [H0 | H1] Hsubst; apply/orP.
    + left; apply/eqP.
      move: H0 => /eqP => H0.
      subst.
      by destruct c => /=.
    + right. 
      move:H1.
      move /orP => [H0 | H1]; apply/orP.
      * left; apply/eqP. 
        move:H0 => /eqP => H0.
        subst.
        by destruct c0 => /=.
      * right. 
        asimpl.
        apply/IH.
        move:H1. 
        apply. 
        move: H1.
        asimpl; rewrite/ch_index/scons/funcomp/shift.
        by subst;destruct (sigma n).
Qed.

Lemma free_ch_congruence : forall (n:nat) (P Q:proc),
    struct_eq P Q -> n\in (free_ch Q) <-> n\in (free_ch P).
Proof.
  move => n P Q Hred; elim: Hred n.
  (* SC_Par_Com *)
  - move => P0 Q0 n /=.
    rewrite !mem_cat.
    split. 
    move/orP => H.
    rewrite Bool.orb_comm. 
    by apply/orP. 
    move/orP => H.
    rewrite Bool.orb_comm. 
    by apply/orP. 
    (* SC_Par_Assoc *) 
  - move => P0 Q0 R n /=. 
    rewrite !mem_cat.
    split. 
    move/orP => H.
    apply/orP.
    inversion H.
    left. 
    apply/orP.
    by left. 
    move:H0 => /orP. 
    case. 
    left; apply/orP.
    by right. 
    by right. 
    move/orP => H.
    apply/orP.
    inversion H.
    move:H0 => /orP => H'. 
    inversion H'. 
    by left. 
    right. 
    apply/orP.
    by left.
    right. 
    apply/orP.
    by right. 
  (* SC_Par_Inact *)
  - move => P0 n /=.
    split. 
    move => H.
    rewrite mem_cat. 
    apply/orP.
    by left. 
    rewrite mem_cat. 
    move/orP.
    by case. 
  (* SC_Res_Par *)
  - move => P0 Q0 n /=.
    split. 
    {
      repeat move/in_prednL.
      rewrite !mem_cat.
      move/orP; case => H.      
      apply/orP.
      by left; repeat apply/in_prednR. 
      apply/orP.
      right. 
      move:H.
      rewrite/shift_up.
      asimpl.
      move => Hyp.
      apply/(free_ch_subst _ (fun x : nat => var_ch (x.+2)) _) =>//=.
      apply/injective_injectiveNS.
      apply/injective_incr2.
    }
    {
      rewrite !mem_cat.
      move/orP; case.
      repeat move/in_prednL. 
      move => H. 
      repeat apply/in_prednR.
      rewrite mem_cat. 
      by apply/orP; left. 
      move => H.
      repeat apply/in_prednR.
      rewrite mem_cat. 
      apply/orP; right. 
      rewrite/shift_up; asimpl.
      rewrite/funcomp.
      apply/free_ch_subst_inv. 
      apply/H => /=. 
      auto.
    }
  (* SC_Res_Inact *)
  - by [].
  (* SC_Res_SwapC *)
  - split => /=.
    {
      repeat move/in_prednL.
      move => H.
      repeat apply/in_prednR.
      apply/(free_ch_subst _ (swap_ch 0 1)) => //=.
      apply/injectiveNS_swap.
    }
    {
      repeat move/in_prednL.
      move => H.
      repeat apply/in_prednR.
      apply/(free_ch_subst_inv n.+2 _ (swap_ch 0 1)) => //.
    }
  (* SC_Res_SwapB *)
  - split => /=. 
    {
      repeat move/in_prednL.
      move => H.
      repeat apply/in_prednR.
      apply/(free_ch_subst _ (swap_ch 0 2)) => //=.
      apply/(free_ch_subst _ (swap_ch 1 3)) => //=.
      apply/injectiveNS_swap.
      apply/injectiveNS_swap.
    }
    {
      repeat move/in_prednL.
      move => H.
      repeat apply/in_prednR. 
      apply/(free_ch_subst_inv n.+4).
      apply/(free_ch_subst_inv n.+4) => //.
      auto.
    }
  (* SC_Refl *)
  - by split. 
  (* SC_Sym *)
  - move => P0 Q0 Heq H n.
    apply iff_sym.
    apply/H.
  (* SC_Trans *)
  - move => P0 Q0 R Heq1 H1 Heq2 H2 n.
    move: (H2 n) (H1 n); apply iff_trans.
  (* SC_Cong_Par *)
  - admit. 
  (* SC_Cong_Res *)
  - admit. 
  (* SC_Cong_Close *)
  - admit. 
  (* SC_Cong_Wait *)
  - admit. 
  (* SC_Cong_OutS *)
  - admit.
  (* SC_Cong_InsP *)
  - admit.
Admitted. 

Lemma free_ch_subst_scons : forall n m P,
    n <> m ->
    n \in free_ch (subst_proc (scons (var_ch m) ids) P) ->
          n.+1 \in free_ch P.
Proof.
  move => n m P ineq.
  set sigma := scons (var_ch m) ids => H.
  apply/(free_ch_subst _ sigma) => //=. 
  rewrite/injectiveNS => x H'.
  destruct x => /=. 
  asimpl.
  case => H''; subst => //. 
  asimpl.
  by case => H''; subst. 
Qed. 

Lemma free_ch_reduction : forall (n:nat) (P Q:proc),
    reduce P Q -> n\in (free_ch Q) -> n \in (free_ch P).
Proof.
  move => n P Q Hred.
  elim: Hred n.
  - move => P0 Q0 Hred IH n =>/=.
    move/in_prednL/in_prednL => H.
    repeat apply/in_prednR.
    by apply/IH.
  - move => P0 Q0 R Hred IH n =>/=.
    rewrite mem_cat.
    move/orP => Hyp.
    rewrite mem_cat. 
    apply/orP.
    inversion Hyp.
    left.
    by apply/IH.
    by right. 
  - move => P0 P' Q0 Q' Hstruct1 Hred1 IH Hstruct2 n H. 
    have free_ch_congruence_R : forall (n:nat),
        struct_eq P0 P' -> n\in (free_ch P') -> n\in (free_ch P0).
    {
      intros. 
      apply/free_ch_congruence.
      apply/SC_Sym.
      apply/Hstruct1.
      auto.
    } 
    apply (free_ch_congruence_R n) in Hstruct1 =>//.
    apply/IH.
    apply(free_ch_congruence n Q' Q0)=>//.
  (* Close/Wait *)
  - move => P0 Q0 n => /=.
    move/in_prednL/in_prednL.
    rewrite mem_cat.
    move/orP => H.
    repeat apply/in_prednR.
    rewrite seq.in_cons; apply/orP; right. 
    rewrite mem_cat; apply/orP.
    move: H; case => Hyp.
    * by left.
    * right. 
      rewrite in_cons; apply/orP.
      by right.
  (* Delegation *)
  - move => x P0 Q0 n => /=. 
    case: x => n0 /=.
    move/in_prednL/in_prednL.
    rewrite mem_cat.
    move/orP => H.
    repeat apply/in_prednR.
    rewrite seq.in_cons; apply/orP; right. 
    rewrite seq.in_cons; apply/orP.
    have fact: (n.+2 = n0) \/ (n.+2 <> n0) by lia. 
    move: fact; case => Hyp.
    * left. apply/eqP/Hyp.
    * right. 
      rewrite mem_cat; apply/orP.
      inversion H. 
      + left. 
        by repeat apply/in_prednR.
      + right. 
        rewrite seq.in_cons; apply/orP; right. 
        repeat apply/in_prednR. 
        apply/(free_ch_subst_scons _ n0) => //.
Qed.


Lemma free_ch_subst_domain_codomain : forall n sigma P,
    n \in free_ch (subst_proc sigma P) -> 
            exists x, x\in free_ch P /\ ch_index(sigma x) = n.
Proof.
  move => n sigma P; elim: P n sigma => //= [|||| [m] | [m] [v]].
  (* WaitP *)
  - move => [m] P IH n sigma => /=.
    rewrite seq.in_cons. 
    move/orP; case. 
    move/eqP => H; subst. 
    exists m.
    split => //. 
    by rewrite seq.in_cons; apply/orP; left. 
    move/IH.
    case => x [H1 H2].
    exists x. 
    split => //. 
    rewrite seq.in_cons; apply/orP; right. 
    auto.
  (* CloseP *)
  - move => [m] P IH n sigma => /=.
    rewrite seq.in_cons. 
    move/orP; case. 
    move/eqP => H; subst. 
    exists m.
    split => //. 
    by rewrite seq.in_cons; apply/orP; left. 
    move/IH.
    case => x [H1 H2].
    exists x. 
    split => //. 
    rewrite seq.in_cons; apply/orP; right. 
    auto.
  (* ResP *)
  - move => P IH n sigma.
    move/in_prednL/in_prednL/IH.
    asimpl. 
    rewrite/funcomp/shift. 
    case. case. 
    + case; discriminate.  
    + case. 
      * case; discriminate. 
      * move => n0 /=; case => H1 H2. 
        exists n0. 
        split.
        by repeat apply/in_prednR. 
        move:H2. 
        case: (sigma n0) => n1. 
        by case. 
  (* ParP *)
  - move => P IH1 Q IH2 n sigma =>/=. 
    rewrite !mem_cat.
    move/orP => [H0 | H1].
    + move:(IH1 _ _ H0).
      case => x.
      case => H1 H2. 
      exists x.    
      split. 
      rewrite mem_cat. 
      apply/orP.
      by left.
      auto.
    + move:(IH2 _ _ H1).
      case => x.
      case => H3 H2. 
      exists x.    
      split. 
      rewrite mem_cat. 
      apply/orP.
      by right.
      auto.
  (* InSP *)
  - move => P IH n sigma => /=; asimpl.
    rewrite seq.in_cons. 
    move/orP; case.
    move/eqP => H; subst.  
    exists m.
    split => //. 
    * rewrite seq.in_cons. 
      apply/orP; left.
      by apply/eqP. 
    * move/in_prednL/IH.
      case => x. 
      case => Hyp.
      destruct x => /=.
      discriminate.
      move => H. 
      exists x. 
      rewrite seq.in_cons.
      split. 
      apply/orP.
      right. 
      by apply/in_prednR.
      move:H.
      rewrite/funcomp.
      destruct (sigma x) => /=. 
      case => //. 
  (* DelP *)
  - move => P IH n sigma => /=; asimpl.
    rewrite seq.in_cons. 
    move/orP; case.
    move/eqP => H; subst.  
    exists m.
    split => //. 
    * rewrite seq.in_cons. 
      by apply/orP; left; apply/eqP. 
    * rewrite seq.in_cons. 
      move/orP; case. 
      move/eqP => H; subst. 
      exists v.
      split => //.
      + rewrite !seq.in_cons. 
        apply/orP;right. 
        by apply/orP;left; apply/eqP.
      + move/IH. 
        case; case.        
        (* case 1 *)
        case => H1 H2; subst. 
        exists 0. 
        split => //. 
        rewrite !seq.in_cons. 
        apply/orP;right. 
        by apply/orP;right. 
        (* case 2 *)
        move => n0.
        case => H1 H2. 
        exists n0.+1.
        split => //. 
        rewrite !seq.in_cons. 
        apply/orP; right.
        by apply/orP; right. 
Qed. 

Lemma free_ch_0_shift : forall P, 
    0\notin free_ch (shift_up P). 
Proof.
  move => P.
  apply/negP.
  move/free_ch_subst_domain_codomain.
  case => x. 
  case => _ /=.
  move => H.
  inversion H. 
Qed.   

Lemma free_ch_1_shift : forall P, 
    1\notin free_ch (shift_up(shift_up P)).
Proof.
  move => P.
  rewrite/shift_up.
  asimpl.
  rewrite/funcomp /=.
  apply/negP.
  move/free_ch_subst_domain_codomain.
  case => x. 
  case => _ /= => H.
  inversion H.
Qed.




(* Proof of Lemma below carried out by Alessandro Bruni *) 
(* CURRENTLY NOT NECESSARY *) 
Lemma swap_ch_ch_id : forall x y m : nat,
    subst_ch (swap_ch x y) (swap_ch x y m) = var_ch m.
Proof.
move => x y m.
rewrite /subst_ch/swap_ch/=.
case: ifP => [/eqP|]; case: ifP => [/eqP ->|].
  by move=> ->.
case: ifP => [/eqP -> //|_ /eqP].
  by [].
case: ifP => [/eqP//|/eqP//].
case: ifP => [_ _ /eqP//|].
case: ifP => //.
Qed.
