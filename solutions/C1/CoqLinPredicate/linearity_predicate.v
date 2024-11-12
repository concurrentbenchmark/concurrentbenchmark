From mathcomp Require Import all_ssreflect.
Require Export syntax.
Require Export semantics.
Require Export free_names. 
Require Import core unscoped.
(* Import ListNotations. *)
Require Import Lia.

Definition ch_shift_up := subst_ch (fun n => var_ch (n.+1)). 

  
(* Linear Predicate *)

Inductive lin : ch -> proc -> Prop :=
| LEndP  x            : lin x EndP
| LWaitP x P          : (ch_index x) \notin (free_ch P) -> 
                        lin x (WaitP x P)
| LWaitPcongr x y P   : lin y P ->
                        not(x = y) -> 
                        lin y (WaitP x P)
| LCloseP x P         : (ch_index x) \notin (free_ch P) -> 
                        lin x (CloseP x P)
| LClosePcongr x y P  : lin y P -> 
                        not (x = y) -> 
                        lin y (CloseP x P)
| LResP  x P          : lin (ch_shift_up(ch_shift_up x)) P ->
                        lin x (ResP P)
| LParPL x P1 P2      : lin x P1 -> 
                        (ch_index x) \notin (free_ch P2) ->
                        lin x (ParP P1 P2)
| LParPR x P1 P2      : (ch_index x) \notin (free_ch P1) ->
                        lin x P2 ->
                        lin x (ParP P1 P2)
| LInSP x y P         : lin (ch_shift_up y) P ->
                        lin y (InSP x P)
| LDelP x y z P       : not (z=y) ->
                        lin z P -> 
                        lin z (DelP x y P)
| LDelPObj x y P      : not (x=y) -> 
                        (ch_index y) \notin (free_ch P) ->
                        lin y (DelP x y P).


Lemma not_in_fn_linear : forall (n:nat) (Q:proc),
    n \notin (free_ch Q) -> lin (var_ch n) Q.
Proof.
  move => n Q; elim: Q n => //.
  - constructor.
  - move => [m] P IH n => /=.
    rewrite in_cons negb_or => /andP [H1 H2].
    apply/LWaitPcongr.
    by apply/IH. 
    case => H; subst. 
    by move:H1 => /negP; case. 
  - move => [m] P IH n => /=.
    rewrite in_cons negb_or => /andP [H1 H2].
    apply/LClosePcongr.
    by apply/IH. 
    case => H; subst. 
    by move:H1 => /negP; case. 
  - move => P IH n => /=.
    move/not_in_prednL/not_in_prednL/IH. 
    by constructor.
  - move => P IH1 Q IH2 n /=.
    rewrite mem_cat negb_or.
    move/andP; case => H1 H2. 
    constructor => //.
    by apply/IH1.
  - move => [m] P IH n /=. 
    rewrite in_cons negb_or => /andP; case => H1.
    move/not_in_prednL.
    constructor => /=.
    by apply/IH.
  - move => [m] [m0] P IH n /=. 
    rewrite in_cons negb_or.
    move/andP; case => H1.
    rewrite in_cons negb_or.
    move/andP; case => /eqP H2 H3.
    constructor => /=.
    by case. 
    by apply/IH.
Qed.

Lemma lin_subst : forall n y P sigma, 
    lin (var_ch n) P -> 
    injectiveNS n (free_ch P) sigma -> 
    y = sigma n -> (* this just makes it easier applyin IH *)
    lin y (subst_proc sigma P).
Proof. 
  move => n y P sigma; elim: P n y sigma => /=.
  - constructor.
  (* WaitP *)
  - move => [m] P IH n y sigma => /= H1 => H2 H3.
    inversion H1; subst. 
    + apply/LWaitP.
      move:H4.
      apply/contra => H.
      apply/free_ch_subst.
      apply/H.
      by move:H2 => /injectiveNS_cons.
    + apply/LWaitPcongr.
      apply/IH => //.
      apply/H5.
      by move:H2 => /injectiveNS_cons.
      move:H6; rewrite/not => Hyp1 Hyp2. 
      apply/Hyp1; apply/Logic.eq_sym.
      f_equal; apply/H2. 
      by rewrite in_cons; apply/orP; left.
      by rewrite Hyp2.
  (* WaitP *)
  - move => [m] P IH n y sigma => /= H1 => H2 H3.
    inversion H1; subst. 
    + apply/LCloseP.
      move:H4.
      apply/contra => H.
      apply/free_ch_subst.
      apply/H.
      by move:H2 => /injectiveNS_cons.
    + apply/LClosePcongr.
      apply/IH => //.
      apply/H5.
      by move:H2 => /injectiveNS_cons.
      move:H6; rewrite/not => Hyp1 Hyp2. 
      apply/Hyp1; apply/Logic.eq_sym.
      f_equal; apply/H2. 
      by rewrite in_cons; apply/orP; left.
      by rewrite Hyp2.
  (* ResP *)
  - move => P IH n y sigma H 
              /injectiveNS_up_ch_ch/injectiveNS_up_ch_ch Inj Eq.  
    inversion H; subst; constructor. 
    apply/(IH n.+2) => //.
  (* ParP *)
  - move => P IH1 Q IH2 n y sigma H Inj Eq.
    inversion H; subst => /=.     
    + apply/LParPL. 
      apply/IH1.
      apply/H3.
      apply/injectiveNS_catL/Inj.
      auto.
      move: H4. 
      apply/contra. 
      move:Inj => /injectiveNS_catR => /[swap].
      apply/free_ch_subst.
    + apply/LParPR. 
      move: H3. 
      apply/contra. 
      move:Inj => /injectiveNS_catL => /[swap].
      apply/free_ch_subst.
      apply/IH2.
      apply/H4.
      apply/injectiveNS_catR/Inj.
      auto.
  (* InSP *)
  - move => [m] P IH n y sigma H 
              /injectiveNS_cons/injectiveNS_up_ch_ch Inj Hyp =>/=.
    inversion H; subst.
    apply/LInSP.
    apply/(IH n.+1) => //.
  (* DelP *)
  - move => [m] [m0] P IH n y sigma H /= Inj Hyp =>/=.
    inversion H; subst.
    (* LDelP *)
    * apply/LDelP. 
      + move:H3.
        rewrite/not => H3 H4; apply/H3; f_equal. 
        move:Inj => /injectiveNS_cons; apply => //.
        by rewrite in_cons; apply/orP; left. 
      + apply/(IH n) => //.
        by move: Inj => /injectiveNS_cons/injectiveNS_cons.
    (* LDelPObj *) 
    * apply/LDelPObj.
      + move:H3.
        rewrite/not => H3 H4; apply/H3; f_equal.
        have fact: forall (x y:nat), x=y -> y=x by lia.
        apply/fact; apply/Inj.
        by rewrite in_cons; apply/orP; left. 
        have fact': forall (x y:ch), x=y -> y=x.
        move => x y. 
        destruct x; destruct y => eq.
        f_equal.
        apply/fact. 
        by inversion eq. 
        by apply/fact'. 
      + move:H5.
        apply/contra => /= => Hyp. 
        apply/(free_ch_subst _ sigma) => //.
        by move:Inj => /injectiveNS_cons/injectiveNS_cons.
Qed. 

Lemma lin_subst_inv : forall n y P sigma, 
    lin y (subst_proc sigma P) -> 
    injectiveNS n (free_ch P) sigma -> 
    y = sigma n -> (* this just makes it easier applyin IH *)
    lin (var_ch n) P .
Proof. 
  move => n y P sigma; elim: P n y sigma => /=.
  - constructor.
  - move => [m] P IH n y sigma /= H HInj Eq => /=.  
    subst. 
    inversion H; subst. 
    + have lem: n = m.
      apply/HInj => //.  (* here need for injectiveNS *)
      by rewrite in_cons; apply/orP; left. 
      subst.
      apply/LWaitP.
      move:H2. 
      apply/contra.
      move/free_ch_subst_inv => /=. 
      apply => //.
    + apply/LWaitPcongr. 
      apply/IH => //.
      apply/H3.
      by move:HInj => /injectiveNS_cons.
      move:H4; rewrite/not => Hyp1 Hyp2. (* here need for injectiveNS *)
      apply/Hyp1.
      by inversion Hyp2. 
  - move => [m] P IH n y sigma /= H HInj Eq => /=.  
    subst. 
    inversion H; subst. 
    + have lem: n = m.
      apply/HInj => //.  (* here need for injectiveNS *)
      by rewrite in_cons; apply/orP; left. 
      subst.
      apply/LCloseP.
      move:H2. 
      apply/contra.
      move/free_ch_subst_inv => /=. 
      apply => //.
    + apply/LClosePcongr. 
      apply/IH => //.
      apply/H3.
      by move:HInj => /injectiveNS_cons.
      move:H4; rewrite/not => Hyp1 Hyp2. (* here need for injectiveNS *)
      apply/Hyp1.
      by inversion Hyp2. 
  - move => P IH n y sigma H HInj Eq. 
    inversion H; subst. 
    constructor. 
    apply/IH.
    apply/H2. 
    by apply/injectiveNS_up_ch_ch/injectiveNS_up_ch_ch.
    asimpl.
    rewrite/core.funcomp/scons/shift/subst_ch => /=. 
    case: (sigma n) => //.
  - move => P IH1 Q IH2 n y sigma H HInj Eq.
    inversion H; subst.
    + apply/LParPL => //. 
      apply/IH1 => //.
      apply/H3.
      by move:HInj => /injectiveNS_catL.
      move: H4. 
      apply/contra => H4. 
      by apply/free_ch_subst_inv => //.
    + apply/LParPR. 
      move: H3. 
      apply/contra => H3. 
      by apply/free_ch_subst_inv => //.
      apply/IH2 => //.
      apply/H4. 
      by move:HInj => /injectiveNS_catR.
  - move => [m] P IH n y sigma H HInj Eq. 
    inversion H; subst. 
    constructor => /=.
    apply/IH. 
    apply/H2.
    by move:HInj => /injectiveNS_cons/injectiveNS_up_ch_ch. 
    by rewrite/up_ch_ch => /=. 
  - move => [m] [m0] P IH n y sigma /= H HInj Eq. 
    inversion H; subst. 
    + apply/LDelP => /=.
      move:H3.
      rewrite/not => H3 Hyp; apply/H3.
      by inversion Hyp.
      apply/IH => //.
      apply/H5.
      by move:HInj => /injectiveNS_cons/injectiveNS_cons.
    + have[] := eqVneq n m0.
      * move => Hyp; subst. 
        apply/LDelPObj.
        move:H3.
        rewrite/not => Hyp1 Hyp2.
        apply/Hyp1.
        by inversion Hyp2. 
        move:H5 => /=.
        apply/contra => Hyp.
        by apply/(free_ch_subst_inv m0).
      * move => Hyp.
        apply/LDelP. 
        move:Hyp => /eqP.
        rewrite/not => Hyp1 Hyp2.
        apply/Hyp1.
        by inversion Hyp2. 
        apply/IH.
        move:H5.
        move/not_in_fn_linear.
        apply. 
        by move:HInj => /injectiveNS_cons/injectiveNS_cons.
        by rewrite H1 id_ch. 
Qed. 
   
Lemma lin_congruence : forall x P Q,
    struct_eq P Q -> lin x P <-> lin x Q.
Proof.
  move => [m] P Q H; elim: H.
  - move => P0 Q0.
    split.
    * move => H. 
      inversion H; subst. 
      by apply/LParPR.
      by apply/LParPL.
    * move => H. 
      inversion H; subst.
      by apply/LParPR. 
      by apply/LParPL. 
  - move => P0 Q0 R0.
    split.
    * move => H.
      inversion H; subst. 
      + inversion H3; subst.
        apply/LParPL => //=.
        by rewrite mem_cat negb_or H4 H6. 
        apply/LParPR => //.
        apply/LParPL => //.
      + apply/LParPR. 
        move:H3 => /=.
        by rewrite mem_cat negb_or => /andP [Hyp1 Hyp2].
        apply/LParPR => //. 
        move:H3 => /=.
        by rewrite mem_cat negb_or => /andP [Hyp1 Hyp2].
    * move => H. 
      inversion H; subst.
      + apply/LParPL. 
        apply/LParPL => //.
        move:H4 => /=.
        rewrite mem_cat.
        apply/contra => ->.
        by apply/orP; left. 
        move:H4 => /=.
        rewrite mem_cat.
        apply/contra => ->. 
        by apply/orP; right. 
      + inversion H4; subst. 
        apply/LParPL => //.
        apply/LParPR => //.
        apply/LParPR => //. 
        by rewrite mem_cat negb_or H3 H5. 
  - move => R.
    split. 
    * move => H. 
      inversion H  =>//=. 
      subst. 
      apply not_in_fn_linear in H3. 
      by rewrite id_ch in H3. 
    * move => H. 
      apply/LParPL => //.
  - move => P0 Q0. (* extrusion case *)
    split. 
    { move => H. 
      inversion H => {H};subst.
      + inversion H3; subst. 
        apply/LResP. 
        apply/LParPL =>//.
        move : H4. 
        apply/contra.
        rewrite/ch_shift_up/shift_up; asimpl.
        rewrite/core.funcomp/subst_ch.
        have fact: m.+2 = ch_index((fun x0 => var_ch(x0.+2))m)
          by auto.
        rewrite fact. 
        move/free_ch_subst. 
        apply.
        rewrite/injectiveNS => x0 H.
        by case. 
      + constructor.
        apply LParPR. 
        move : H3 => //=. 
        rewrite/ch_shift_up; asimpl.
        apply/contra => H. 
        repeat (apply/in_prednR; rewrite addn1).
        move: H => /= => H. 
        by repeat apply/in_prednR.
        rewrite/ch_shift_up/shift_up; asimpl.
        apply/(lin_subst m) => //.
        rewrite /core.funcomp; asimpl.
        rewrite/injectiveNS => n0 H. 
        by case. 
    }
    { move => H.
      inversion H => {H}; subst. 
      inversion H2 => {H2}; subst. 
      + apply/LParPL. 
        apply/LResP => //.
        move:H4 => /=.
        apply/contra => Hyp.
        asimpl.
        apply/(free_ch_subst_inv m) => //=.
      + apply/LParPR => /=.
        by repeat apply/not_in_prednR.
        move:H4 => /=.
        asimpl => H.
        apply/(lin_subst_inv m (var_ch m.+2)). 
        apply/H. 
        rewrite/funcomp => /=.
        apply injectiveNS_incr2.
        by asimpl.
    }
  - split.
    constructor. 
    repeat constructor.
  - move => R. (* swapC *) 
    split. 
    {
      move => H. 
      inversion H;subst. 
      constructor => /=.
      apply/(lin_subst m.+2) => //.
      apply/injectiveNS_swap.
    } 
    {
      move => H.
      inversion H; subst. 
      constructor => /=. 
      apply/(lin_subst_inv m.+2 _ _ (swap_ch 0 1)) => //.
      by rewrite/swap_ch.
      apply/injectiveNS_swap.
    } 
  - move => R. (* swapB *)
    split.
    {
      move => H.
      inversion H;subst. 
      inversion H2;subst. 
      constructor; constructor => /=.
      apply/(lin_subst m.+4) => //.
      apply/(lin_subst m.+4) => //.
      apply/injectiveNS_swap.
      apply/injectiveNS_swap.
    }
    {
      move => H. 
      inversion H; subst. 
      inversion H2; subst. 
      constructor. 
      constructor => /=. 
      apply/(lin_subst_inv m.+4 _ _ (swap_ch 0 2)) => /=.
      apply/(lin_subst_inv m.+4 _ _ (swap_ch 1 3)) => /=.
      apply/H3. 
      apply/injectiveNS_swap.
      rewrite/swap_ch => //=.
      apply/injectiveNS_swap.
      rewrite/swap_ch => //=.
    }
  - by [].
  - move => P0 Q0 H1 H2. 
    by apply iff_sym.
  - move => P0 Q0 R  Heq1 H1 Heq2 H2.
    move: H1 H2; apply iff_trans.
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
Admitted. 

Inductive all_bound_lin : proc -> Prop :=
| allbLNilP       : all_bound_lin EndP
| allbLWaitP x P  : all_bound_lin P -> all_bound_lin (WaitP x P)
| allbLCloseP x P : all_bound_lin P -> all_bound_lin (CloseP x P)
| allbLResP  P    : lin (var_ch 0) P -> lin (var_ch 1) P ->
                     all_bound_lin P -> all_bound_lin (ResP P)
| allbLParP P1 P2 : all_bound_lin P1 -> all_bound_lin P2 -> 
                     all_bound_lin (ParP P1 P2)
| allbLInSP x P   : all_bound_lin P -> lin (var_ch 0) P -> 
                    all_bound_lin (InSP x P)
| allbLDelP x y P : all_bound_lin P -> all_bound_lin (DelP x y P)
.

Lemma allbound_subst : forall P sigma, 
    all_bound_lin P -> all_bound_lin (subst_proc sigma P).
Proof. 
  move => P sigma; elim: P sigma. 
  - constructor. 
  - move => c P IH sigma H => /=. 
    inversion H; subst. 
    constructor. 
    by apply/IH. 
  - move => c P IH sigma H => /=. 
    inversion H; subst. 
    constructor. 
    by apply/IH.
  - move => P IH sigma H /=.
    inversion H; subst.    
    constructor.
    apply/lin_subst.
    apply/H1.
    apply/injectiveNS_up_ch_ch_0.
    auto.
    apply/lin_subst.
    apply/H2. 
    apply/injectiveNS_up_ch_ch_1.
    auto.
    apply/IH => //.
  - move => P IH1 Q IH2 sigma H.
    inversion H; subst => /=.
    constructor. 
    by apply/IH1. 
    by apply/IH2. 
  - move => c P IH sigma H => /=.
    inversion H; subst. 
    constructor. 
    by apply/IH.
    apply/lin_subst.
    apply/H3. 
    apply/injectiveNS_up_ch_ch_0.
    auto.
  - move => c c0 P IH sigma H => /=.
    inversion H; subst. 
    constructor. 
    by apply/IH.
Qed.

Lemma allbound_subst_inv : forall P sigma, 
    all_bound_lin (subst_proc sigma P) -> all_bound_lin P.
Proof. 
  move => P sigma; elim: P sigma. 
  - constructor. 
  - move => c P IH sigma /= H.
    inversion H; subst. 
    constructor. 
    by apply/(IH sigma).
  - move => c P IH sigma /= H.
    inversion H; subst. 
    constructor. 
    by apply/(IH sigma).
  - move => P IH sigma H.
    inversion H; subst.    
    constructor.
    apply/lin_subst_inv => //.
    apply/H1. 
    apply/injectiveNS_up_ch_ch_0.
    apply/lin_subst_inv => //.
    apply/H2. 
    apply/injectiveNS_up_ch_ch_1.
    apply/IH.
    apply/H3.
  - move => P IH1 Q IH2 sigma H.
    inversion H; subst => /=.
    constructor. 
    move:H2.
    by apply/IH1. 
    move:H3.
    by apply/IH2. 
  - move => c P IH sigma H.
    inversion H;subst => /=.
    constructor. 
    apply/(IH (up_ch_ch sigma)). 
    by apply/H2. 
    apply/lin_subst_inv => //. 
    apply/H3.
    apply/injectiveNS_up_ch_ch_0.
  - move => c c0 P IH sigma H.
    inversion H; subst => /=.
    constructor. 
    by apply/(IH sigma).
Qed.


Lemma allbound_struct : forall P Q, 
    struct_eq P Q -> all_bound_lin P <-> all_bound_lin Q.
Proof. 
  move => P Q H; elim: H.
  - split. 
    move => H.
    inversion H; subst.
    by constructor. 
    move => H.
    inversion H; subst. 
    by constructor.
  - split. 
    move => H.
    inversion H; subst. 
    inversion H2; subst. 
    constructor.
    apply/H4. 
    by constructor. 
    move => H.
    inversion H; subst. 
    inversion H3; subst. 
    constructor. 
    by constructor. 
    apply/H5.
  - split.
    by move => H; inversion H.
    move => H. 
    constructor => //. 
    constructor. 
  - split.
    move => H.
    inversion H; subst. 
    inversion H2;subst. 
    constructor. 
    apply/LParPL => //.
    apply/free_ch_0_shift.
    constructor => //. 
    apply/free_ch_1_shift. 
    constructor => //.
    by repeat apply/allbound_subst.
    move => H.
    inversion H; subst. 
    inversion H3; subst. 
    constructor. 
    constructor. 
    inversion H1; subst => //. 
    by apply/not_in_fn_linear.
    inversion H2; subst => //.
    by apply/not_in_fn_linear.
    apply/H5. 
    apply/(allbound_subst_inv _ (fun n => var_ch (n.+2))).
    move:H6.
    rewrite/shift_up; asimpl.
    apply.
  - split.
    constructor. 
    repeat constructor.
  - split. 
    { 
      move => H. 
      inversion H; subst. 
      apply/allbLResP.
      apply/(lin_subst 1 _ _ (swap_ch 0 1)) => //.
      apply/injectiveNS_swap.
      apply/(lin_subst 0 _ _ (swap_ch 0 1)) => //.
      apply/injectiveNS_swap.
      apply/allbound_subst => //. 
    } 
    {
      move => H. 
      inversion H; subst. 
      apply/allbLResP. 
      apply/(lin_subst_inv 0) => //.
      apply/H2.
      apply/injectiveNS_swap.
      apply/(lin_subst_inv 1) => //.
      apply/H1.
      apply/injectiveNS_swap.
      apply/(allbound_subst_inv _ (swap_ch 0 1)) => //.
    } 
  - split.
    {
      move => H.
      inversion H; subst. 
      inversion H1; subst. 
      inversion H2; subst. 
      inversion H3; subst. 
      simpl in * => {H H1 H2 H3}. 
      apply/allbLResP. 
      + apply/LResP => /=.
        apply (lin_subst 2 (var_ch 2) _ (swap_ch 1 3)) => //.
        apply (lin_subst 0 (var_ch 2) _ (swap_ch 0 2)) => //.
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.
      + apply/LResP => /=.
        apply (lin_subst 1 (var_ch 3) _ (swap_ch 1 3)) => //.
        apply (lin_subst 1 (var_ch 1) _ (swap_ch 0 2)) => //.
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.
      + apply/allbLResP. 
        apply (lin_subst 0 (var_ch 0) _ (swap_ch 1 3)) => //.
        apply (lin_subst 2 (var_ch 0) _ (swap_ch 0 2)) => //.
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.
        apply (lin_subst 3 (var_ch 1) _ (swap_ch 1 3)) => //.
        apply (lin_subst 3 (var_ch 3) _ (swap_ch 0 2)) => //.
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.
        apply/allbound_subst.
        apply/allbound_subst => //.
    } 
    {
      move => H. 
      inversion H; subst. 
      inversion H1; subst. 
      inversion H2; subst. 
      inversion H3; subst. 
      simpl in * => {H H1 H2 H3}. 
      apply/allbLResP. 
      + apply/LResP => /=.
        apply/(lin_subst_inv 2 (var_ch 0) _ (swap_ch 0 2)) => //. 
        apply/(lin_subst_inv 0 (var_ch 0) _ (swap_ch 1 3)) => //. 
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.
      + apply/LResP => /=.
        apply/(lin_subst_inv 3 (var_ch 3) _ (swap_ch 0 2)) => //. 
        apply/(lin_subst_inv 3 (var_ch 1) _ (swap_ch 1 3)) => //. 
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.
      + apply/allbLResP.
        apply/(lin_subst_inv 0 (var_ch 2) _ (swap_ch 0 2)) => //. 
        apply/(lin_subst_inv 2 (var_ch 2) _ (swap_ch 1 3)) => //. 
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.
        apply/(lin_subst_inv 1 (var_ch 1) _ (swap_ch 0 2)) => //. 
        apply/(lin_subst_inv 1 (var_ch 3) _ (swap_ch 1 3)) => //. 
        apply/injectiveNS_swap.
        apply/injectiveNS_swap.
        apply/allbound_subst_inv. 
        apply/allbound_subst_inv. 
        apply/H8.
     }
  - by [].
  - move => P0 Q0 Heq H.
    by apply iff_sym.
  - move => P0 Q0 R  Heq1 H1 Heq2 H2.
    move: H1 H2; apply iff_trans.
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
Admitted. 

Lemma lin_reduction : forall x P Q,
    all_bound_lin P -> reduce P Q -> lin x P -> lin x Q.
Proof.
  move => x P Q Hallb H; elim: H x Hallb.
  - move => P0 Q0 Hred IH x Hallb H.
    inversion H; constructor; subst => {H}.
    apply/IH.
    by inversion Hallb.
    apply/H2. 
  - move => P0 Q0 R Hred IH x Hallb H. 
    inversion Hallb; subst. 
    inversion H; subst => {H}. 
    * apply/LParPL. 
      apply/IH => //.
      apply/H6.
    * apply/LParPR. 
      move:H5. 
      apply/contra. 
      by move/(free_ch_reduction _ _ _ Hred). 
      apply/H6. 
  - move => P0 P' Q0 Q' Hstruct1 Hred IH Hstruct2 x Hallb H.
    apply/(lin_congruence x Q' Q0) =>//.
    apply/IH.
    move:Hallb.
    apply allbound_struct.
    by apply/SC_Sym.
    by apply/(lin_congruence x P0 P').
  - move => P0 Q0 [m] Hallb H. 
    inversion H; subst => {H}. 
    constructor => /=.
    inversion H2; subst => {H2}.
    (* LParL *)
    + inversion H3; subst => {H3}. 
      apply/LParPL => //.
    + inversion H4; subst => {H4}. 
      apply/LParPR => //.
  (* Delegation case, key part *)
  - move => [m] P0 Q0 [n] Hallb H. 
    inversion H; subst => {H}. 
    constructor => /=. 
    inversion H2; subst  => {H2}.
    (* LParL *)
    + inversion H3; subst => {H3}.
      (* LDelP *) 
      * apply/LParPL => //. 
        move:H4 => /=.
        rewrite seq.in_cons negb_or.
        move/andP; case => _.
        move/not_in_prednL.
        apply/contra => Hyp.
        apply (free_ch_subst _ (scons (var_ch m) ids)) => //=.
        apply/injectiveNS_scons_n.
        apply/eqP; move:H2 => /=.
        rewrite/not => H H'.
        by apply/H; subst. 
      (* LDelPObj *) 
      * simpl in *. 
        inversion Hallb; subst => {Hallb H0 H1}. 
        inversion H3; subst => {H3 H1}. 
        inversion H5; subst => {H1 H2 H5}. 
        apply/LParPR => //.
        apply/(lin_subst 0) => //. 
        apply/injectiveNS_scons_0.
        move:H4.
        rewrite !seq.in_cons !negb_or.
        by move/andP; case => _ => /not_in_prednL.
    + (* LParR *)
      inversion H4; subst => {H4}.  
      apply/LParPR. 
      * move:H3 => /=.
        rewrite !seq.in_cons !negb_or.  
        move/andP; case => _.
        by move/andP; case.
      * apply/lin_subst.
        apply/H1.
        apply/injectiveNS_scons_n.
        move:H3 => /=.
        rewrite !in_cons !negb_or => /andP; case => _ /andP.
        case => //.
        auto.
Qed. 
