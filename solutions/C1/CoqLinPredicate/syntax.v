Require Import core unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive ch : Type :=
    var_ch : nat -> ch.

Definition subst_ch (sigma_ch : nat -> ch) (s : ch) : ch :=
  match s with
  | var_ch s0 => sigma_ch s0
  end.

Lemma up_ch_ch (sigma : nat -> ch) : nat -> ch.
Proof.
exact (scons (var_ch var_zero)
         (funcomp (subst_ch (funcomp (var_ch) shift)) sigma)).
Defined.

Lemma upId_ch_ch (sigma : nat -> ch) (Eq : forall x, sigma x = var_ch x) :
  forall x, up_ch_ch sigma x = var_ch x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (subst_ch (funcomp (var_ch) shift)) (Eq n')
       | O => eq_refl
       end).
Qed.

Definition idSubst_ch (sigma_ch : nat -> ch)
  (Eq_ch : forall x, sigma_ch x = var_ch x) (s : ch) :
  subst_ch sigma_ch s = s := match s with
                             | var_ch s0 => Eq_ch s0
                             end.

Lemma upExt_ch_ch (sigma : nat -> ch) (tau : nat -> ch)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ch_ch sigma x = up_ch_ch tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (subst_ch (funcomp (var_ch) shift)) (Eq n')
       | O => eq_refl
       end).
Qed.

Definition ext_ch (sigma_ch : nat -> ch) (tau_ch : nat -> ch)
  (Eq_ch : forall x, sigma_ch x = tau_ch x) (s : ch) :
  subst_ch sigma_ch s = subst_ch tau_ch s :=
  match s with
  | var_ch s0 => Eq_ch s0
  end.

Definition compSubstSubst_ch (sigma_ch : nat -> ch) (tau_ch : nat -> ch)
  (theta_ch : nat -> ch)
  (Eq_ch : forall x, funcomp (subst_ch tau_ch) sigma_ch x = theta_ch x)
  (s : ch) : subst_ch tau_ch (subst_ch sigma_ch s) = subst_ch theta_ch s :=
  match s with
  | var_ch s0 => Eq_ch s0
  end.

Lemma up_subst_subst_ch_ch (sigma : nat -> ch) (tau_ch : nat -> ch)
  (theta : nat -> ch)
  (Eq : forall x, funcomp (subst_ch tau_ch) sigma x = theta x) :
  forall x,
  funcomp (subst_ch (up_ch_ch tau_ch)) (up_ch_ch sigma) x = up_ch_ch theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compSubstSubst_ch (funcomp (var_ch) shift) (up_ch_ch tau_ch)
                (funcomp (up_ch_ch tau_ch) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstSubst_ch tau_ch (funcomp (var_ch) shift)
                      (funcomp (subst_ch (funcomp (var_ch) shift)) tau_ch)
                      (fun x => eq_refl) (sigma n')))
                (ap (subst_ch (funcomp (var_ch) shift)) (Eq n')))
       | O => eq_refl
       end).
Qed.

Lemma substSubst_ch (sigma_ch : nat -> ch) (tau_ch : nat -> ch) (s : ch) :
  subst_ch tau_ch (subst_ch sigma_ch s) =
  subst_ch (funcomp (subst_ch tau_ch) sigma_ch) s.
Proof.
exact (compSubstSubst_ch sigma_ch tau_ch _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_ch_pointwise (sigma_ch : nat -> ch) (tau_ch : nat -> ch) :
  pointwise_relation _ eq (funcomp (subst_ch tau_ch) (subst_ch sigma_ch))
    (subst_ch (funcomp (subst_ch tau_ch) sigma_ch)).
Proof.
exact (fun s => compSubstSubst_ch sigma_ch tau_ch _ (fun n => eq_refl) s).
Qed.

Lemma instId'_ch (s : ch) : subst_ch (var_ch) s = s.
Proof.
exact (idSubst_ch (var_ch) (fun n => eq_refl) s).
Qed.

Lemma instId'_ch_pointwise : pointwise_relation _ eq (subst_ch (var_ch)) id.
Proof.
exact (fun s => idSubst_ch (var_ch) (fun n => eq_refl) s).
Qed.

Lemma varL'_ch (sigma_ch : nat -> ch) (x : nat) :
  subst_ch sigma_ch (var_ch x) = sigma_ch x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_ch_pointwise (sigma_ch : nat -> ch) :
  pointwise_relation _ eq (funcomp (subst_ch sigma_ch) (var_ch)) sigma_ch.
Proof.
exact (fun x => eq_refl).
Qed.

Inductive proc : Type :=
  | EndP : proc
  | WaitP : ch -> proc -> proc
  | CloseP : ch -> proc -> proc
  | ResP : proc -> proc
  | ParP : proc -> proc -> proc
  | InSP : ch -> proc -> proc
  | DelP : ch -> ch -> proc -> proc.

Lemma congr_EndP : EndP = EndP.
Proof.
exact (eq_refl).
Qed.

Lemma congr_WaitP {s0 : ch} {s1 : proc} {t0 : ch} {t1 : proc} (H0 : s0 = t0)
  (H1 : s1 = t1) : WaitP s0 s1 = WaitP t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => WaitP x s1) H0))
         (ap (fun x => WaitP t0 x) H1)).
Qed.

Lemma congr_CloseP {s0 : ch} {s1 : proc} {t0 : ch} {t1 : proc} (H0 : s0 = t0)
  (H1 : s1 = t1) : CloseP s0 s1 = CloseP t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => CloseP x s1) H0))
         (ap (fun x => CloseP t0 x) H1)).
Qed.

Lemma congr_ResP {s0 : proc} {t0 : proc} (H0 : s0 = t0) : ResP s0 = ResP t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => ResP x) H0)).
Qed.

Lemma congr_ParP {s0 : proc} {s1 : proc} {t0 : proc} {t1 : proc}
  (H0 : s0 = t0) (H1 : s1 = t1) : ParP s0 s1 = ParP t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => ParP x s1) H0))
         (ap (fun x => ParP t0 x) H1)).
Qed.

Lemma congr_InSP {s0 : ch} {s1 : proc} {t0 : ch} {t1 : proc} (H0 : s0 = t0)
  (H1 : s1 = t1) : InSP s0 s1 = InSP t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => InSP x s1) H0))
         (ap (fun x => InSP t0 x) H1)).
Qed.

Lemma congr_DelP {s0 : ch} {s1 : ch} {s2 : proc} {t0 : ch} {t1 : ch}
  {t2 : proc} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  DelP s0 s1 s2 = DelP t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => DelP x s1 s2) H0))
            (ap (fun x => DelP t0 x s2) H1)) (ap (fun x => DelP t0 t1 x) H2)).
Qed.

Fixpoint subst_proc (sigma_ch : nat -> ch) (s : proc) {struct s} : proc :=
  match s with
  | EndP => EndP
  | WaitP s0 s1 => WaitP (subst_ch sigma_ch s0) (subst_proc sigma_ch s1)
  | CloseP s0 s1 => CloseP (subst_ch sigma_ch s0) (subst_proc sigma_ch s1)
  | ResP s0 => ResP (subst_proc (up_ch_ch (up_ch_ch sigma_ch)) s0)
  | ParP s0 s1 => ParP (subst_proc sigma_ch s0) (subst_proc sigma_ch s1)
  | InSP s0 s1 =>
      InSP (subst_ch sigma_ch s0) (subst_proc (up_ch_ch sigma_ch) s1)
  | DelP s0 s1 s2 =>
      DelP (subst_ch sigma_ch s0) (subst_ch sigma_ch s1)
        (subst_proc sigma_ch s2)
  end.

Fixpoint idSubst_proc (sigma_ch : nat -> ch)
(Eq_ch : forall x, sigma_ch x = var_ch x) (s : proc) {struct s} :
subst_proc sigma_ch s = s :=
  match s with
  | EndP => congr_EndP
  | WaitP s0 s1 =>
      congr_WaitP (idSubst_ch sigma_ch Eq_ch s0)
        (idSubst_proc sigma_ch Eq_ch s1)
  | CloseP s0 s1 =>
      congr_CloseP (idSubst_ch sigma_ch Eq_ch s0)
        (idSubst_proc sigma_ch Eq_ch s1)
  | ResP s0 =>
      congr_ResP
        (idSubst_proc (up_ch_ch (up_ch_ch sigma_ch))
           (upId_ch_ch _ (upId_ch_ch _ Eq_ch)) s0)
  | ParP s0 s1 =>
      congr_ParP (idSubst_proc sigma_ch Eq_ch s0)
        (idSubst_proc sigma_ch Eq_ch s1)
  | InSP s0 s1 =>
      congr_InSP (idSubst_ch sigma_ch Eq_ch s0)
        (idSubst_proc (up_ch_ch sigma_ch) (upId_ch_ch _ Eq_ch) s1)
  | DelP s0 s1 s2 =>
      congr_DelP (idSubst_ch sigma_ch Eq_ch s0)
        (idSubst_ch sigma_ch Eq_ch s1) (idSubst_proc sigma_ch Eq_ch s2)
  end.

Fixpoint ext_proc (sigma_ch : nat -> ch) (tau_ch : nat -> ch)
(Eq_ch : forall x, sigma_ch x = tau_ch x) (s : proc) {struct s} :
subst_proc sigma_ch s = subst_proc tau_ch s :=
  match s with
  | EndP => congr_EndP
  | WaitP s0 s1 =>
      congr_WaitP (ext_ch sigma_ch tau_ch Eq_ch s0)
        (ext_proc sigma_ch tau_ch Eq_ch s1)
  | CloseP s0 s1 =>
      congr_CloseP (ext_ch sigma_ch tau_ch Eq_ch s0)
        (ext_proc sigma_ch tau_ch Eq_ch s1)
  | ResP s0 =>
      congr_ResP
        (ext_proc (up_ch_ch (up_ch_ch sigma_ch)) (up_ch_ch (up_ch_ch tau_ch))
           (upExt_ch_ch _ _ (upExt_ch_ch _ _ Eq_ch)) s0)
  | ParP s0 s1 =>
      congr_ParP (ext_proc sigma_ch tau_ch Eq_ch s0)
        (ext_proc sigma_ch tau_ch Eq_ch s1)
  | InSP s0 s1 =>
      congr_InSP (ext_ch sigma_ch tau_ch Eq_ch s0)
        (ext_proc (up_ch_ch sigma_ch) (up_ch_ch tau_ch)
           (upExt_ch_ch _ _ Eq_ch) s1)
  | DelP s0 s1 s2 =>
      congr_DelP (ext_ch sigma_ch tau_ch Eq_ch s0)
        (ext_ch sigma_ch tau_ch Eq_ch s1) (ext_proc sigma_ch tau_ch Eq_ch s2)
  end.

Fixpoint compSubstSubst_proc (sigma_ch : nat -> ch) (tau_ch : nat -> ch)
(theta_ch : nat -> ch)
(Eq_ch : forall x, funcomp (subst_ch tau_ch) sigma_ch x = theta_ch x)
(s : proc) {struct s} :
subst_proc tau_ch (subst_proc sigma_ch s) = subst_proc theta_ch s :=
  match s with
  | EndP => congr_EndP
  | WaitP s0 s1 =>
      congr_WaitP (compSubstSubst_ch sigma_ch tau_ch theta_ch Eq_ch s0)
        (compSubstSubst_proc sigma_ch tau_ch theta_ch Eq_ch s1)
  | CloseP s0 s1 =>
      congr_CloseP (compSubstSubst_ch sigma_ch tau_ch theta_ch Eq_ch s0)
        (compSubstSubst_proc sigma_ch tau_ch theta_ch Eq_ch s1)
  | ResP s0 =>
      congr_ResP
        (compSubstSubst_proc (up_ch_ch (up_ch_ch sigma_ch))
           (up_ch_ch (up_ch_ch tau_ch)) (up_ch_ch (up_ch_ch theta_ch))
           (up_subst_subst_ch_ch _ _ _ (up_subst_subst_ch_ch _ _ _ Eq_ch)) s0)
  | ParP s0 s1 =>
      congr_ParP (compSubstSubst_proc sigma_ch tau_ch theta_ch Eq_ch s0)
        (compSubstSubst_proc sigma_ch tau_ch theta_ch Eq_ch s1)
  | InSP s0 s1 =>
      congr_InSP (compSubstSubst_ch sigma_ch tau_ch theta_ch Eq_ch s0)
        (compSubstSubst_proc (up_ch_ch sigma_ch) (up_ch_ch tau_ch)
           (up_ch_ch theta_ch) (up_subst_subst_ch_ch _ _ _ Eq_ch) s1)
  | DelP s0 s1 s2 =>
      congr_DelP (compSubstSubst_ch sigma_ch tau_ch theta_ch Eq_ch s0)
        (compSubstSubst_ch sigma_ch tau_ch theta_ch Eq_ch s1)
        (compSubstSubst_proc sigma_ch tau_ch theta_ch Eq_ch s2)
  end.

Lemma substSubst_proc (sigma_ch : nat -> ch) (tau_ch : nat -> ch) (s : proc)
  :
  subst_proc tau_ch (subst_proc sigma_ch s) =
  subst_proc (funcomp (subst_ch tau_ch) sigma_ch) s.
Proof.
exact (compSubstSubst_proc sigma_ch tau_ch _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_proc_pointwise (sigma_ch : nat -> ch) (tau_ch : nat -> ch) :
  pointwise_relation _ eq (funcomp (subst_proc tau_ch) (subst_proc sigma_ch))
    (subst_proc (funcomp (subst_ch tau_ch) sigma_ch)).
Proof.
exact (fun s => compSubstSubst_proc sigma_ch tau_ch _ (fun n => eq_refl) s).
Qed.

Lemma instId'_proc (s : proc) : subst_proc (var_ch) s = s.
Proof.
exact (idSubst_proc (var_ch) (fun n => eq_refl) s).
Qed.

Lemma instId'_proc_pointwise :
  pointwise_relation _ eq (subst_proc (var_ch)) id.
Proof.
exact (fun s => idSubst_proc (var_ch) (fun n => eq_refl) s).
Qed.

Class Up_proc X Y :=
    up_proc : X -> Y.

Class Up_ch X Y :=
    up_ch : X -> Y.

#[global]Instance Subst_proc : (Subst1 _ _ _) := @subst_proc.

#[global]Instance Up_ch_ch : (Up_ch _ _) := @up_ch_ch.

#[global]Instance Subst_ch : (Subst1 _ _ _) := @subst_ch.

#[global]
Instance VarInstance_ch : (Var _ _) := @var_ch.

Notation "[ sigma_ch ]" := (subst_proc sigma_ch)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_ch ]" := (subst_proc sigma_ch s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__proc" := up_proc (only printing)  : subst_scope.

Notation "↑__ch" := up_ch_ch (only printing)  : subst_scope.

Notation "[ sigma_ch ]" := (subst_ch sigma_ch)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_ch ]" := (subst_ch sigma_ch s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__ch" := up_ch (only printing)  : subst_scope.

Notation "'var'" := var_ch ( at level 1, only printing)  : subst_scope.

Notation "x '__ch'" := (@ids _ _ VarInstance_ch x)
( at level 5, format "x __ch", only printing)  : subst_scope.

Notation "x '__ch'" := (var_ch x) ( at level 5, format "x __ch")  :
subst_scope.

#[global]
Instance subst_proc_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_proc)).
Proof.
exact (fun f_ch g_ch Eq_ch s t Eq_st =>
       eq_ind s (fun t' => subst_proc f_ch s = subst_proc g_ch t')
         (ext_proc f_ch g_ch Eq_ch s) t Eq_st).
Qed.

#[global]
Instance subst_proc_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_proc)).
Proof.
exact (fun f_ch g_ch Eq_ch s => ext_proc f_ch g_ch Eq_ch s).
Qed.

#[global]
Instance subst_ch_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_ch)).
Proof.
exact (fun f_ch g_ch Eq_ch s t Eq_st =>
       eq_ind s (fun t' => subst_ch f_ch s = subst_ch g_ch t')
         (ext_ch f_ch g_ch Eq_ch s) t Eq_st).
Qed.

#[global]
Instance subst_ch_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_ch)).
Proof.
exact (fun f_ch g_ch Eq_ch s => ext_ch f_ch g_ch Eq_ch s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_ch, Var, ids, Subst_ch, Subst1,
                      subst1, Up_ch_ch, Up_ch, up_ch, Subst_proc, Subst1,
                      subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_ch, Var, ids,
                                            Subst_ch, Subst1, subst1,
                                            Up_ch_ch, Up_ch, up_ch,
                                            Subst_proc, Subst1, subst1 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_proc_pointwise
                 | progress setoid_rewrite substSubst_proc
                 | progress setoid_rewrite substSubst_ch_pointwise
                 | progress setoid_rewrite substSubst_ch
                 | progress setoid_rewrite instId'_proc_pointwise
                 | progress setoid_rewrite instId'_proc
                 | progress setoid_rewrite varL'_ch_pointwise
                 | progress setoid_rewrite varL'_ch
                 | progress setoid_rewrite instId'_ch_pointwise
                 | progress setoid_rewrite instId'_ch
                 | progress unfold up_ch_ch, up_ren
                 | progress cbn[subst_proc subst_ch]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_ch, Var, ids, Subst_ch, Subst1, subst1,
                  Up_ch_ch, Up_ch, up_ch, Subst_proc, Subst1, subst1 
                  in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold.

Ltac renamify := auto_unfold.

End Core.

Module Extra.

Import Core.

#[global]Hint Opaque subst_proc: rewrite.

#[global]Hint Opaque subst_ch: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

