(* Per-instance L_computable_closed bridge, built for a KNOWN closed term
   t_c and a known x_L (both fixed at Gallina/meta level, not runtime
   input). This is the piece that lets EffectiveInseparability_L.v's
   already-proven eff_insep_A0_B1_L be transported to a *different*
   numbering (e.g. R_target/MM2, via Undecidability/mm.v's existing
   L_computable_closed -> MM2_computable compiler chain) via a PLAIN,
   non-self-referential reduction, instead of needing an MM2-native race
   construction. See project memory (2026-08-06) for the overall
   architecture this is a piece of.

   Since t_c is an ARBITRARY closed term, `L.app t_c (enc x_L)` might
   converge to something that is *not* nat-shaped (or might not converge
   at all). L_computable_closed's second conjunct demands that every
   convergent output IS nat-shaped, so we can't just hand over t_c's
   raw application -- we have to GUARD it: run it via Eval (the
   unbounded-fuel self-interpreter), try to decode the result with
   nat_unenc, and diverge (via Omega) if that fails.

   The one subtlety: under weak call-by-value, a term passed as an
   ordinary (eagerly evaluated) argument must already be a value. You
   cannot pass Omega itself as one of the two branch-arguments of the
   option eliminator (as e.g. ClosedLAdmissible.v's total_decodable_closed_new
   does with a `ext false` placeholder) -- CBV would force it
   unconditionally and the WHOLE term would diverge regardless of which
   branch is selected. Instead both branches are THUNKS (`lam
   (lam (var 1))` for Some, `lam Omega` for None), and the selected thunk
   is forced by one trailing application of `I`, exactly mirroring the
   `... (lam Omega) ... I` idiom already used in
   Acceptability.v / LBool.v's trueOrDiverge. *)

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.Seval.
Require Import Undecidability.L.Tactics.LTactics.
Require Import Undecidability.L.Util.L_facts.
Require Import Undecidability.L.Datatypes.LNat.
Require Import Undecidability.L.Datatypes.LOptions.
Require Import Undecidability.L.Functions.Eval.
Require Import Undecidability.L.Util.NaryApp.

Instance nat_unenc_computable : computable nat_unenc.
Proof. extract. Qed.

Section Wrapper.

Variable (t_c : term) (Ht_c : closed t_c) (x_L : nat).

Definition s0 : term := L.app t_c (enc x_L).

Definition someHandler : term := lam (lam (var 1)).
Definition noneHandler : term := lam Omega.

Definition guarded : term :=
  L.app
    (L.app
       (L.app (L.app (ext nat_unenc) (L.app Eval (ext s0))) someHandler)
       noneHandler)
    I.

Lemma s0_closed : closed s0.
Proof. unfold s0. Lproc. Qed.

Lemma Eval_closed : closed Eval.
Proof. unfold Eval. Lproc. Qed.

Lemma Omega_closed : closed Omega.
Proof. unfold Omega, omega. Lproc. Qed.

Lemma guarded_closed : closed guarded.
Proof.
  unfold guarded, someHandler, noneHandler.
  pose proof Eval_closed. pose proof Omega_closed. pose proof s0_closed.
  Lproc.
Qed.

Lemma guarded_correct_some (m : nat) :
  s0 == enc m -> guarded == enc m.
Proof.
  intros H.
  assert (Hev : eval s0 (enc m)).
  { split; [eapply equiv_lambda; [Lproc | exact H] | Lproc]. }
  eapply eval_Eval in Hev.
  unfold guarded.
  rewrite Hev.
  unfold someHandler, noneHandler, I.
  Lsimpl.
  rewrite unenc_correct.
  Lsimpl.
  reflexivity.
Qed.

Lemma guarded_eval_case (o : term) :
  eval guarded o -> exists m : nat, eval s0 (enc m) /\ o = enc m.
Proof.
  intros [Hred Hlam].
  assert (Hgo : guarded == o) by (apply star_equiv_subrelation, Hred).
  assert (Hc : converges guarded) by (exists o; split; assumption).
  unfold guarded in Hc.
  apply app_converges in Hc as [Hc _].
  apply app_converges in Hc as [Hc _].
  apply app_converges in Hc as [Hc _].
  apply app_converges in Hc as [_ Hc].
  apply Eval_converges in Hc.
  destruct (eval_converges Hc) as [t' Ht'].
  pose proof (eval_Eval Ht') as HEv.
  destruct (nat_unenc t') as [k|] eqn:Hk.
  - apply unenc_correct2 in Hk. subst t'.
    exists k. split; [exact Ht' |].
    assert (Hg : guarded == enc k).
    { unfold guarded. rewrite HEv. unfold someHandler, noneHandler, I.
      Lsimpl. rewrite unenc_correct. Lsimpl. reflexivity. }
    apply unique_normal_forms; [exact Hlam | Lproc | rewrite <- Hgo; exact Hg].
  - exfalso.
    assert (Hg : guarded == Omega).
    { unfold guarded. rewrite HEv. unfold someHandler, noneHandler, I.
      Lsimpl. rewrite Hk.
      apply beta_red; [Lproc | rewrite subst_closed; [reflexivity | exact Omega_closed]]. }
    rewrite Hgo in Hg. destruct Hlam as [u ->].
    symmetry in Hg. eapply Omega_diverges. exact Hg.
Qed.

Lemma guarded_output_shape (o : term) :
  eval guarded o -> exists m : nat, o = enc m.
Proof.
  intros H % guarded_eval_case. destruct H as [m [_ ->]]. now exists m.
Qed.

Lemma guarded_correct (m : nat) :
  s0 == enc m <-> eval guarded (enc m).
Proof.
  split.
  - intros H. split.
    + eapply equiv_lambda; [Lproc | now apply guarded_correct_some].
    + Lproc.
  - intros H % guarded_eval_case. destruct H as [k [Hk Heq]].
    rewrite Heq. destruct Hk as [Hred _]. now apply star_equiv_subrelation.
Qed.

Definition R_tc_xL : Vector.t nat 0 -> nat -> Prop := fun _ m => s0 == enc m.

Lemma R_tc_xL_L_computable_closed : L_computable_closed R_tc_xL.
Proof.
  exists guarded. split; [exact guarded_closed |].
  intros v. revert v. eapply Vector.case0. cbn. split.
  - intros m. rewrite eval_iff. apply guarded_correct.
  - intros o H % eval_iff. now apply guarded_output_shape.
Qed.

End Wrapper.

(* The bridge from T_L's step-indexed meta-level evaluator down to L's own
   object-level equivalence, for a KNOWN c_L whose enum_closed value t_c
   has already been computed once (at the meta level, by ordinary Gallina
   evaluation -- no generic extractability of enum_closed/T_L is needed
   at all). This is what lets R_tc_xL above be re-phrased in terms of
   T_L/Theta_ours_L/A0_L. *)

Lemma T_L_known (c_L x_L m : nat) (t_c : term)
  (Henum : enum_closed c_L = Some t_c) :
  (exists n, T_L c_L x_L n = Some m) <-> L.app t_c (enc x_L) == enc m.
Proof.
split.
- intros [n Hn].
  unfold T_L in Hn. rewrite Henum in Hn.
  destruct (eva n (L.app t_c (enc x_L))) as [t'|] eqn:E; [| discriminate].
  simpl in Hn.
  apply unenc_correct2 in Hn.
  apply eva_equiv in E.
  rewrite <- Hn in E. exact E.
- intros Heq.
  eapply equiv_eva in Heq as [n Hn].
  + exists n. unfold T_L. rewrite Henum. rewrite Hn. simpl.
    now rewrite unenc_correct.
  + eapply nat_enc_proc.
Qed.

(* Putting the two pieces together: for a known c_L/x_L pair, the relation
   "T_L c_L x_L eventually outputs m" is L_computable_closed. This is the
   per-instance witness Task #3 compiles through the existing
   L_computable_closed -> MM2_computable chain. *)

Lemma R_TL_L_computable_closed (c_L x_L : nat) (t_c : term)
  (Ht_c : closed t_c) (Henum : enum_closed c_L = Some t_c) :
  L_computable_closed
    (fun _ : Vector.t nat 0 => fun m => exists n, T_L c_L x_L n = Some m).
Proof.
  destruct (@R_tc_xL_L_computable_closed t_c Ht_c x_L) as [s [Hs Hcorrect]].
  exists s. split; [exact Hs |].
  intros v. specialize (Hcorrect v). destruct Hcorrect as [H1 H2].
  split.
  - intros m. rewrite <- H1. unfold R_tc_xL. apply T_L_known, Henum.
  - exact H2.
Qed.
