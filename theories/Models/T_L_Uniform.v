(* Builds a SINGLE, uniform L-term realizing T_L c x (searching for the
   first n where it halts and returning that value), taking (c,x) as
   RUNTIME bound L-variables -- not a per-instance construction. Possible
   now that T_L_Extract.v establishes T_L is genuinely, uniformly
   extractable. Mirrors Undecidability/EffectiveInseparability_MM2_Race.v's
   s_race/raceVal_MM2 construction closely, but for a single T_L lookup
   instead of a race between two semideciders. *)

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.T_L_Extract.
Require Import Undecidability.L.Tactics.LTactics.
Require Import Undecidability.L.Util.L_facts.
Require Import Undecidability.L.Datatypes.LNat.
Require Import Undecidability.L.Datatypes.LOptions.
Require Import Undecidability.L.Datatypes.LBool.
Require Import Undecidability.L.Datatypes.LTerm.
Require Import SyntheticComputability.Shared.partial.
Require Import SyntheticComputability.Shared.embed_nat.

Require Import ssreflect.

(* --- 0. TL_val, as a plain Gallina partial function --------------------- *)

Definition TL_bit (c x n : nat) : bool :=
  match T_L' c x n with Some _ => true | None => false end.

Instance TL_bit_computable : computable TL_bit.
Proof. extract. Qed.

Definition TL_val (c x : nat) : part nat :=
  bind (mu (fun n => ret (TL_bit c x n)))
       (fun n => match T_L' c x n with Some m => ret m | None => ret 0 end).

Lemma TL_val_iff c x v :
  TL_val c x =! v <->
    exists n,
      (TL_bit c x n = true) /\
      (forall m, m < n -> TL_bit c x m = false) /\
      T_L' c x n = Some v.
Proof.
unfold TL_val.
split.
- intros [n [Hmu Hbranch]] % bind_hasvalue.
  apply mu_hasvalue in Hmu as [Htrue Hforall].
  simpl in Htrue, Hbranch, Hforall.
  apply (@ret_hasvalue_inv partial.implementation.monotonic_functions) in Htrue.
  exists n. split; [exact Htrue |]. split.
  + intros m Hlt.
    specialize (Hforall m Hlt).
    now apply (@ret_hasvalue_inv partial.implementation.monotonic_functions) in Hforall.
  + destruct (T_L' c x n) as [v'|] eqn:E.
    * apply (@ret_hasvalue_inv partial.implementation.monotonic_functions) in Hbranch. congruence.
    * exfalso. unfold TL_bit in Htrue. rewrite E in Htrue. discriminate.
- intros [n [Htrue [Hlt Hval]]].
  apply bind_hasvalue.
  exists n. split.
  + apply mu_hasvalue. split.
    * simpl. apply (@ret_hasvalue' partial.implementation.monotonic_functions). exact Htrue.
    * intros m Hm. simpl. now apply (@ret_hasvalue' partial.implementation.monotonic_functions), Hlt.
  + simpl. rewrite Hval. apply (@ret_hasvalue partial.implementation.monotonic_functions).
Qed.

(* --- 1. A single 2-argument L term realizing the whole T_L family ------
   Structurally s_race's shape (EffectiveInseparability_MM2_Race.v), but
   with a single T_L' lookup instead of a race between two semideciders,
   and OPTION elimination (T_L' returns option nat, not bool) instead of
   boolean elimination -- reusing PerInstanceGuard.v's someHandler=identity
   idiom (no Omega/divergence needed here: the None branch is logically
   unreachable once mu has found n with TL_bit c x n = true, so any
   placeholder value for it is fine). *)

Require SyntheticComputability.Models.LMuRecursion.

Definition s_TL : term :=
  lam (lam (
    L.app
      (L.app
        (L.app (L.app (L.app (ext T_L') (var 1)) (var 0))
               (L.app LMuRecursion.mu
                      (lam (L.app (L.app (L.app (ext TL_bit) (var 2)) (var 1)) (var 0)))))
        (lam (var 0)))
      (enc 0)
  )).

Lemma s_TL_proc : proc s_TL.
Proof.
pose proof LMuRecursion.mu_proc.
pose proof (proc_ext T_L'_computable).
pose proof (proc_ext TL_bit_computable).
unfold s_TL. Lproc.
Qed.

(* TLP c x: same search predicate as inlined inside s_TL, but as a
   standalone term with c,x baked in via Gallina currying -- connected to
   s_TL's own inlined (de Bruijn-referencing) copy by s_TL_reduce below,
   mirroring raceP_MM2/s_race_reduce's role in
   EffectiveInseparability_MM2_Race.v. *)
Definition TLP (c x : nat) : term :=
  lam (L.app (L.app (L.app (ext TL_bit) (enc c)) (enc x)) (var 0)).

Lemma TLP_proc c x : proc (TLP c x).
Proof.
pose proof (proc_ext TL_bit_computable).
unfold TLP. Lproc.
Qed.

Lemma TLP_dec c x : forall n : nat, exists b : bool, L.app (TLP c x) (ext n) == ext b.
Proof.
intros n. unfold TLP. eexists. now Lsimpl.
Qed.

Lemma s_TL_reduce c x :
  L.app (L.app s_TL (enc c)) (enc x) ==
  L.app
    (L.app
       (L.app
          (L.app (L.app (ext T_L') (enc c)) (enc x))
          (L.app LMuRecursion.mu (TLP c x)))
       (lam (var 0)))
    (enc 0).
Proof.
unfold s_TL, TLP.
apply star_equiv.
etransitivity.
{ apply star_trans_l, step_star, step_beta; [reflexivity | Lproc]. }
etransitivity.
{ apply step_star, step_beta; [reflexivity | Lproc]. }
cbn [subst Nat.eqb nat_enc].
assert (HT : forall n t, subst (ext T_L') n t = ext T_L')
  by (intros; apply SyntheticComputability.Models.CT.closed_subst;
      now apply proc_closed, proc_ext).
assert (HB : forall n t, subst (ext TL_bit) n t = ext TL_bit)
  by (intros; apply SyntheticComputability.Models.CT.closed_subst;
      now apply proc_closed, proc_ext).
assert (HM : forall n t, subst LMuRecursion.mu n t = LMuRecursion.mu)
  by (intros; apply SyntheticComputability.Models.CT.closed_subst;
      now apply proc_closed, LMuRecursion.mu_proc).
assert (HE : forall (k n : nat) (t : term), subst (enc k) n t = enc k)
  by (intros; apply SyntheticComputability.Models.CT.closed_subst;
      now apply proc_closed, proc_enc).
rewrite !HT.
rewrite !HB.
rewrite !HM.
rewrite !HE.
reflexivity.
Qed.

Require Undecidability.L.Functions.Eval.
Require Undecidability.L.Computability.Seval.
Notation enc_extinj := Undecidability.L.Computability.Computability.enc_extinj.

Lemma s_TL_full_reduce c x v :
  L.app (L.app s_TL (enc c)) (enc x) == enc v
  <-> exists n, L.app LMuRecursion.mu (TLP c x) == enc n /\ T_L' c x n = Some v.
Proof.
rewrite s_TL_reduce.
split.
- intros H.
  assert (Hconv0 :
    converges
      (L.app
         (L.app
            (L.app
               (L.app (L.app (ext T_L') (enc c)) (enc x))
               (L.app LMuRecursion.mu (TLP c x)))
            (lam (var 0)))
         (enc 0)))
    by (eexists; split; [exact H | Lproc]).
  apply Seval.app_converges in Hconv0 as [Hconv1 _].
  apply Seval.app_converges in Hconv1 as [Hconv2 _].
  apply Seval.app_converges in Hconv2 as [_ Hconv].
  destruct Hconv as [vn [Hvn Hlvn]].
  destruct (LMuRecursion.mu_sound (TLP_proc c x) (TLP_dec c x) Hlvn Hvn) as [n [-> [Htrue _]]].
  exists n. split; [exact Hvn |].
  assert (Htrue' : TL_bit c x n = true).
  { unfold TLP in Htrue. LsimplHypo. Lrewrite in Htrue. symmetry in Htrue.
    now apply enc_extinj in Htrue. }
  unfold TL_bit in Htrue'.
  destruct (T_L' c x n) as [v'|] eqn:E; [| discriminate].
  rewrite Hvn in H.
  assert (Hcore :
    L.app (L.app (L.app (ext T_L') (enc c)) (enc x)) (enc n) == ext (T_L' c x n))
    by now Lsimpl.
  rewrite E in Hcore. rewrite Hcore in H.
  assert (Hunwrap :
    L.app (L.app (ext (Some v')) (lam (var 0))) (enc 0) == enc v')
    by now Lsimpl.
  rewrite Hunwrap in H.
  symmetry in H. apply enc_extinj in H. congruence.
- intros [n [Hmu Hval]].
  rewrite Hmu.
  transitivity
    (L.app (L.app (ext (T_L' c x n)) (lam (var 0))) (enc 0)); [now Lsimpl |].
  rewrite Hval. now Lsimpl.
Qed.

Lemma minimal_unique (P : nat -> bool) (n1 n2 : nat) :
  P n1 = true -> (forall m, m < n1 -> P m = false) ->
  P n2 = true -> (forall m, m < n2 -> P m = false) ->
  n1 = n2.
Proof.
intros H1 Hm1 H2 Hm2.
destruct (Compare_dec.lt_eq_lt_dec n1 n2) as [[Hlt|Heq]|Hgt]; auto.
- specialize (Hm2 n1 Hlt). congruence.
- specialize (Hm1 n2 Hgt). congruence.
Qed.

Lemma s_TL_val_iff c x v :
  L.app (L.app s_TL (enc c)) (enc x) == enc v
  <-> TL_val c x =! v.
Proof.
rewrite s_TL_full_reduce.
rewrite TL_val_iff.
split.
- intros [n [Hmu Hval]].
  destruct (LMuRecursion.mu_sound (TLP_proc c x) (TLP_dec c x) (proc_lambda (proc_enc n)) Hmu)
    as [n' [Heq [Htrue Hmin]]].
  rewrite ext_is_enc in Heq. apply inj_enc in Heq. subst n'.
  assert (Htrue' : TL_bit c x n = true).
  { unfold TLP in Htrue. LsimplHypo. Lrewrite in Htrue. symmetry in Htrue.
    now apply enc_extinj in Htrue. }
  assert (Hmin' : forall m, m < n -> TL_bit c x m = false).
  { intros m Hlt. specialize (Hmin m Hlt). unfold TLP in Hmin.
    LsimplHypo. Lrewrite in Hmin. symmetry in Hmin.
    now apply enc_extinj in Hmin. }
  exists n. split; [exact Htrue' |]. split; [exact Hmin' | exact Hval].
- intros [n [Htrue [Hmin Hv]]].
  assert (HPtrue : L.app (TLP c x) (ext n) == ext true).
  { unfold TLP. Lsimpl. now rewrite Htrue. }
  destruct (LMuRecursion.mu_complete (TLP_proc c x) (TLP_dec c x) HPtrue) as [n0 Hn0].
  destruct (LMuRecursion.mu_sound (TLP_proc c x) (TLP_dec c x) (proc_lambda (proc_enc n0)) Hn0)
    as [n0' [Heq0 [Htrue0 Hmin0]]].
  rewrite ext_is_enc in Heq0. apply inj_enc in Heq0. subst n0'.
  assert (Htrue0' : TL_bit c x n0 = true).
  { unfold TLP in Htrue0. LsimplHypo. Lrewrite in Htrue0. symmetry in Htrue0.
    now apply enc_extinj in Htrue0. }
  assert (Hmin0' : forall m, m < n0 -> TL_bit c x m = false).
  { intros m Hm. specialize (Hmin0 m Hm). unfold TLP in Hmin0.
    LsimplHypo. Lrewrite in Hmin0. symmetry in Hmin0.
    now apply enc_extinj in Hmin0. }
  assert (Hn0n : n0 = n) by (eapply minimal_unique; eauto).
  subst n0. exists n. split; [exact Hn0 | exact Hv].
Qed.

Lemma s_TL_applied_terminal (c x : nat) o :
  L.app (L.app s_TL (enc c)) (enc x) == o -> lambda o ->
  exists m : nat, o = enc m.
Proof.
intros H Ho.
rewrite s_TL_reduce in H.
assert (Hconv0 :
  converges
    (L.app
       (L.app
          (L.app
             (L.app (L.app (ext T_L') (enc c)) (enc x))
             (L.app LMuRecursion.mu (TLP c x)))
          (lam (var 0)))
       (enc 0)))
  by (eexists; split; [exact H | exact Ho]).
apply Seval.app_converges in Hconv0 as [Hconv1 _].
apply Seval.app_converges in Hconv1 as [Hconv2 _].
apply Seval.app_converges in Hconv2 as [_ Hconv].
destruct Hconv as [vn [Hvn Hlvn]].
destruct (LMuRecursion.mu_sound (TLP_proc c x) (TLP_dec c x) Hlvn Hvn) as [n [-> [Htrue _]]].
assert (Htrue' : TL_bit c x n = true).
{ unfold TLP in Htrue. LsimplHypo. Lrewrite in Htrue. symmetry in Htrue.
  now apply enc_extinj in Htrue. }
unfold TL_bit in Htrue'.
destruct (T_L' c x n) as [v'|] eqn:E; [| discriminate].
rewrite Hvn in H.
assert (Hcore :
  L.app (L.app (L.app (ext T_L') (enc c)) (enc x)) (enc n) == ext (T_L' c x n))
  by now Lsimpl.
rewrite E in Hcore. rewrite Hcore in H.
assert (Hunwrap :
  L.app (L.app (ext (Some v')) (lam (var 0))) (enc 0) == enc v')
  by now Lsimpl.
rewrite Hunwrap in H.
exists v'. eapply unique_normal_forms; [exact Ho | apply proc_enc |].
now symmetry.
Qed.

(* --- 2. L_computable_closed R_TL ---------------------------------------- *)

From Stdlib Require Import Vector.
Import VectorNotations.

Definition R_TL (v : Vector.t nat 2) (m : nat) : Prop :=
  TL_val (Vector.hd v) (Vector.hd (Vector.tl v)) =! m.

Lemma vector1_eta (A : Type) (w : Vector.t A 1) : w = [Vector.hd w].
Proof.
transitivity (Vector.hd w :: Vector.tl w).
- apply VectorSpec.eta.
- now rewrite (VectorSpec.nil_spec (Vector.tl w)).
Qed.

Lemma vector2_eta (A : Type) (v : Vector.t A 2) :
  v = [Vector.hd v; Vector.hd (Vector.tl v)].
Proof.
transitivity (Vector.hd v :: Vector.tl v).
- apply VectorSpec.eta.
- now rewrite (vector1_eta (Vector.tl v)).
Qed.

Lemma equiv_enc_eval s (v : nat) : s == enc v -> L.eval s (enc v).
Proof.
intros H. apply eval_iff. split; [| apply proc_enc].
apply equiv_lambda; [apply proc_enc | exact H].
Qed.

Lemma eval_enc_equiv s (v : nat) : L.eval s (enc v) -> s == enc v.
Proof.
intros H % eval_iff. destruct H as [H _]. now apply star_equiv.
Qed.

Lemma L_computable_closed_R_TL : L_computable_closed R_TL.
Proof.
exists s_TL. split.
{ destruct s_TL_proc as [Hc _]. exact Hc. }
intros v.
rewrite (vector2_eta v).
set (c := Vector.hd v). set (x := Vector.hd (Vector.tl v)).
unfold R_TL. cbn [Vector.hd Vector.tl Vector.fold_left].
split.
- intros m. rewrite <- s_TL_val_iff. split.
  + intros H % equiv_enc_eval. exact H.
  + intros H % eval_enc_equiv. exact H.
- intros o Ho % eval_iff.
  destruct Ho as [Ho1 Ho2].
  eapply s_TL_applied_terminal; [now apply star_equiv | exact Ho2].
Qed.

