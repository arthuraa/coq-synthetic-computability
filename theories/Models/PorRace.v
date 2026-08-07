(* Pure L-term-level facts about Undecidability.L.Computability.Por, exposing
   the exact step (n) at which the race resolves and which side won, not just
   "converges to some boolean" (which is all Por_correct_1a/1b/2/' give).
   Deliberately its own file, with no dependency on Shared/partial.v: this
   lets us freely Import Por/MuRec/Eval here (all of which bring an L-term
   named `mu` into unqualified scope) without it ever colliding with
   partial.mu, which is only relevant in files reasoning about the `part`
   monad -- this file only reasons about `term`/`nat`/`bool`. *)

Require Import Undecidability.L.L.
Require Import Undecidability.L.Util.L_facts.
Require Import Undecidability.L.Tactics.LTactics.
Require Import Undecidability.L.Computability.Por.
Require Import Undecidability.L.Computability.MuRec.
Require Import Undecidability.L.Functions.Eval.

Import L_Notations.

Unset Implicit Arguments.

(* A minimal witness for a boolean predicate over nat is unique -- pure
   arithmetic, no L-term reasoning needed. *)
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

Lemma Por_correct_2_precise (s t : term) :
  converges (Por (ext s) (ext t)) ->
  exists n, (doesHaltIn s n = true \/ doesHaltIn t n = true) /\
            (forall m, m < n -> doesHaltIn s m = false /\ doesHaltIn t m = false) /\
            Por (ext s) (ext t) == ext (doesHaltIn s n).
Proof.
intros [v [R lv]]. unfold Por in R. LsimplHypo.
evar (s':term). assert (C:converges s'). eexists. split. exact R. Lproc. subst s'.
apply app_converges in C as [_ [v' [C lv']]].
assert (C':=C).
apply mu_sound in C as [n [eq [R' H]]]; try Lproc.
- subst v'.
  exists n.
  assert (Hbool : orb (doesHaltIn s n) (doesHaltIn t n) = true).
  { LsimplHypo. Lrewrite in R'. now apply enc_extinj in R'. }
  assert (Hmin : forall m, m < n -> orb (doesHaltIn s m) (doesHaltIn t m) = false).
  { intros m Hm. specialize (H m Hm). LsimplHypo. Lrewrite in H. now apply enc_extinj in H. }
  split; [now apply Bool.orb_true_iff in Hbool |].
  split; [intros m Hm; specialize (Hmin m Hm); now apply Bool.orb_false_iff in Hmin |].
  unfold Por. Lsimpl. rewrite C'. now Lsimpl.
- eexists. now Lsimpl.
Qed.

Lemma Por_correct_1_precise (s t : term) (n : nat) :
  doesHaltIn s n = true \/ doesHaltIn t n = true ->
  (forall m, m < n -> doesHaltIn s m = false /\ doesHaltIn t m = false) ->
  Por (ext s) (ext t) == ext (doesHaltIn s n).
Proof.
intros Hor Hmin.
assert (Hconv : converges s \/ converges t).
{ destruct Hor as [H|H]; unfold doesHaltIn in H.
  - destruct (eva n s) eqn:E; try discriminate.
    left. apply eva_seval in E. apply seval_eval in E. eauto.
  - destruct (eva n t) eqn:E; try discriminate.
    right. apply eva_seval in E. apply seval_eval in E. eauto. }
destruct (Por_correct_2_precise s t (Por_correct_1 Hconv)) as [n' [Hor' [Hmin' Heq]]].
assert (Hn : n = n').
{ eapply minimal_unique with (P := fun m => orb (doesHaltIn s m) (doesHaltIn t m)).
  - now apply Bool.orb_true_iff.
  - intros m Hm. apply Bool.orb_false_iff. exact (Hmin m Hm).
  - now apply Bool.orb_true_iff.
  - intros m Hm. apply Bool.orb_false_iff. exact (Hmin' m Hm). }
now rewrite Hn.
Qed.

Theorem Por_race_precise (s t : term) (b : bool) :
  Por (ext s) (ext t) == ext b <->
  exists n, (doesHaltIn s n = true \/ doesHaltIn t n = true) /\
            (forall m, m < n -> doesHaltIn s m = false /\ doesHaltIn t m = false) /\
            b = doesHaltIn s n.
Proof.
split.
- intros Heq.
  assert (Hconv : converges (Por (ext s) (ext t))) by (eexists; split; [exact Heq | Lproc]).
  destruct (Por_correct_2_precise s t Hconv) as [n [Hor [Hmin Heq']]].
  exists n. split; [exact Hor |]. split; [exact Hmin |].
  rewrite Heq' in Heq. now apply enc_extinj in Heq.
- intros [n [Hor [Hmin ->]]].
  now apply Por_correct_1_precise.
Qed.
