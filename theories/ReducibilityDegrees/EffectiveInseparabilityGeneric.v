(* The shared skeleton of ReducibilityDegrees/EffectiveInseparability.v's
   Section Mη and Models/EffectiveInseparability_L.v: both build a
   diagonal/race argument establishing effective inseparability, differing
   only in HOW they get an L-term/index η representing the race -- one via
   the abstract EA typeclass's S-m-n property (EAS), the other via
   LMuRecursion.mu applied to a hand-extracted predicate over T_L. This file
   factors out everything else (raceVal, the A0/B1 membership-at-the-
   diagonal argument, enumerability, the final assembly) into one theorem
   parametrized by an abstract W plus an "η exists and agrees with raceVal"
   hypothesis, so both constructions can be shown to be *instances* of the
   same argument instead of independently-proved lookalikes. *)

From SyntheticComputability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts Definitions.
Require Import SyntheticComputability.Shared.partial.
Require Import SyntheticComputability.Shared.embed_nat.
(* Only for enum_iff (a plain enumerable <-> semi_decidable fact that
   happens to live in this file) -- NOT for the EA typeclass itself; this
   file never assumes/constructs an EA instance, so no axiom dependency
   is introduced by this import. *)
Require Import SyntheticComputability.Axioms.EA.

Require Import ssreflect.

Section EffInsepShape.

Context {Part : partiality}.

(* Exactly ReducibilityDegrees/EffectiveInseparability.v's `eff_insep`, with
   the abstract-EA-derived W replaced by an explicit parameter. *)
Definition eff_insep_shape (W : nat -> nat -> Prop) (A B : nat -> Prop) : Prop :=
  enumerable A /\ enumerable B /\
  (forall x, A x -> ~ B x) /\
  exists f : nat -> nat -> part nat,
    forall i j,
    (forall x, A x -> W i x) ->
    (forall x, B x -> W j x) ->
    (forall x, W i x -> ~ W j x) ->
    exists k, hasvalue (f i j) k /\ ~ W i k /\ ~ W j k.

End EffInsepShape.

Section EffInsepGeneric.

Context {Part : partiality}.
Variable W : nat -> nat -> Prop.
Variable semidec_of : nat -> nat -> nat -> bool.
Hypothesis semidec_of_spec : forall c, semi_decider (semidec_of c) (W c).

Variable Θ_ours : nat -> nat -> part nat.

Definition raceVal_g (i j y : nat) : part nat :=
  bind (mu (fun n => ret (orb (semidec_of i (embed (y,y)) n) (semidec_of j (embed (y,y)) n))))
       (fun n => if semidec_of i (embed (y,y)) n then ret 0 else ret 1).

Definition A0_g (z : nat) : Prop := Θ_ours (fst (unembed z)) (snd (unembed z)) =! 1.
Definition B1_g (z : nat) : Prop := Θ_ours (fst (unembed z)) (snd (unembed z)) =! 0.

Variable η : nat -> nat -> nat.
Hypothesis Hθη : forall i j y v, Θ_ours (η i j) y =! v <-> raceVal_g i j y =! v.

Lemma A0_at_k_g i j : A0_g (embed (η i j, η i j)) <-> raceVal_g i j (η i j) =! 1.
Proof. rewrite /A0_g embedP /=. exact: Hθη. Qed.

Lemma B1_at_k_g i j : B1_g (embed (η i j, η i j)) <-> raceVal_g i j (η i j) =! 0.
Proof. rewrite /B1_g embedP /=. exact: Hθη. Qed.

Lemma raceVal_iff_race_g i j y v :
  raceVal_g i j y =! v <->
    exists n,
      (semidec_of i (embed (y,y)) n = true \/ semidec_of j (embed (y,y)) n = true) /\
      (forall m, m < n -> semidec_of i (embed (y,y)) m = false
                        /\ semidec_of j (embed (y,y)) m = false) /\
      (if semidec_of i (embed (y,y)) n then v = 0 else v = 1).
Proof.
unfold raceVal_g.
split.
- intros [n [Hmu Hbranch]] % bind_hasvalue.
  apply mu_hasvalue in Hmu as [Htrue Hforall].
  simpl in Htrue, Hbranch, Hforall.
  apply ret_hasvalue_inv in Htrue.
  apply Bool.orb_true_iff in Htrue.
  exists n. split; [exact Htrue |]. split.
  + intros m Hlt.
    specialize (Hforall m Hlt).
    apply ret_hasvalue_inv in Hforall.
    apply Bool.orb_false_iff in Hforall.
    exact Hforall.
  + destruct (semidec_of i (embed (y, y)) n) eqn:EA.
    * apply ret_hasvalue_inv in Hbranch. symmetry. exact Hbranch.
    * apply ret_hasvalue_inv in Hbranch. symmetry. exact Hbranch.
- intros [n [Hor [Hlt Hval]]].
  apply bind_hasvalue.
  exists n. split.
  + apply mu_hasvalue. split.
    * simpl. apply ret_hasvalue'. apply Bool.orb_true_iff. exact Hor.
    * intros m Hm. simpl. apply ret_hasvalue'. apply Bool.orb_false_iff. exact (Hlt m Hm).
  + simpl. destruct (semidec_of i (embed (y,y)) n) eqn:EA.
    * rewrite Hval. apply ret_hasvalue.
    * rewrite Hval. apply ret_hasvalue.
Qed.

Lemma raceVal_wins_left_g i j y :
  (exists n, semidec_of i (embed (y,y)) n = true) ->
  (forall n, semidec_of j (embed (y,y)) n = false) ->
  raceVal_g i j y =! 0.
Proof.
intros [n0 Hn0] Hjfalse.
destruct (mu_tot_ter Hn0) as [n Hn].
apply mu_tot_hasvalue in Hn as [Htrue Hmin].
apply raceVal_iff_race_g.
exists n. split; [left; exact Htrue |].
split.
- intros m Hlt. split; [apply Hmin; exact Hlt | apply Hjfalse].
- rewrite Htrue. reflexivity.
Qed.

Lemma raceVal_wins_right_g i j y :
  (exists n, semidec_of j (embed (y,y)) n = true) ->
  (forall n, semidec_of i (embed (y,y)) n = false) ->
  raceVal_g i j y =! 1.
Proof.
intros [n0 Hn0] Hifalse.
destruct (mu_tot_ter Hn0) as [n Hn].
apply mu_tot_hasvalue in Hn as [Htrue Hmin].
apply raceVal_iff_race_g.
exists n. split; [right; exact Htrue |].
split.
- intros m Hlt. split; [apply Hifalse | apply Hmin; exact Hlt].
- rewrite (Hifalse n). reflexivity.
Qed.

Lemma A0_g_enumerable : enumerable A0_g.
Proof.
apply (proj2 (enum_iff A0_g)).
exists (fun z n =>
  match seval (Θ_ours (fst (unembed z)) (snd (unembed z))) n with
  | Some v => Nat.eqb v 1
  | None => false
  end).
intros z. unfold A0_g. split.
- intros [n Hn] % seval_hasvalue.
  exists n. rewrite Hn. apply PeanoNat.Nat.eqb_refl.
- intros [n Hn].
  destruct (seval (Θ_ours (fst (unembed z)) (snd (unembed z))) n) as [v0|] eqn:E;
    [| discriminate].
  apply PeanoNat.Nat.eqb_eq in Hn. subst v0.
  apply seval_hasvalue. exists n. exact E.
Qed.

Lemma B1_g_enumerable : enumerable B1_g.
Proof.
apply (proj2 (enum_iff B1_g)).
exists (fun z n =>
  match seval (Θ_ours (fst (unembed z)) (snd (unembed z))) n with
  | Some v => Nat.eqb v 0
  | None => false
  end).
intros z. unfold B1_g. split.
- intros [n Hn] % seval_hasvalue.
  exists n. rewrite Hn. apply PeanoNat.Nat.eqb_refl.
- intros [n Hn].
  destruct (seval (Θ_ours (fst (unembed z)) (snd (unembed z))) n) as [v0|] eqn:E;
    [| discriminate].
  apply PeanoNat.Nat.eqb_eq in Hn. subst v0.
  apply seval_hasvalue. exists n. exact E.
Qed.

Theorem eff_insep_A0_B1_generic : eff_insep_shape W A0_g B1_g.
Proof.
split; [exact A0_g_enumerable |].
split; [exact B1_g_enumerable |].
split.
- intros z HA0 HB1.
  unfold A0_g in HA0. unfold B1_g in HB1.
  pose proof (hasvalue_det HA0 HB1) as Hcontra.
  discriminate Hcontra.
- exists (fun i j => ret (embed (η i j, η i j))).
  intros i j H1 H2 H3.
  exists (embed (η i j, η i j)).
  split; [apply ret_hasvalue |].
  assert (Hnk : ~ W i (embed (η i j, η i j))).
  { intros HWi.
    pose proof (H3 (embed (η i j, η i j)) HWi) as HWjneg.
    assert (Hiwin : exists n, semidec_of i (embed (η i j, η i j)) n = true).
    { apply (semidec_of_spec i (embed (η i j, η i j))). exact HWi. }
    assert (Hjlose : forall n, semidec_of j (embed (η i j, η i j)) n = false).
    { intros n.
      destruct (semidec_of j (embed (η i j, η i j)) n) eqn:Ej; [exfalso | reflexivity].
      apply HWjneg. apply (semidec_of_spec j (embed (η i j, η i j))).
      exists n. exact Ej.
    }
    pose proof (raceVal_wins_left_g i j (η i j) Hiwin Hjlose) as Hrace0.
    pose proof (proj2 (B1_at_k_g i j) Hrace0) as HB1k.
    apply HWjneg. apply H2. exact HB1k.
  }
  split; [exact Hnk |].
  intros HWj.
  assert (Hjwin : exists n, semidec_of j (embed (η i j, η i j)) n = true).
  { apply (semidec_of_spec j (embed (η i j, η i j))). exact HWj. }
  assert (Hilose : forall n, semidec_of i (embed (η i j, η i j)) n = false).
  { intros n.
    destruct (semidec_of i (embed (η i j, η i j)) n) eqn:Ei; [exfalso | reflexivity].
    apply Hnk. apply (semidec_of_spec i (embed (η i j, η i j))).
    exists n. exact Ei.
  }
  pose proof (raceVal_wins_right_g i j (η i j) Hjwin Hilose) as Hrace1.
  pose proof (proj2 (A0_at_k_g i j) Hrace1) as HA0k.
  apply Hnk. apply H1. exact HA0k.
Qed.

End EffInsepGeneric.
