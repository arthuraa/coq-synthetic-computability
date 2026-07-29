From SyntheticComputability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts.
Require Import SyntheticComputability.Axioms.EA.
From SyntheticComputability.ReducibilityDegrees Require Import simple.
From SyntheticComputability.CRM Require Import principles.
From SyntheticComputability.Basic Require Import Recursion.
From SyntheticComputability.Axioms Require Import EPF Equivalence.

Require Import ssreflect.

Section EffectiveInseparability.

Context {Part : partiality}.
Context {EA_inst : EA}.

Hypothesis MP_assm : MP.

Notation φ := (proj1_sig EA_inst).
Notation EAP := (proj2_sig EA_inst).

Definition eff_insep (A B : nat -> Prop) : Prop :=
  enumerable A /\ enumerable B /\
  (forall x, A x -> ~ B x) /\
  exists f : nat -> nat -> part nat,
    forall i j,
    (forall x, A x -> W i x) ->
    (forall x, B x -> W j x) ->
    (forall x, W i x -> ~ W j x) ->
    exists k, hasvalue (f i j) k /\ ~ W i k /\ ~ W j k.

(* TODO: come back to this once the builds work.
Lemma temp (A A' B : nat -> Prop) :
  enumerable A' -> eff_insep A B -> (forall x, A x -> A' x) -> (forall x, A' x -> ~ B x) -> eff_insep A' B.
*)

Lemma W_union :
  exists u : nat -> nat -> nat,
    forall j c x, W (u j c) x <-> W j x \/ W c x.
Proof.
destruct (EAS (fun jc x => W (fst (unembed jc)) x \/ W (snd (unembed jc)) x))
  as [e He].
{exists (fun k =>
  let (jc, m) := unembed k in
  let (j, c) := unembed jc in
  let (side, n) := unembed m in
  match side with
  | 0 => match φ j n with Some x => Some (jc, x) | None => None end
  | _ => match φ c n with Some x => Some (jc, x) | None => None end
  end).
intros [jc x]. split.
- intros [[n Hn] | [n Hn]];
  [exists ⟨jc, ⟨0, n⟩⟩ | exists ⟨jc, ⟨1, n⟩⟩];
  rewrite !embedP; destruct (unembed jc) as [??]; simpl in Hn;
    now rewrite Hn.
- intros [k Hk].
  destruct (unembed k) as [jc' m];
    destruct (unembed jc') as [j c] eqn:Eqjc;
    destruct (unembed m) as [side n].
  destruct side;
    [destruct (φ j n) as [x'|] eqn:Eqn | destruct (φ c n) as [x'|] eqn:Eqn];
    try discriminate;
    inversion Hk; subst; [left | right];
    exists n; rewrite Eqjc; simpl; exact Eqn.
}
exists (fun j c => e ⟨j, c⟩).
intros j c x.
specialize (He ⟨j, c⟩ x).
rewrite embedP in He.
simpl in He.
rewrite He.
reflexivity.
Qed.

Theorem eff_insep_to_creative (A B : nat -> Prop) :
  eff_insep A B -> creative A.
Proof.
intros (Ha & Hb & Hdisj & f & Hf).
split; [apply Ha |].
apply (partial_productive_iff_productive _ MP_assm).
rewrite W_spec in Ha; destruct Ha as [i Ha].
rewrite W_spec in Hb; destruct Hb as [j Hb].
destruct W_union as [u Hu].
exists (fun c => f i (u j c)).
intros c Hx.
pose proof (Hf i (u j c)) as Hf'.
set (HsupA := (fun x HAx => (proj1 (Ha x) HAx))).
assert (HsupB : forall x, B x -> W (u j c) x).
{ intros x HB % Hb. rewrite Hu. left. exact HB. }
assert (HWdisj : forall x, W i x -> ~ W (u j c) x).
{ intros x HA % Ha Huc % Hu.
  destruct Huc as [Hj | Hc].
  - apply Hb in Hj. eapply Hdisj; eauto.
  - apply Hx in Hc. exact (Hc HA).
}
specialize (Hf' HsupA HsupB HWdisj) as [k [Hk [Hki Hkj]]].
exists k.
repeat split; [exact Hk | |].
- intro HAk.
  apply Hki.
  apply Ha.
  exact HAk.
- intro Hwck.
  apply Hkj.
  apply (Hu j c k).
  right.
  exact Hwck.
Qed.

Theorem eff_insep_to_m_complete (A B : nat -> Prop):
  eff_insep A B -> m-complete A.
Proof.
intros Hinsep.
exact (creative_to_m_complete MP_assm _ (eff_insep_to_creative _ _ Hinsep)).
Qed.

End EffectiveInseparability.

Section Racing.

Definition race {X} (f g : X -> nat -> bool) (x : X) (n : nat) : option bool :=
  if      f x n then Some true
  else if g x n then Some false
  else None.

Lemma race_spec {X} {P Q : X -> Prop} f g :
  semi_decider f P ->
  semi_decider g Q ->
  (forall x, P x -> Q x -> False) ->
  forall x,
    (P x -> exists n, race f g x n = Some true) /\
    (Q x -> exists n, race f g x n = Some false) /\
    (forall n b,
        race f g x n = Some b ->
        (b = true -> P x) /\ (b = false -> Q x)).
Proof.
move=> SemiFP SemiGQ Disj x; repeat split.
- move=> /SemiFP [n Hf].
  by exists n; rewrite /race Hf.
- rewrite /race => /SemiGQ [n Hg]; exists n.
  case Ef: (f x n)=> //; last by rewrite Hg.
  exfalso; eapply Disj; [apply SemiFP | apply SemiGQ]; eauto.
- move=> B; move: H; rewrite /race {b}B.
  case E: (f x n); first by move=>_; apply SemiFP; exists n.
  by case E': (g x n); discriminate.
- move=> B; move: H; rewrite /race {b}B.
  case E: (f x n); first discriminate.
  case E': (g x n); last discriminate.
  by move=> _; apply SemiGQ; exists n.
Qed.

End Racing.

Section Mη.

Context {Part : partiality}.
Context {EA_inst : EA}.

Notation φ := (proj1_sig EA_inst).
Notation EAP := (proj2_sig EA_inst).

Local Definition recursion_EPF : EPF := SCT_to_EPF (EA_to_SCT EA_inst).
Local Notation Θ := (proj1_sig recursion_EPF).
Local Definition EPFP := proj2_sig recursion_EPF.

Definition semidec_of (c x n : nat) : bool :=
  match φ c n with Some y => Nat.eqb x y | None => false end.

Lemma semidec_of_spec c : semi_decider (semidec_of c) (W c).
Proof.
  intros x; unfold semidec_of, W; split.
  - move=> [n Hn]; exists n; rewrite Hn; apply PeanoNat.Nat.eqb_refl.
  - move=> [n Hn]; move: Hn; case E: (φ c n) => [a |]; last by discriminate.
    rewrite PeanoNat.Nat.eqb_eq => ->. by exists n.
Qed.

Definition raceVal (i j y : nat) : part nat :=
  bind (mu (fun n => ret (orb (semidec_of i (embed (y,y)) n) (semidec_of j (embed (y,y)) n))))
       (fun n => if semidec_of i (embed (y,y)) n then ret 0 else ret 1).

Definition Θ_ours (c y : nat) : part nat :=
  bind (mu (fun n => match φ c n with
                      | Some z => ret (Nat.eqb (fst (unembed z)) y)
                      | None => ret false
                      end))
       (fun n => match φ c n with
                 | Some z => ret (snd (unembed z))
                 | None => undef
                 end).

Definition A0 (z : nat) : Prop := Θ_ours (fst (unembed z)) (snd (unembed z)) =! 1.
Definition B1 (z : nat) : Prop := Θ_ours (fst (unembed z)) (snd (unembed z)) =! 0.

Definition RaceGraph (i j z : nat) : Prop :=
  raceVal i j (fst (unembed z)) =! snd (unembed z).

(* --- 1. RaceGraph enumerable, uniformly in <i,j> ------------------- *)

Definition RaceGraph' (c z : nat) : Prop :=
  RaceGraph (fst (unembed c)) (snd (unembed c)) z.

  Definition RaceGraph'_semidec (cz : nat * nat) (n : nat) : bool :=
  match seval (raceVal (fst (unembed (fst cz))) (snd (unembed (fst cz)))
                             (fst (unembed (snd cz)))) n with
  | Some v => Nat.eqb v (snd (unembed (snd cz)))
  | None   => false
  end.
Definition RaceGraph_flat (w : nat) : Prop := uncurry RaceGraph' (unembed w).

Lemma RaceGraph_flat_enumerable : enumerable RaceGraph_flat.
Proof.
apply (proj2 (enum_iff RaceGraph_flat)).
exists (fun w n =>
  let c := fst (unembed w) in let z := snd (unembed w) in
  let i := fst (unembed c) in let j := snd (unembed c) in
  let y := fst (unembed z) in let v := snd (unembed z) in
  match seval (raceVal i j y) n with
  | Some v' => Nat.eqb v' v
  | None    => false
  end).
intros w; unfold RaceGraph_flat, uncurry, RaceGraph', RaceGraph; cbn.
split.
- case E: (unembed w) => [a b] Hval.
  apply seval_hasvalue in Hval as [n Hn].
  exists n. rewrite /= Hn. apply PeanoNat.Nat.eqb_refl.
- move=> [n Hn].
  case E: (seval (raceVal (fst (unembed (fst (unembed w))))
                            (snd (unembed (fst (unembed w))))
                            (fst (unembed (snd (unembed w))))
                  ) n) Hn => /= [v' |]; last by discriminate.
  rewrite PeanoNat.Nat.eqb_eq => Hv'.
  subst v'.
  case E': (unembed w) => [a b] /=.
  apply seval_hasvalue.
  exists n. rewrite E' in E. exact E.
Qed.

Lemma RaceGraph'_enumerable_uncurried : enumerable (uncurry RaceGraph').
Proof.
  case: RaceGraph_flat_enumerable => [g Hg].
  exists (fun n => match g n with Some w => Some (unembed w) | None => None end).
  move=> [c z].
  transitivity (RaceGraph_flat (embed (c, z))).
  - rewrite /RaceGraph_flat embedP //=.
  - rewrite (Hg (embed (c, z))).
    split; move=> [n Hn]; exists n.
    + by rewrite Hn embedP.
    + case E: (g n) Hn => [w |] /=; last by discriminate.
      case => /(f_equal embed); by rewrite unembedP => ->.
Qed.

(* --- 2. S-m-n witness via EAS --------------------------------------- *)

Lemma γ_RaceGraph'_spec :
  exists γ : nat -> nat,
    forall c, enumerator (φ (γ c)) (RaceGraph' c).
Proof. exact (EAS RaceGraph' RaceGraph'_enumerable_uncurried). Qed.

(* γ is a Prop-existential witness, so it can't be a free-standing
   top-level Definition. Everything that needs it (η and every lemma
   below, down to eff_insep_A0_B1 itself) is Prop-sorted, so this is
   fine -- park γ as a Section variable with its spec as a hypothesis,
   build everything relative to it, then destruct γ_spec exactly once
   at the very end, outside the section, to discharge the hypothesis. *)

Section Race.

Variable γ : nat -> nat.
Hypothesis Hγ : forall c, enumerator (φ (γ c)) (RaceGraph' c).

Definition η (i j : nat) : nat := γ (embed (i, j)).

Lemma η_spec i j z : W (η i j) z <-> RaceGraph i j z.
Proof.
unfold η, W.
pose proof (Hγ (embed (i, j)) z) as Hspec.
unfold RaceGraph' in Hspec.
rewrite embedP in Hspec.
cbn in Hspec.
symmetry.
exact Hspec.
Qed.

(* --- 3. theta_ours agrees with raceVal at index η i j --------------- *)

Lemma raceVal_functional i j y v1 v2 :
  raceVal i j y =! v1 -> raceVal i j y =! v2 -> v1 = v2.
Proof. exact: hasvalue_det. Qed.

Lemma θ_ours_η i j y v : Θ_ours (η i j) y =! v <-> raceVal i j y =! v.
Proof.
unfold Θ_ours.
split.
- intros [n [Hmu Hbranch]] % bind_hasvalue.
  apply mu_hasvalue in Hmu as [Htrue _].
  simpl in Htrue, Hbranch.
  destruct (φ (η i j) n) as [z|] eqn:E.
  + apply ret_hasvalue_inv in Htrue.
    apply PeanoNat.Nat.eqb_eq in Htrue.
    apply ret_hasvalue_inv in Hbranch.
    assert (HW : W (η i j) z) by (exists n; exact E).
    apply η_spec in HW.
    unfold RaceGraph in HW.
    rewrite Htrue in HW.
    rewrite Hbranch in HW.
    exact HW.
  + apply ret_hasvalue_inv in Htrue.
    discriminate Htrue.
- intros Hrace.
  assert (HRG : RaceGraph i j (embed (y, v))).
  { unfold RaceGraph. rewrite embedP. simpl. exact Hrace. }
  destruct (proj2 (η_spec i j (embed (y, v))) HRG) as [n0 Hn0].
  assert (Hter : ter (mu (fun n => match φ (η i j) n with
                                    | Some z => ret (Nat.eqb (fst (unembed z)) y)
                                    | None => ret false
                                    end))).
  { apply mu_ter. exists n0. split.
    - simpl. rewrite Hn0. rewrite embedP. simpl.
      apply ret_hasvalue'. apply PeanoNat.Nat.eqb_refl.
    - intros x _. destruct (φ (η i j) x); eexists; apply ret_hasvalue.
  }
  destruct Hter as [n Hmu].
  apply bind_hasvalue.
  exists n. split; [exact Hmu |].
  simpl.
  apply mu_hasvalue in Hmu as [Htrue _].
  simpl in Htrue.
  destruct (φ (η i j) n) as [z|] eqn:E.
  + apply ret_hasvalue_inv in Htrue.
    apply PeanoNat.Nat.eqb_eq in Htrue.
    assert (HW : W (η i j) z) by (exists n; exact E).
    apply η_spec in HW.
    unfold RaceGraph in HW.
    rewrite Htrue in HW.
    assert (Hv : snd (unembed z) = v)
      by (apply (raceVal_functional i j y (snd (unembed z)) v HW Hrace)).
    rewrite Hv.
    apply ret_hasvalue.
  + apply ret_hasvalue_inv in Htrue.
    discriminate Htrue.
Qed.

(* --- 4. A0 / B1 membership at the diagonal point k = <η i j, η i j> - *)

Lemma A0_at_k i j : A0 (embed (η i j, η i j)) <-> raceVal i j (η i j) =! 1.
Proof. rewrite /A0 embedP /=. exact: θ_ours_η. Qed.

Lemma B1_at_k i j : B1 (embed (η i j, η i j)) <-> raceVal i j (η i j) =! 0.
Proof. rewrite /B1 embedP /=. exact: θ_ours_η. Qed.

(* --- 5. raceVal value unfolds directly via mu_hasvalue + semidec_of ---
   (raceAt/race are gone -- raceVal's `mu` argument already *is* the race,
   inlined, so there's nothing left to compose through; this restates
   mu_hasvalue/bind_hasvalue in terms of semidec_of directly instead.) --- *)

Lemma raceVal_iff_race i j y v :
  raceVal i j y =! v <->
    exists n,
      (semidec_of i (embed (y,y)) n = true \/ semidec_of j (embed (y,y)) n = true) /\
      (forall m, m < n -> semidec_of i (embed (y,y)) m = false
                        /\ semidec_of j (embed (y,y)) m = false) /\
      (if semidec_of i (embed (y,y)) n then v = 0 else v = 1).
Proof.
unfold raceVal.
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

(* --- 5b. race-resolution helpers: if one side answers and the other
   never does, raceVal settles on the winner's value --------------------- *)

Lemma raceVal_wins_left i j y :
  (exists n, semidec_of i (embed (y,y)) n = true) ->
  (forall n, semidec_of j (embed (y,y)) n = false) ->
  raceVal i j y =! 0.
Proof.
intros [n0 Hn0] Hjfalse.
destruct (mu_tot_ter Hn0) as [n Hn].
apply mu_tot_hasvalue in Hn as [Htrue Hmin].
apply raceVal_iff_race.
exists n. split; [left; exact Htrue |].
split.
- intros m Hlt. split; [apply Hmin; exact Hlt | apply Hjfalse].
- rewrite Htrue. reflexivity.
Qed.

Lemma raceVal_wins_right i j y :
  (exists n, semidec_of j (embed (y,y)) n = true) ->
  (forall n, semidec_of i (embed (y,y)) n = false) ->
  raceVal i j y =! 1.
Proof.
intros [n0 Hn0] Hifalse.
destruct (mu_tot_ter Hn0) as [n Hn].
apply mu_tot_hasvalue in Hn as [Htrue Hmin].
apply raceVal_iff_race.
exists n. split; [right; exact Htrue |].
split.
- intros m Hlt. split; [apply Hifalse | apply Hmin; exact Hlt].
- rewrite (Hifalse n). reflexivity.
Qed.

(* --- 5c. A0 / B1 enumerable, via seval on Θ_ours ----------------------- *)

Lemma A0_enumerable : enumerable A0.
Proof.
apply (proj2 (enum_iff A0)).
exists (fun z n =>
  match seval (Θ_ours (fst (unembed z)) (snd (unembed z))) n with
  | Some v => Nat.eqb v 1
  | None => false
  end).
intros z. unfold A0. split.
- intros [n Hn] % seval_hasvalue.
  exists n. rewrite Hn. apply PeanoNat.Nat.eqb_refl.
- intros [n Hn].
  destruct (seval (Θ_ours (fst (unembed z)) (snd (unembed z))) n) as [v0|] eqn:E;
    [| discriminate].
  apply PeanoNat.Nat.eqb_eq in Hn. subst v0.
  apply seval_hasvalue. exists n. exact E.
Qed.

Lemma B1_enumerable : enumerable B1.
Proof.
apply (proj2 (enum_iff B1)).
exists (fun z n =>
  match seval (Θ_ours (fst (unembed z)) (snd (unembed z))) n with
  | Some v => Nat.eqb v 0
  | None => false
  end).
intros z. unfold B1. split.
- intros [n Hn] % seval_hasvalue.
  exists n. rewrite Hn. apply PeanoNat.Nat.eqb_refl.
- intros [n Hn].
  destruct (seval (Θ_ours (fst (unembed z)) (snd (unembed z))) n) as [v0|] eqn:E;
    [| discriminate].
  apply PeanoNat.Nat.eqb_eq in Hn. subst v0.
  apply seval_hasvalue. exists n. exact E.
Qed.

(* --- 6. Main theorem, still inside Section Race --------------------- *)

Lemma eff_insep_A0_B1_rel : eff_insep A0 B1.
Proof.
split; [exact A0_enumerable |].
split; [exact B1_enumerable |].
split.
- intros z HA0 HB1.
  unfold A0 in HA0. unfold B1 in HB1.
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
    pose proof (raceVal_wins_left i j (η i j) Hiwin Hjlose) as Hrace0.
    pose proof (proj2 (B1_at_k i j) Hrace0) as HB1k.
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
  pose proof (raceVal_wins_right i j (η i j) Hjwin Hilose) as Hrace1.
  pose proof (proj2 (A0_at_k i j) Hrace1) as HA0k.
  apply Hnk. apply H1. exact HA0k.
Qed.

End Race.

(* --- Final assembly: discharge the γ hypothesis exactly once here --- *)

Lemma eff_insep_A0_B1 : eff_insep A0 B1.
Proof.
  destruct γ_RaceGraph'_spec as [γ Hγ].
  exact (eff_insep_A0_B1_rel γ Hγ).
Qed.

End Mη.