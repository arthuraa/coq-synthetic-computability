From SyntheticComputability.Basic Require Import Recursion.
From SyntheticComputability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts.
Require Import SyntheticComputability.Axioms.EA.
From SyntheticComputability.ReducibilityDegrees Require Import simple.
From SyntheticComputability.CRM Require Import principles.

Section EffectiveInseparability.

Context {EA_inst : EA}.
Context {Part : partiality}.

Hypothesis MP_assm : MP.

Notation φ := (proj1_sig EA).
Notation EAP := (proj2_sig EA).

Definition eff_insep (A B : nat -> Prop) : Prop :=
  enumerable A /\ enumerable B /\
  (forall x, A x -> ~ B x) /\
  exists f : nat -> nat -> part nat,
    forall i j,
    (forall x, A x -> W i x) ->
    (forall x, B x -> W j x) ->
    (forall x, W i x -> ~ W j x) ->
    exists k, hasvalue (f i j) k /\ ~ W i k /\ ~ W j k.

Lemma W_union :
  forall j, exists u, forall c x, W (u c) x <-> W j x \/ W c x.
Proof.
intros j.
destruct W_via_Θ as [β Hβ].
set (Θ := proj1_sig Recursion.recursion_EPF).
pose proof (proj2_sig Recursion.recursion_EPF) as HΘ.
pose (h' := fun e x fuel =>
  match seval (Θ (β j) x) fuel, seval (Θ (β e) x) fuel with
  | Some _, _ => ret true
  | _, Some _ => ret true
  | _, _ => ret false
  end).
pose (h := fun e x => mu (h' e x)).
destruct (HΘ h) as [γ Hγ].
destruct Θ_via_W as [α Hα].
exists (fun c => α (γ c)).
intros c x.
rewrite (Hα (γ c) x).
split.
- intros [v Hv].
  apply (proj1 (Hγ c x v)) in Hv.
  unfold h in Hv.
  apply mu_hasvalue in Hv as [Hh' _].
  apply seval_hasvalue in Hh' as [n Hn].
  unfold h' in Hn.
  destruct (seval (Θ (β j) x) v) as [y|] eqn:E1.
  + left. apply Hβ. exists y. apply seval_hasvalue. exists v. exact E1.
  + destruct (seval (Θ (β c) x) v) as [y|] eqn:E2.
    * right. apply Hβ. exists y. apply seval_hasvalue. exists v. exact E2.
    * assert (Hcon : ret false =! true) by ( apply seval_hasvalue; exists n; exact Hn ).
      pose proof (ret_hasvalue (A:=bool) false) as Hret.
      pose proof (hasvalue_det (A:=bool) Hcon Hret) as Heq.
      discriminate Heq.
- set (P := fun n : nat =>
    (exists y, seval (Θ (β j) x) n = Some y) \/
    (exists y, seval (Θ (β c) x) n = Some y)).
  assert (Hd : forall n, {P n} + {~ P n}).
  { intros n.
    destruct (seval (Θ (β j) x) n) as [y'|] eqn:E1.
    - left; now left; exists y'.
    - destruct (seval (Θ (β c) x) n) as [y'|] eqn:E2.
      + left; right; exists y'; apply E2.
      + right. intros [[y' H]|[y' H]]; [congruence|congruence].
  }
assert (Hstep : (W j x \/ W c x) -> exists v, Θ (γ c) x =! v).
{ intros Hor.
  assert (Hex : exists n, P n).
  { destruct Hor as [Hj | Hc].
    - apply Hβ in Hj as [y Hy].
      apply seval_hasvalue in Hy as [n0 Hn0].
      exists n0. left. exists y. exact Hn0.
    - apply Hβ in Hc as [v Hv].
      apply seval_hasvalue in Hv as [n0 Hn0].
      exists n0. right. exists v. exact Hn0. }
  set (sig := mu_nat_dep P Hd Hex).
  set (n := proj1_sig sig).
  exists n.
  apply (proj2 (Hγ c x n)).
  unfold h. rewrite mu_hasvalue.
  split.
  - destruct (proj2_sig sig) as [[y' Hy'] | [y' Hy']];
    unfold h'; fold n in Hy'; rewrite Hy';
    [ | destruct (seval (A:=nat) (Θ (β j) x) n)];
    apply ret_hasvalue.
  - intros m Hm.
    assert (HP : ~ P m) by (eapply mu_nat_dep_min; exact Hm).
    unfold P in HP.
    destruct (seval (Θ (β j) x) m) as [y'|] eqn:E1.
    + exfalso. apply HP. left. exists y'. reflexivity.
    + destruct (seval (Θ (β c) x) m) as [y'|] eqn:E2.
      * exfalso. apply HP. right. exists y'. reflexivity.
      * unfold h'. rewrite E1, E2. apply ret_hasvalue. }
intros [Hj | Hc].
+ exact (Hstep (or_introl Hj)).
+ exact (Hstep (or_intror Hc)).
Qed.

Theorem eff_insep_to_creative (A B : nat -> Prop) :
  eff_insep A B -> creative A.
Proof.
intros (Ha & Hb & Hdisj & f & Hf).
split; [apply Ha |].
apply partial_productive_iff_productive; auto.
rewrite W_spec in Ha; destruct Ha as [i Ha].
rewrite W_spec in Hb; destruct Hb as [j Hb].
destruct (W_union j) as [u Hu].
exists (fun c => f i (u c)).
intros c Hx.
pose proof (Hf i (u c)) as Hf'.
set (HsupA := (fun x HAx => (proj1 (Ha x) HAx))).
assert (HsupB : forall x, B x -> W (u c) x).
{ intros x HB % Hb. rewrite Hu. left. exact HB. }
assert (HWdisj : forall x, W i x -> ~ W (u c) x).
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
  apply (Hu c k).
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