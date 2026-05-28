From SyntheticComputability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts.
Require Import SyntheticComputability.Axioms.EA.
From SyntheticComputability.ReducibilityDegrees Require Import simple.
From SyntheticComputability.CRM Require Import principles.

Section EffectiveInseparability.

Context {EA_inst : EA}.
Context {Part : partiality}.

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
  destruct side as [|];
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