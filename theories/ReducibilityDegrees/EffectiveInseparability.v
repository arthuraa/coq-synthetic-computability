From SyntheticComputability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts reductions.
Require Import SyntheticComputability.Axioms.EA.
From SyntheticComputability.ReducibilityDegrees Require Import simple EffectiveInseparabilityGeneric.
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

(* The one construction: from a separating witness f, the productive
   function for compl A is c |-> f i (u j c), where W i = A, W j = B and
   W (u j c) = W j ∪ W c. Generic in how a witness value denotes its
   separating number, so it serves the partial and total notions alike. *)
Theorem eff_insep_with_to_productive_with {F : Type}
    (out : F -> nat -> Prop) (A B : nat -> Prop) :
  eff_insep_with out W A B -> productive_with out (compl A).
Proof.
intros (Ha & Hb & Hdisj & f & Hf).
rewrite W_spec in Ha; destruct Ha as [i Ha].
rewrite W_spec in Hb; destruct Hb as [j Hb].
destruct W_union as [u Hu].
exists (fun c => f i (u j c)).
intros c Hx.
set (HsupA := (fun x HAx => (proj1 (Ha x) HAx))).
assert (HsupB : forall x, B x -> W (u j c) x).
{ intros x HB % Hb. rewrite Hu. left. exact HB. }
assert (HWdisj : forall x, W i x -> ~ W (u j c) x).
{ intros x HA % Ha Huc % Hu.
  destruct Huc as [Hj | Hc].
  - apply Hb in Hj. eapply Hdisj; eauto.
  - apply Hx in Hc. exact (Hc HA).
}
destruct (Hf i (u j c) HsupA HsupB HWdisj) as [k [Hk [Hki Hkj]]].
exists k.
repeat split; [exact Hk | |].
- intro HAk. apply Hki. apply Ha. exact HAk.
- intro Hwck. apply Hkj. apply Hu. right. exact Hwck.
Qed.

(* Creativity, given a way to totalize productive_with out. The two
   instances below are the only difference between the partial and
   total notions. *)
Theorem eff_insep_with_to_creative {F : Type} (out : F -> nat -> Prop)
    (Htot : forall p, productive_with out p -> productive p)
    (A B : nat -> Prop) :
  eff_insep_with out W A B -> creative A.
Proof.
intros H. split; [exact (proj1 H) |].
apply Htot. exact (eff_insep_with_to_productive_with out A B H).
Qed.

(* Total witness: no MP. *)
Theorem eff_insep_tot_to_creative (A B : nat -> Prop) :
  eff_insep_shape_tot W A B -> creative A.
Proof. apply eff_insep_with_to_creative. intros p. apply productive_with_eq. Qed.

(* Partial witness: totalizing costs MP. *)
Theorem eff_insep_to_creative (A B : nat -> Prop) :
  eff_insep_shape W A B -> creative A.
Proof.
apply eff_insep_with_to_creative.
intros p. apply (partial_productive_iff_productive p MP_assm).
Qed.

(* MP enters only through Myhill's theorem here. *)
Theorem eff_insep_tot_to_m_complete (A B : nat -> Prop) :
  eff_insep_shape_tot W A B -> m-complete A.
Proof.
intros H. exact (creative_to_m_complete MP_assm _ (eff_insep_tot_to_creative _ _ H)).
Qed.

Theorem eff_insep_to_m_complete (A B : nat -> Prop) :
  eff_insep_shape W A B -> m-complete A.
Proof.
intros H. exact (creative_to_m_complete MP_assm _ (eff_insep_to_creative _ _ H)).
Qed.

End EffectiveInseparability.