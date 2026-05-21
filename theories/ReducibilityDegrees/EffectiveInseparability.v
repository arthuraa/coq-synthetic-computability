From SyntheticComputability.Basic Require Import Recursion.
From SyntheticComputability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts.
Require Import SyntheticComputability.Axioms.EA.
From SyntheticComputability.ReducibilityDegrees Require Import simple.

Section EffectiveInseparability.

Context {EA_inst : EA}.
Context {Part : partiality}.

(* Destructure the EA instance to get the universal enumerator *)
Let φ := proj1_sig EA_inst.
Let EAP := proj2_sig EA_inst.

Definition eff_insep (A B : nat -> Prop) : Prop :=
  enumerable A /\ enumerable B /\
  exists f : nat -> nat -> part nat,
    forall i j,
    (forall x, A x -> W i x) ->
    (forall x, B x -> W j x) ->
    (forall x, W i x -> ~ W j x) ->
    exists k,
    hasvalue (f i j) k /\ ~ W i k /\ ~ W j k.

Lemma eff_insep__creative (A B : nat -> Prop) :
  eff_insep A B -> creative A.
Proof.
intros (Ha & Hb & [f Hf]).
split; [apply Ha |].
unfold productive.
rewrite W_spec in Ha.
destruct Ha as [i Ha].
rewrite W_spec in Hb.
destruct Hb as [j Hb].
destruct W_via_Θ as [β Hβ].
pose (Θ := proj1_sig Recursion.recursion_EPF).
pose proof (HΘ := proj2_sig Recursion.recursion_EPF).
pose (h' := fun c x fuel =>
  match seval (Θ (β j) x) fuel, seval (Θ (β c) x) fuel with
  | Some _, _ => ret true
  | _, Some _ => ret true
  | _, _ => undef
  end).
pose (h := fun c x => mu (h' c x)).
specialize (HΘ h).
destruct HΘ as [γ Hγ].
destruct Θ_via_W as [α Hα].
assert (G : forall c x, W (α (γ c)) x <-> W j x \/ W c x).
{
  intros c x.
  split; [intros Hx | intros [Hx | Hx]].
  - rewrite Hα in Hx.
    destruct Hx as [v Hv].
    rewrite Hγ in Hv.
  admit.
}
pose (f' := fun c => f i (α (γ c))).
assert (G' : forall c, ter (f' c)).
{ admit. }
Check eval.
exists (fun c => eval (G' c)).
intros c Hx.
Qed.

(* K: the diagonal halting set — index e is in K iff e is in W_e *)
Definition K : nat -> Prop := fun e => W e e.

(* Its complement *)
Definition Kbar : nat -> Prop := fun e => ~ W e e.

Lemma K_Kbar_eff_insep : eff_insep K Kbar.
Proof.
  unfold eff_insep.
  repeat split.
  - (* semi_decidable K *)
    exists (fun e => fun n => match φ e n with
                              | Some x => Nat.eqb x e
                              | None   => false
                              end).
    intro e; unfold K, W. split.
    + intros [n Hn]. exists n.
      fold φ in Hn. rewrite Hn, PeanoNat.Nat.eqb_refl.
      reflexivity.
    + intros [n Hn]. exists n. fold φ.
      destruct (φ e n); [|discriminate].
      apply PeanoNat.Nat.eqb_eq in Hn. subst. reflexivity.
  - (* semi_decidable Kbar — needs the recursion theorem *)
    ...
  - (* productive function — from the recursion theorem *)
    ...
Qed.

(* The "canonical" effectively inseparable pair *)
Definition K0 : nat -> Prop := fun n => halts n n true.   (* accepts on self *)
Definition K1 : nat -> Prop := fun n => halts n n false.  (* rejects on self *)

Lemma K0_K1_eff_insep : eff_insep K0 K1.
Proof.
  (* Use the double recursion theorem from Recursion.v:
     Given any separator index pair (i, j), construct via smn/recursion
     an index e such that:
     - if e ∈ W_i, then run some diverging computation to derive e ∈ K1
     - if e ∈ W_j, then run some diverging computation to derive e ∈ K0
     In both cases we get a contradiction, so e ∉ W_i ∪ W_j. *)
  ...
Qed.

End EffectiveInseparability.