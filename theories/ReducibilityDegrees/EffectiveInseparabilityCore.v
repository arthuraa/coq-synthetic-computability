(* Effective inseparability, stated once over an arbitrary "output"
   relation out : F -> nat -> Prop saying which separating number a
   witness value denotes. The two instances are

     partial: F := part nat, out := hasvalue   (Kuznetsov's Definition 5)
     total:   F := nat,      out := eq         (Rogers/Soare)

   and every structural lemma below is proved once for both.

   eff_insep_core_with is the unbundled notion (disjointness plus a
   witness function, no enumerability requirement, as both source
   papers state Theorem 17); eff_insep_with bundles enumerability of
   both sets on top (as Kuznetsov's Proposition 7 / Myhill's theorem
   need). The bundled notion is literally `enumerable A /\ enumerable B
   /\ core`, so existing `[HA [HB [Hdisj [f Hf]]]]` patterns still apply.

   The total notion implies the partial one (eff_insep_with_map with
   g := ret). The converse costs MP, through simple.v's
   partial_productive_iff_productive; that is the only reason to keep
   both. Parametrized over an arbitrary numbering W -- not tied to any
   specific model or project. *)

From SyntheticComputability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts Definitions.
Require Import SyntheticComputability.Shared.partial.

Definition eff_insep_core_with {F : Type} (out : F -> nat -> Prop)
    (W : nat -> nat -> Prop) (A B : nat -> Prop) : Prop :=
  (forall x, A x -> ~ B x) /\
  exists f : nat -> nat -> F,
    forall i j,
    (forall x, A x -> W i x) ->
    (forall x, B x -> W j x) ->
    (forall x, W i x -> ~ W j x) ->
    exists k, out (f i j) k /\ ~ W i k /\ ~ W j k.

Definition eff_insep_with {F : Type} (out : F -> nat -> Prop)
    (W : nat -> nat -> Prop) (A B : nat -> Prop) : Prop :=
  enumerable A /\ enumerable B /\ eff_insep_core_with out W A B.

Notation eff_insep_core := (eff_insep_core_with (@hasvalue _ nat)).
Notation eff_insep_shape := (eff_insep_with (@hasvalue _ nat)).
Notation eff_insep_core_tot := (eff_insep_core_with (@eq nat)).
Notation eff_insep_shape_tot := (eff_insep_with (@eq nat)).

Section Structural.

Context {F : Type}.
Variable out : F -> nat -> Prop.

Lemma eff_insep_with_to_core {W A B} :
  eff_insep_with out W A B -> eff_insep_core_with out W A B.
Proof. intros (_ & _ & H). exact H. Qed.

(* Proposition 9: effective inseparability transfers to any superset A'
   of A that stays disjoint from B, over the same numbering W. *)
Lemma eff_insep_core_with_superset {W A B A'} :
  eff_insep_core_with out W A B ->
  (forall x, A x -> A' x) ->
  (forall x, A' x -> ~ B x) ->
  eff_insep_core_with out W A' B.
Proof.
intros [_ [f Hf]] Hsub Hdisj'.
split; [exact Hdisj' |].
exists f. intros i j Hi Hj Hij.
apply Hf; [| exact Hj | exact Hij].
intros x Hx. apply Hi, Hsub, Hx.
Qed.

Lemma eff_insep_with_superset {W A B A'} :
  eff_insep_with out W A B ->
  enumerable A' ->
  (forall x, A x -> A' x) ->
  (forall x, A' x -> ~ B x) ->
  eff_insep_with out W A' B.
Proof.
intros (_ & HB & H) HA' Hsub Hdisj'.
split; [exact HA' |]. split; [exact HB |].
exact (eff_insep_core_with_superset H Hsub Hdisj').
Qed.

(* Invariance under a pointwise-equivalent numbering. *)
Lemma eff_insep_core_with_W_iff {W1 W2 A B} :
  (forall c x, W1 c x <-> W2 c x) ->
  eff_insep_core_with out W1 A B -> eff_insep_core_with out W2 A B.
Proof.
intros HW [Hdisj [f Hf]].
split; [exact Hdisj |].
exists f. intros i j Hi Hj Hij.
destruct (Hf i j) as [k [Hk [Hki Hkj]]].
- intros x Hx. apply HW, Hi, Hx.
- intros x Hx. apply HW, Hj, Hx.
- intros x Hx Hy. apply HW in Hx. apply HW in Hy. exact (Hij x Hx Hy).
- exists k. split; [exact Hk |]. split.
  + intros Hw. apply Hki, HW, Hw.
  + intros Hw. apply Hkj, HW, Hw.
Qed.

Lemma eff_insep_with_W_iff {W1 W2 A B} :
  (forall c x, W1 c x <-> W2 c x) ->
  eff_insep_with out W1 A B -> eff_insep_with out W2 A B.
Proof.
intros HW (HA & HB & H).
split; [exact HA |]. split; [exact HB |].
exact (eff_insep_core_with_W_iff HW H).
Qed.

Lemma eff_insep_core_with_symmetric {W A B} :
  eff_insep_core_with out W A B -> eff_insep_core_with out W B A.
Proof.
intros [Hdisj [f Hf]].
split; [intros x HB HA; exact (Hdisj x HA HB) |].
exists (fun i j => f j i). intros i j HBw HAw Hij.
destruct (Hf j i HAw HBw) as [k [Hk [Hkj Hki]]].
- intros x Hx Hy. exact (Hij x Hy Hx).
- exists k. repeat split; assumption.
Qed.

Lemma eff_insep_with_symmetric {W A B} :
  eff_insep_with out W A B <-> eff_insep_with out W B A.
Proof.
split; intros (HA & HB & H);
  (split; [assumption |]); (split; [assumption |]);
  exact (eff_insep_core_with_symmetric H).
Qed.

End Structural.

(* Changing the witness representation along a map g that preserves
   the denoted separating number. *)
Lemma eff_insep_core_with_map {F1 F2 : Type}
    (out1 : F1 -> nat -> Prop) (out2 : F2 -> nat -> Prop) (g : F1 -> F2)
    {W A B} :
  (forall x k, out1 x k -> out2 (g x) k) ->
  eff_insep_core_with out1 W A B -> eff_insep_core_with out2 W A B.
Proof.
intros Hg [Hdisj [f Hf]].
split; [exact Hdisj |].
exists (fun i j => g (f i j)). intros i j Hi Hj Hij.
destruct (Hf i j Hi Hj Hij) as [k [Hk Hout]].
exists k. split; [apply Hg, Hk | exact Hout].
Qed.

Lemma eff_insep_with_map {F1 F2 : Type}
    (out1 : F1 -> nat -> Prop) (out2 : F2 -> nat -> Prop) (g : F1 -> F2)
    {W A B} :
  (forall x k, out1 x k -> out2 (g x) k) ->
  eff_insep_with out1 W A B -> eff_insep_with out2 W A B.
Proof.
intros Hg (HA & HB & H).
split; [exact HA |]. split; [exact HB |].
exact (eff_insep_core_with_map out1 out2 g Hg H).
Qed.

Section Partial.

Context {Part : partiality}.

Lemma eff_insep_shape_tot_to_shape {W A B} :
  eff_insep_shape_tot W A B -> eff_insep_shape W A B.
Proof.
apply (eff_insep_with_map _ _ (@ret _ nat)).
intros x k <-. apply ret_hasvalue.
Qed.

End Partial.
