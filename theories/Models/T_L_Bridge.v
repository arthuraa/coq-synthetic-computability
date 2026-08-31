(* Bridges T_L (the step-indexed L-interpreter) to T_L_Uniform.R_TL, the
   mu-search-shaped uniform relation. Also z_vec/GenericK: a generic
   "T_L_Uniform.R_TL connection -> eff_insep_core" argument, parametrized
   over an arbitrary Pred : nat -> Prop characterized by an R_TL/mu <= 1
   connection -- not tied to any specific downstream project's own
   target set.

   theta_L_iff used to be stated over a trivial Theta_ours_L alias for
   theta_L (Theta_ours_L c y := theta_L c y); eliminated 2026-08-31 along
   with that alias itself (see Models/EffectiveInseparability_L.v),
   since it added a name without adding meaning. *)

From Stdlib Require Import Unicode.Utf8 Arith Lia.
From Undecidability Require Import FRACTRAN.
From Undecidability.FRACTRAN Require Import prime_seq.
From Undecidability.Shared.Libs.DLW Require Import vec.
Import vec_notations.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityCore.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.T_L_Extract.
Require Import SyntheticComputability.Models.T_L_Uniform.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityGeneric.
Require Import SyntheticComputability.Shared.partial.
Require Import SyntheticComputability.Shared.embed_nat.

(* T_L/theta_L (theta_L's own plain hasvalue) vs R_TL (T_L_Uniform's
   mu-search over TL_bit) are ultimately just "T_L i j eventually outputs m,"
   phrased through different scaffolding -- this bridges the two, including
   finding a LEAST witness n for the mu-search side (T_L is monotonic, so
   once it outputs Some m at any n it does so at all larger n too, but the
   search specifically wants the first such n). *)

Lemma theta_L_iff (c y v : nat) : θ_L c y =! v <-> exists n, T_L c y n = Some v.
Proof. unfold θ_L, hasvalue. reflexivity. Qed.

Lemma T_L_first_or_none (c y n : nat) :
  (forall k, k <= n -> T_L c y k = None) \/
  (exists n0 v0, n0 <= n /\ T_L c y n0 = Some v0 /\ forall k, k < n0 -> T_L c y k = None).
Proof.
induction n as [| n' [IHnone | [n0 [v0 [Hn0 [Hval Hmin]]]]]].
- destruct (T_L c y 0) as [v0|] eqn:E0.
  + right. exists 0, v0. repeat split; auto; intros k Hk; lia.
  + left. intros k Hk. assert (k = 0) by lia. congruence.
- destruct (T_L c y (S n')) as [v0|] eqn:ES.
  + right. exists (S n'), v0. repeat split; auto.
    intros k Hk. apply IHnone. lia.
  + left. intros k Hk. destruct (Nat.eq_dec k (S n')) as [-> | Hne]; [exact ES |].
    apply IHnone. lia.
- right. exists n0, v0. repeat split; auto; lia.
Qed.

Lemma T_L_least_witness (c y v : nat) :
  (exists n, T_L c y n = Some v) ->
  exists n, T_L c y n = Some v /\ forall k, k < n -> T_L c y k = None.
Proof.
intros [n Hn].
destruct (T_L_first_or_none c y n) as [Hnone | [n0 [v0 [Hn0 [Hval Hmin]]]]].
- exfalso. specialize (Hnone n (le_n n)). congruence.
- exists n0. split; [| exact Hmin].
  pose proof (@monotonic_T_L c y) as Hmono.
  specialize (@Hmono n0 v0 Hval n Hn0).
  congruence.
Qed.

Lemma R_TL_iff (v : Vector.t nat 2) (m : nat) :
  T_L_Uniform.R_TL v m <->
  exists n, T_L (Vector.hd v) (Vector.hd (Vector.tl v)) n = Some m.
Proof.
unfold T_L_Uniform.R_TL.
set (i := Vector.hd v). set (j := Vector.hd (Vector.tl v)).
rewrite TL_val_iff.
split.
- intros [n [_ [_ Hn]]]. exists n. rewrite <- (@T_L'_eq i j n). exact Hn.
- intros Hex.
  destruct (@T_L_least_witness i j m Hex) as [n [Hn Hmin]].
  exists n. repeat split.
  + unfold TL_bit. rewrite (@T_L'_eq i j n), Hn. reflexivity.
  + intros k Hk. unfold TL_bit. rewrite (@T_L'_eq i j k), (Hmin k Hk). reflexivity.
  + rewrite (@T_L'_eq i j n). exact Hn.
Qed.

(* Gödel-pairing packing of a single nat into a 2-vector, used to index
   z_vec-shaped pairs uniformly by every K/K_bin-style instantiation. *)
Definition z_vec (z : nat) : Vector.t nat 2 :=
  fst (unembed z) ## snd (unembed z) ## vec_nil.

Section GenericK.

Variable (Pred : nat -> Prop).
Hypothesis Hc : forall (v : Vector.t nat 2) (m : nat),
  (m <= 1)%nat -> T_L_Uniform.R_TL v m -> (m = 1 <-> Pred (ps 1 * enc 2 v)).

Definition K_of (z : nat) : Prop :=
  Pred (ps 1 * enc 2 (z_vec z)).

Lemma A0_L_subset_K_of (z : nat) : A0_L z -> K_of z.
Proof.
intros HA. apply theta_L_iff in HA.
assert (HR1 : T_L_Uniform.R_TL (z_vec z) 1)
  by (apply R_TL_iff; exact HA).
exact (proj1 (@Hc (z_vec z) 1 (Nat.le_refl 1) HR1) eq_refl).
Qed.

Lemma K_of_B1_L_disjoint (z : nat) : K_of z -> ~ B1_L z.
Proof.
intros HK HB. apply theta_L_iff in HB.
assert (HR0 : T_L_Uniform.R_TL (z_vec z) 0)
  by (apply R_TL_iff; exact HB).
assert (Heq : 0 = 1)
  by (apply (@Hc (z_vec z) 0 (Nat.le_0_l 1) HR0); exact HK).
discriminate Heq.
Qed.

Theorem eff_insep_K_of_B1_L : eff_insep_core W_L K_of B1_L.
Proof.
apply (eff_insep_core_superset (A := A0_L)).
- exact (eff_insep_shape_to_core eff_insep_A0_B1_L_via_generic).
- exact A0_L_subset_K_of.
- exact K_of_B1_L_disjoint.
Qed.

End GenericK.
