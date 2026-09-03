(* A monotonicity/transport lemma for the bundled effective-inseparability
   notion eff_insep_shape (EffectiveInseparabilityGeneric.v): effective
   inseparability of (A,B) transfers to any *superset* A' of A that stays
   disjoint from B, over the SAME numbering W and the SAME underlying
   domain -- no new race/diagonal construction needed, just monotonicity
   of the witness hypotheses.

   This is the piece that lets an effective-inseparability result proved
   for one set A be transported, via a plain inclusion A ⊆ A', to a
   different, harder-to-construct-directly set A', without re-running the
   race construction against A' itself. *)

From SyntheticComputability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts Definitions.
Require Import SyntheticComputability.Shared.partial.
From SyntheticComputability.ReducibilityDegrees Require Import EffectiveInseparabilityGeneric.

Require Import ssreflect.

Section Transport.

Context {Part : partiality}.

Lemma eff_insep_shape_superset (W : nat -> nat -> Prop) (A B A' : nat -> Prop) :
  eff_insep_shape W A B ->
  enumerable A' ->
  (forall x, A x -> A' x) ->
  (forall x, A' x -> ~ B x) ->
  eff_insep_shape W A' B.
Proof.
intros [HAenum [HBenum [Hdisj [f Hf]]]] HA'enum Hsub Hdisj'.
split; [exact HA'enum |].
split; [exact HBenum |].
split; [exact Hdisj' |].
exists f.
intros i j Hi Hj Hij.
apply (Hf i j).
- intros x Hx. apply Hi, Hsub, Hx.
- exact Hj.
- exact Hij.
Qed.

End Transport.
