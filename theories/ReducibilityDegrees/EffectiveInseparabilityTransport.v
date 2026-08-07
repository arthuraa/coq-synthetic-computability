(* The "folklore" transport lemma behind Azevedo de Amorim, Zhang &
   Gaboardi's Theorem 19 (and, per their own citation, Kuznetsov's
   Proposition 9): effective inseparability of (A,B) transfers to any
   *superset* A' of A that stays disjoint from B, over the SAME numbering
   W and the SAME underlying domain -- no new race/diagonal construction
   needed, just monotonicity of the witness hypotheses.

   This is the piece that lets an effective-inseparability result be
   transported from one numbering (e.g. T_L, where it's cheap to prove)
   to a *different*, harder-to-work-with set A' (e.g. one phrased via a
   separate machine model's own semantics) via a PLAIN reduction, without
   ever needing to re-run the race construction natively in the second
   model. See project memory (2026-08-07) for how this is meant to be
   used against Undecidability/mm.v's R_target. *)

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
