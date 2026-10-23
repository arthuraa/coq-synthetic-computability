(* Superset transport (Kuznetsov's Proposition 9) for the bundled
   notions now lives in EffectiveInseparabilityCore.v as
   eff_insep_with_superset, proved once for the partial and the total
   witness. These are the older names, kept so downstream code compiles
   unchanged; new code should use eff_insep_with_superset directly. *)

From SyntheticComputability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts Definitions.
Require Import SyntheticComputability.Shared.partial.
Require Export SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityCore.

Notation eff_insep_shape_superset := (eff_insep_with_superset (@hasvalue _ nat))
  (only parsing).
Notation eff_insep_shape_tot_superset := (eff_insep_with_superset (@eq nat))
  (only parsing).
