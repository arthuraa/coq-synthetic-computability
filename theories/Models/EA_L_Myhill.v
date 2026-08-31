(* Generic Myhill's-theorem-style machinery built on top of EA_L.v:
   given CT_L (to build EA_L at all) and MP (needed inside
   eff_insep_to_creative itself, to convert a `part`-valued/partial
   separating witness into a decidable total one -- a genuinely separate
   cost of the underlying Myhill's-theorem-style argument, not subsumed
   by CT_L, regardless of which numbering is used), turns
   eff_insep_shape W_L P B1_L into creative P / m-complete P for an
   arbitrary P. Zero content specific to any particular downstream
   project -- the only choice left to a caller is which set supplies
   the eff_insep_shape hypothesis.

   Named EA_L_Myhill.v (not Myhill.v) to avoid colliding with
   Basic/Myhill.v, which proves Myhill's *isomorphism* theorem -- a
   different classical result. *)

From Stdlib Require Import Unicode.Utf8.
Require Import ssreflect.
Require Import SyntheticComputability.Models.EA_L.

Require Import SyntheticComputability.Models.CT.
Require Import SyntheticComputability.Models.EffectiveInseparability_L.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparabilityGeneric.
Require Import SyntheticComputability.ReducibilityDegrees.EffectiveInseparability.
Require Import SyntheticComputability.ReducibilityDegrees.simple.
Require Import SyntheticComputability.Axioms.EA.
Require Import SyntheticComputability.CRM.principles.

(* --- eff_insep_shape is invariant under replacing W with a pointwise-
   equivalent numbering -- a generic, mechanical transport lemma. --- *)

Lemma eff_insep_shape_W_iff (W1 W2 : nat -> nat -> Prop) (A B : nat -> Prop) :
  (forall c x, W1 c x <-> W2 c x) -> eff_insep_shape W1 A B -> eff_insep_shape W2 A B.
Proof.
intros HW [HAenum [HBenum [Hdisj [f Hf]]]].
split; [exact HAenum |]. split; [exact HBenum |]. split; [exact Hdisj |].
exists f. intros i j Hi Hj Hij.
destruct (Hf i j) as [k [Hk [Hki Hkj]]].
- intros x Hx % Hi. apply HW. exact Hx.
- intros x Hx % Hj. apply HW. exact Hx.
- intros x Hx % HW. intros Hy % HW. exact (Hij x Hx Hy).
- exists k. split; [exact Hk |]. split.
  + intros Hk1 % HW. exact (Hki Hk1).
  + intros Hk2 % HW. exact (Hkj Hk2).
Qed.

(* `creative` is stated relative to an ambient EA instance's own
   canonical numbering (simple.v's productive/creative are defined via
   `W`, which is itself EA-instance-relative, resolved through EA's
   `Existing Class` declaration) -- so the instance has to be in scope
   before the THEOREM STATEMENT elaborates, not just inside the proof.
   `ct : CT_L` is what supplies it (via EA_L), so it has to become a
   section Variable here rather than an intro'd hypothesis; this is the
   same shape EA_L.v itself already uses (Section BuildEA_L, Hypothesis
   ct : CT_L). EA_inst itself needs `Local Instance`, not `Let` --
   typeclass resolution auto-registers Variable/Context section
   hypotheses of a Class type, but not plain Let-bound local
   definitions, and a Let here left `creative`'s implicit EA_inst
   argument unresolved even with EA_L ct sitting right there in scope.
   Local Instance forces the registration explicitly; it gets
   substituted away (not re-generalized) when the section closes,
   giving exactly `forall ct : CT_L, forall P, MP -> ... -> creative P`,
   with the EA instance silently EA_L ct throughout. *)

Section GenericCreative.

Variable ct : CT_L.
Local Instance EA_inst : EA := EA_L ct.

Theorem creative_of_eff_insep_shape (P : nat -> Prop) (MP_assm : MP) :
  eff_insep_shape W_L P B1_L -> creative P.
Proof.
intros Hshape.
eapply (eff_insep_to_creative MP_assm).
eapply eff_insep_shape_W_iff; [| exact Hshape].
intros i x. symmetry. exact (W_psi_L_iff i x).
Qed.

End GenericCreative.

Theorem m_complete_of_eff_insep_shape (P : nat -> Prop) :
  CT_L -> MP -> eff_insep_shape W_L P B1_L -> m-complete P.
Proof.
intros ct MP_assm Hshape.
exact (creative_to_m_complete MP_assm _ (creative_of_eff_insep_shape ct MP_assm Hshape)).
Qed.
