(* Generic Myhill's-theorem-style machinery built on top of EA_L.v:
   given CT_L (to build EA_L at all), turns effective inseparability
   eff_insep_with out W_L P B1_L into creative P / m-complete P for an
   arbitrary P. creative_of_eff_insep_with is stated once, for any
   witness representation out, given a way Htot to totalize
   productive_with out; its two instances differ only in Htot:

     creative_of_eff_insep_shape_tot  (total witness)    no MP
     creative_of_eff_insep_shape      (partial witness)  MP, via
                                      partial_productive_iff_productive

   m-completeness adds MP once more, through creative_to_m_complete.
   Zero content specific to any particular downstream project -- the
   only choice left to a caller is which set supplies the effective
   inseparability hypothesis.

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
   giving exactly `forall ct : CT_L, forall P, ... -> creative P`,
   with the EA instance silently EA_L ct throughout. *)

Section GenericCreative.

Variable ct : CT_L.
Local Instance EA_inst : EA := EA_L ct.

Theorem creative_of_eff_insep_with {F : Type} (out : F -> nat -> Prop)
    (Htot : forall p, productive_with out p -> productive p) (P : nat -> Prop) :
  eff_insep_with out W_L P B1_L -> creative P.
Proof.
intros Hshape.
eapply (eff_insep_with_to_creative out Htot).
eapply eff_insep_with_W_iff; [| exact Hshape].
intros i x. symmetry. exact (W_psi_L_iff i x).
Qed.

Theorem creative_of_eff_insep_shape_tot (P : nat -> Prop) :
  eff_insep_shape_tot W_L P B1_L -> creative P.
Proof.
apply creative_of_eff_insep_with. intros p. apply productive_with_eq.
Qed.

Theorem creative_of_eff_insep_shape (P : nat -> Prop) (MP_assm : MP) :
  eff_insep_shape W_L P B1_L -> creative P.
Proof.
apply creative_of_eff_insep_with.
intros p. apply (partial_productive_iff_productive p MP_assm).
Qed.

End GenericCreative.

Theorem m_complete_of_eff_insep_shape_tot (P : nat -> Prop) :
  CT_L -> MP -> eff_insep_shape_tot W_L P B1_L -> m-complete P.
Proof.
intros ct MP_assm Hshape.
exact (creative_to_m_complete MP_assm _
         (creative_of_eff_insep_shape_tot ct Hshape)).
Qed.

Theorem m_complete_of_eff_insep_shape (P : nat -> Prop) :
  CT_L -> MP -> eff_insep_shape W_L P B1_L -> m-complete P.
Proof.
intros ct MP_assm Hshape.
exact (creative_to_m_complete MP_assm _
         (creative_of_eff_insep_shape ct MP_assm Hshape)).
Qed.
