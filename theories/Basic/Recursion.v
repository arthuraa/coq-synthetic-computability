(** * Kleene's Uniform Recursion Theorem

    Parametric (uniform-in-[y]) generalisation of the fixed-point
    theorem [Basic/Rice.v:FP], plus a translation from partial-function
    indices ([Θ], from [EPF]) to c.e.-set indices ([W], from [EA]).

    All results are stated under
      - [Context {EA_inst : EA}]: the enumeration axiom for c.e. sets,
      - [Context {Part : partiality}]: a partiality monad,
      - [Variable Θ : nat -> nat ↛ nat] together with [Hypothesis EPFP]
        asserting that every parametric family of partial functions
        is enumerated by [Θ].

    The corollary [URec_W] gives a uniform fixed point at the W level
    and is the workhorse used by Myhill's theorem
    ([ReducibilityDegrees/simple.v]). *)

Require Import SyntheticComputability.Axioms.EA.
Require Import SyntheticComputability.Synthetic.Definitions.
Require Import SyntheticComputability.Synthetic.EnumerabilityFacts.
From SyntheticComputability.Shared Require Import partial equiv_on embed_nat.
From SyntheticComputability.Axioms Require Import EPF.
Require Import Arith.

Section Recursion.

Context {EA_inst : EA}.
Context {Part : partiality}.

Notation φ := (proj1_sig EA_inst).
Notation EAP := (proj2_sig EA_inst).

Variable Θ : nat -> (nat ↛ nat).
Hypothesis EPFP :
  forall f : nat -> nat ↛ nat,
    exists γ, forall x, Θ (γ x) ≡{nat ↛ nat} f x.

(** ** Kleene's Uniform Recursion Theorem for [Θ]

    For every two-argument index function [f], there is a total
    function [h : nat -> nat] such that [Θ (h y)] and [Θ (f (h y) y)]
    agree as partial functions, uniformly in [y]. *)
Lemma URec_Θ :
  forall f : nat -> nat -> nat,
    exists h : nat -> nat, forall y, Θ (h y) ≡{nat ↛ nat} Θ (f (h y) y).
Proof.
  intros f.
  pose (a := fun x z => bind (Θ x x) (fun e => Θ e z)).
  destruct (EPFP a) as [γ Hγ].
  pose (ψ := fun y x => ret (f (γ x) y) : part nat).
  destruct (EPFP ψ) as [cy Hcy].
  exists (fun y => γ (cy y)).
  intros y z v.
  transitivity (a (cy y) z =! v).
  { apply (Hγ (cy y)). }
  unfold a. rewrite bind_hasvalue. split.
  - intros (e & He & Hv).
    specialize (Hcy y (cy y)). apply Hcy in He. unfold ψ in He.
    apply ret_hasvalue_inv in He. subst e. exact Hv.
  - intros Hv. exists (f (γ (cy y)) y). split; [|exact Hv].
    specialize (Hcy y (cy y)). apply Hcy. unfold ψ. eapply ret_hasvalue.
Qed.

(** ** Bridging c.e. sets and partial functions

    For every [EA]-index [c] we construct an [EPF]-index [β c] whose
    corresponding partial function has domain [W c]. *)
Lemma W_via_Θ :
  exists β : nat -> nat,
    forall c x, W c x <-> exists v, Θ (β c) x =! v.
Proof.
  destruct (EPFP (fun c x => mkpart (fun n => if φ c n is Some x'
                                            then if Nat.eqb x' x then Some 0 else None
                                            else None))) as [β Hβ].
  exists β. intros c x. split.
  - intros [n Hn]. exists 0.
    specialize (Hβ c x). cbn in Hβ. red in Hβ. apply Hβ.
    apply mkpart_hasvalue.
    + intros n1 n2 v1 v2 H1 H2.
      destruct (φ c n1) as [x1|] eqn:E1; try discriminate.
      destruct (Nat.eqb x1 x); try discriminate. inversion H1; subst.
      destruct (φ c n2) as [x2|] eqn:E2; try discriminate.
      destruct (Nat.eqb x2 x); try discriminate. inversion H2; subst.
      reflexivity.
    + exists n. rewrite Hn. rewrite Nat.eqb_refl. reflexivity.
  - intros [v Hv].
    specialize (Hβ c x). cbn in Hβ. red in Hβ. apply Hβ in Hv.
    apply mkpart_hasvalue1 in Hv as [n Hn].
    destruct (φ c n) as [x'|] eqn:E; try discriminate.
    destruct (Nat.eqb_spec x' x); try discriminate. subst x'.
    exists n. exact E.
Qed.

(** Conversely, for every [EPF]-index [d] we construct an [EA]-index
    [α d] enumerating the domain of [Θ d]. *)
Lemma Θ_via_W :
  exists α : nat -> nat,
    forall d x, W (α d) x <-> exists v, Θ d x =! v.
Proof.
  edestruct (EAS (fun d x => exists v, Θ d x =! v)) as [α Hα].
  - exists (fun k => let (d, xn) := unembed k in
                     let (x, n) := unembed xn in
                     if seval (Θ d x) n is Some _ then Some (d, x) else None).
    intros [d x]. split.
    + intros [v [n Hn] % seval_hasvalue].
      exists ⟨d, ⟨x, n⟩⟩. rewrite !embedP. now rewrite Hn.
    + intros [k Hk].
      destruct (unembed k) as [d' xn].
      destruct (unembed xn) as [x' n].
      destruct (seval (Θ d' x') n) as [v|] eqn:E; try discriminate.
      inversion Hk; subst. exists v.
      apply seval_hasvalue. eauto.
  - exists α. intros d x. specialize (Hα d x).
    unfold W. exact (iff_sym Hα).
Qed.

(** ** Uniform Recursion Theorem for [W]

    The same fixed-point principle as [URec_Θ] but at the level of
    c.e. sets indexed by [W]. *)
Lemma URec_W :
  forall f : nat -> nat -> nat,
    exists h : nat -> nat, forall y z, W (h y) z <-> W (f (h y) y) z.
Proof.
  intros f.
  destruct W_via_Θ as [β Hβ].
  destruct Θ_via_W as [α Hα].
  destruct (URec_Θ (fun d y => β (f (α d) y))) as [hΘ HhΘ].
  exists (fun y => α (hΘ y)). intros y z.
  rewrite Hα. rewrite Hβ. split.
  - intros [v Hv]. specialize (HhΘ y z v). cbn in HhΘ. red in HhΘ.
    apply HhΘ in Hv. eauto.
  - intros [v Hv]. specialize (HhΘ y z v). cbn in HhΘ. red in HhΘ.
    apply HhΘ in Hv. eauto.
Qed.

End Recursion.
