Require Import SyntheticComputability.Axioms.EA.
Require Import SyntheticComputability.Shared.Pigeonhole.
Require Import SyntheticComputability.Shared.FinitenessFacts.
Require Import SyntheticComputability.Synthetic.reductions SyntheticComputability.Synthetic.truthtables.
Require Import SyntheticComputability.Synthetic.DecidabilityFacts SyntheticComputability.Synthetic.EnumerabilityFacts SyntheticComputability.Synthetic.SemiDecidabilityFacts SyntheticComputability.Synthetic.ReducibilityFacts.
Require Import SyntheticComputability.Shared.ListAutomation.
Require Import List Arith.

Section Assume_EA.

Context {EA : EA}.

Notation φ := (proj1_sig EA).
Notation EAP := (proj2_sig EA).

Import ListNotations ListAutomationNotations.

Definition productive (p : nat -> Prop) := exists f : nat -> nat, forall c, (forall x, W c x -> p x) -> p (f c) /\ ~ W c (f c).

Lemma productive_nonenumerable p :
  productive p -> ~ enumerable p.
Proof.
  intros [f Hf] [c Hc] % W_spec.
  destruct (Hf c) as [H1 % Hc H2].
  eapply Hc. tauto.
Qed.

Lemma K0_productive :
  productive (compl K0).
Proof.
  exists (fun n => n). intros c H.
  specialize (H c). unfold K0, compl in *. tauto.
Qed.

Lemma productive_cantor_infinite p :
  productive p -> cantor_infinite p.
Proof.
  specialize List_id as [c_l c_spec]. intros [f Hf].
  eapply (weakly_generative_cantor_infinite). econstructor.
  intros l.
  exists (f (c_l l)). intros Hl. split.
  - specialize (Hf (c_l l)).
    rewrite <- c_spec. eapply Hf.
    intros x. rewrite c_spec. eapply Hl.
  - eapply Hf. intros x. rewrite c_spec. eapply Hl.
Qed.

Lemma productive_subpredicate p :
  productive p ->
  exists q : nat -> Prop, enumerable q /\ cantor_infinite q /\ (forall x, q x -> p x).
Proof.
  intros H.
  eapply cantor_infinite_problem.
  eapply productive_cantor_infinite. eauto.
Qed.

Lemma productive_red p q :
  p ⪯ₘ q -> productive p -> productive q.
Proof.
  intros [f Hf] [g Hg].
  specialize (SMN' f) as [k Hk].
  exists (fun c => f (g (k c))). intros c Hs.
  assert (Hkc : forall x, W (k c) x -> p x) by  (intros; now eapply Hf, Hs, Hk).
  split.
  - now eapply Hf, Hg.
  - intros ?. eapply Hg, Hk; eauto.
Qed.

Lemma many_one_complete_subpredicate p :
  m-complete p ->
  exists q : nat -> Prop, enumerable q /\ cantor_infinite q /\ (forall x, q x -> compl p x).
Proof.
  intros Hcomp. eapply productive_subpredicate.
  eapply productive_red.
  - eapply red_m_complement. eapply Hcomp. eapply K0_enum.
  - eapply K0_productive.
Qed.

Definition simple (p : nat -> Prop) :=
  enumerable p /\ ~ exhaustible (compl p) /\ ~ exists q, enumerable q /\ ~ exhaustible q /\ (forall x, q x -> compl p x).

Lemma simple_non_enumerable p :
  simple p -> ~ enumerable (compl p).
Proof.
  intros (H1 & H2 & H3) H4.
  apply H3. eauto.
Qed.

Lemma simple_undecidable p :
  simple p -> ~ decidable p.
Proof.
  intros Hs Hd % decidable_complement % decidable_enumerable; eauto.
  now eapply simple_non_enumerable in Hs.
Qed.

Lemma simple_m_incomplete p :
  simple p -> ~ m-complete p.
Proof.
  intros (H1 & H2 & H3) (q & Hq1 & Hq2 & Hq3) % many_one_complete_subpredicate.
  eapply H3. exists q; repeat split; eauto.
  now eapply unbounded_non_finite, cantor_infinite_unbounded.
Qed.

Lemma non_finite_non_empty {X} (p : X -> Prop) :
  ~ exhaustible p -> ~~ exists x, p x.
Proof.
  intros H1 H2. apply H1. exists []. firstorder.
Qed.

Lemma simple_no_cylinder p :
  (fun '((x, n) : nat * nat) => p x) ⪯₁ p -> ~ simple p.
Proof.
  intros [f [inj_f Hf]] (H1 & H2 & H3). red in Hf.
  apply (non_finite_non_empty _ H2). intros [x0 Hx0].
  apply H3.
  exists (fun x => exists n, x = f (x0, n)). split. 2:split.
  - eapply semi_decidable_enumerable; eauto.
    exists (fun x n => Nat.eqb x (f (x0, n))).
    intros x. split; intros [n H]; exists n; destruct (Nat.eqb_spec x (f (x0, n))); firstorder congruence.
  - eapply unbounded_non_finite, cantor_infinite_unbounded.
    exists (fun n => f (x0, n)). intros. split. eauto.
    now intros ? [=] % inj_f.
  - intros ? [n ->]. red. now rewrite <- (Hf (x0, n)).
Qed.

(** * Creative sets *)

(** A set is creative when it is enumerable and its complement is productive.
    Intuitively, a productivity function effectively witnesses that the
    complement of a creative set is not enumerable. *)

Definition creative (p : nat -> Prop) := enumerable p /\ productive (compl p).

Lemma K0_creative : creative K0.
Proof.
  split.
  - eapply K0_enum.
  - eapply K0_productive.
Qed.

(** Every Σ⁰₁-complete (i.e., m-complete for enumerable sets) set is creative. *)
Theorem m_complete_to_creative p :
  enumerable p -> m-complete p -> creative p.
Proof.
  intros Hp Hcomp. split; [exact Hp|].
  eapply productive_red.
  - eapply red_m_complement, Hcomp, K0_enum.
  - eapply K0_productive.
Qed.

(** Creative sets are undecidable: a decidable set has an enumerable
    complement, but a creative set's complement is productive, hence never
    enumerable. Constructive, no further hypotheses beyond the ambient EA
    instance. *)
Lemma creative_undecidable (p : nat -> Prop) : creative p -> ~ decidable p.
Proof.
  intros [_ Hprod] Hd.
  eapply productive_nonenumerable; [exact Hprod |].
  eapply decidable_enumerable_complement; eauto.
Qed.

(** Every m-complete enumerable set is undecidable, via creativity. *)
Lemma m_complete_undecidable (p : nat -> Prop) : enumerable p -> m-complete p -> ~ decidable p.
Proof.
  intros He Hc.
  eapply creative_undecidable.
  eapply m_complete_to_creative; eauto.
Qed.

End Assume_EA.

From SyntheticComputability.Shared Require Import partial.
From SyntheticComputability.Basic Require Import Recursion.
From SyntheticComputability.CRM Require Import principles.

Section PartialProductive.

Context {EA : EA}.
Context {Part : partiality}.

Notation φ := (proj1_sig EA).
Notation EAP := (proj2_sig EA).

Definition partial_productive (p : nat -> Prop) : Prop :=
  exists f : nat -> part nat,
    forall c,
      (forall x, W c x -> p x) ->
      exists k,
        hasvalue (f c) k /\ p k /\ ~ W c k.

Lemma partial_productive_iff_productive (p : nat -> Prop) :
  MP -> partial_productive p <-> productive p.
Proof.
intros MP; split.
- intros [f Hf].
  (* Build an enumerator λ for pairs (e,c) listing values x with
      seval (f e) n = Some x and W c x. *)
  destruct (EAS
    (fun iy z => exists e c, iy = ⟨e, c⟩ /\ exists n, seval (f e) n = Some z /\ W c z)
  ) as [λ Hλ].
  { exists (fun k => let (e, r) := unembed k in
                      let (cn, m) := unembed r in
                      let (c, n) := unembed cn in
                      match seval (f e) n, φ c m with
                      | Some z1, Some z2 => if z1 =? z2 then Some (⟨e, c⟩, z1) else None
                      | _, _ => None end).
    intros [iy z]. split.
    - intros (e & c & -> & n & Hse & m & Hφ).
      exists ⟨e, ⟨⟨c, n⟩, m⟩⟩.
      rewrite !embedP, Hse, Hφ.
      now rewrite Nat.eqb_refl.
    - intros [k Hk].
      destruct (unembed k) as [e r],
              (unembed r) as [cn m],
              (unembed cn) as [c n].
      destruct (seval (f e) n) as [z1|] eqn:Ese; [| discriminate].
      destruct (φ c m) as [z2|] eqn:Ephi; [| discriminate].
      destruct (Nat.eqb_spec z1 z2) as [->|_].
      + injection Hk; intros -> <-. exists e, c.
        split; [reflexivity|].
        exists n.
        split; [exact Ese| exists m; exact Ephi].
      + discriminate Hk.
  }

  destruct (URec_W (fun i y => λ ⟨i, y⟩)) as [g Hg].

  assert (Hf_total : forall c, ter (f (g c))).
  { intros c.
    assert (Hter : ~~ ter (f (g c))).
    { intro Hnter.
      (* If f (g c) does not terminate then there is no n with seval ... = Some _,
          so by Hλ and Hg we get W (g c) = ∅. *)
      assert (Hnexist : forall x, ~ (exists n, seval (f (g c)) n = Some x)).
      { intros x [??]. apply Hnter. exists x. eapply seval_hasvalue; eauto. }
      assert (HnotWgc : forall x, ~ W (g c) x).
      { intros x Hgx. specialize (Hg c x).
        specialize (Hλ (⟨g c, c⟩)) as Hλgc.
        apply Hg in Hgx.
        edestruct Hλgc as [_ Hλgc2].
        apply Hλgc2 in Hgx as (e & c' & Heq & [n [Hse Hw]]).
        apply embed_pair_inv in Heq as [<- <-].
        apply (Hnexist x). exists n. exact Hse.
      }
      (* From W (g c) = ∅ we get W (g c) ⊆ p, so applying Hf yields a value, contradicting Hnter. *)
      assert (Wsub : forall z, W (g c) z -> p z).
      { intros z Hz. exfalso. apply (HnotWgc z Hz). }
      destruct (Hf (g c) Wsub) as (k & Hk & _ & _).
      apply Hnter. exists k. exact Hk.
    }
    eapply MP_to_MP_partial; eauto.
  }
  assert (HWgc : forall c (Hc : forall x, W c x -> p x) x, W (g c) x -> p x).
  { intros c ? x Hgx.
    apply (Hg c x) in Hgx.
    specialize (Hλ (⟨g c, c⟩)) as Hλgc.
    edestruct Hλgc as [_ Hλgc2].
    apply Hλgc2 in Hgx as (e & c' & Heq & [n [Hse Hw]]).
    apply embed_pair_inv in Heq as [<- <-].
    auto. }
  assert (Heval : forall c k (Hk : f (g c) =! k), eval (Hf_total c) = k).
  { intros ?? Hk; symmetry; eapply hasvalue_det; [exact Hk | apply eval_hasvalue]. }
  (* Define the total productive witness by extracting the value from f (g c). *)
  exists (fun c => eval (Hf_total c)).
  intros c Hc; split;
    destruct (Hf (g c) (HWgc c Hc)) as (k & Hk & ? & Hwk);
    rewrite (Heval c k Hk); [assumption |].
  intro Hwc. apply Hwk. apply (Hg c k).
  specialize (Hλ (⟨g c, c⟩) k) as [Hλgc _].
  apply Hλgc.
  exists (g c), c.
  split; [reflexivity | ].
  apply seval_hasvalue in Hk as [n Hn].
  exists n.
  split; [exact Hn | exact Hwc].
- intros [f Hf].
  exists (fun c => ret (f c)).
  intros c [Hp Hw] % Hf.
  exists (f c).
  split; eauto.
  apply ret_hasvalue.
Qed.

End PartialProductive.

(** ** Creative ⇒ Σ⁰₁-complete (Myhill, 1955)

    The reverse direction of Myhill's theorem leans on Kleene's Uniform
    Recursion Theorem [Basic/Recursion.v:URec_W], which is derivable
    from [EA] together with [partiality] (the chain [EA -> SCT -> EPF]
    of [Axioms/Equivalence.v] gives a partial-function indexing).

    Turning the fixed-point into a many-one reduction additionally
    requires Markov's principle, to extract a positive membership
    witness from a double-negated one in an enumerable set.  This is
    unavoidable: MP is equivalent to every m-complete enumerable set
    being stable (see [CRM/principles.v]). *)

Section Creative_is_complete.

Context {EA_inst : EA}.
Context {Part : partiality}.

Notation φ := (proj1_sig EA_inst).
Notation EAP := (proj2_sig EA_inst).

Hypothesis MP_assm : MP.

(** *** Myhill's theorem: every creative set is Σ⁰₁-complete.

    The proof follows Mayr's slides (Computability Theory, CU Boulder
    2021, lecture 20): given [A] creative with productivity function
    [q] for [compl A] and an arbitrary enumerable [B], Uniform Recursion
    yields [h] with
    [[
      W (h y) z  ↔  z = q (h y) ∧ y ∈ B
    ]]
    so [W (h y) = {q (h y)}] when [y ∈ B] and [∅] otherwise.  Productivity
    then forces [q (h y) ∈ A] exactly when [y ∈ B]. *)
Theorem creative_to_m_complete A :
  creative A -> m-complete A.
Proof.
  intros [HAenum [q Hq]] B HBenum.
  (* Get an EA-index [cB] for B. *)
  destruct (do_EA B HBenum) as [cB HcB].
  (* Parametric family of c.e. sets: W (λ ⟨i, y⟩) z ↔ z = q i ∧ y ∈ B. *)
  edestruct (EAS (fun iy z => exists i y, iy = ⟨i, y⟩ /\ z = q i /\ W cB y))
    as [λ Hλ].
  { exists (fun k => let (i, yn) := unembed k in
                     let (y, n) := unembed yn in
                     if φ cB n is Some y' then
                       if Nat.eqb y' y then Some (⟨i, y⟩, q i) else None
                     else None).
    intros [iy z]. split.
    - intros (i & y & -> & -> & [n Hn]).
      exists ⟨i, ⟨y, n⟩⟩. rewrite embedP. rewrite embedP.
      rewrite Hn. now rewrite Nat.eqb_refl.
    - intros [k Hk].
      destruct (unembed k) as [i' yn].
      destruct (unembed yn) as [y' n].
      destruct (φ cB n) as [y''|] eqn:Eφ; try discriminate.
      destruct (Nat.eqb_spec y'' y'); try discriminate.
      inversion Hk; subst. exists i', y'.
      split; [reflexivity|]. split; [reflexivity|].
      exists n. exact Eφ. }
  (* Apply URec_W to obtain h with W (h y) = {q (h y)} when y ∈ B, ∅ else. *)
  destruct (URec_W (fun i y => λ ⟨i, y⟩)) as [h Hh].
  (* Characterise W (h y). *)
  assert (Wh : forall y z,
             W (h y) z <-> z = q (h y) /\ B y).
  { intros y z. rewrite Hh. rewrite <- (Hλ ⟨h y, y⟩ z).
    split.
    - intros (i' & y' & Hpair & Hz & Hy').
      apply (f_equal unembed) in Hpair. rewrite !embedP in Hpair.
      injection Hpair as Heq1 Heq2.
      rewrite <- Heq1 in Hz.
      rewrite <- Heq2 in Hy'.
      split; [exact Hz | now apply HcB].
    - intros [-> HyB]. exists (h y), y.
      split; [reflexivity |]. split; [reflexivity |].
      now apply HcB. }
  exists (fun y => q (h y)). intros y. split.
  - (* y ∈ B → q (h y) ∈ A *)
    intros HyB.
    (* ¬¬ A (q (h y)) follows from productivity; MP then yields A (q (h y)). *)
    assert (HWhy : W (h y) (q (h y))) by (apply Wh; split; auto).
    apply (MP_to_MP_semidecidable MP_assm nat A
             (enumerable_semi_decidable discrete_nat HAenum) (q (h y))).
    intros HnA.
    assert (Wsub : forall z, W (h y) z -> compl A z).
    { intros z Hz. apply Wh in Hz as [-> _]. exact HnA. }
    destruct (Hq (h y) Wsub) as [_ Hnotw]. exact (Hnotw HWhy).
  - (* q (h y) ∈ A → y ∈ B *)
    intros HqA.
    (* y ∉ B would make W (h y) = ∅ ⊆ compl A; productivity yields
       q (h y) ∈ compl A, contradicting [HqA]. *)
    apply (MP_to_MP_semidecidable MP_assm nat B
             (enumerable_semi_decidable discrete_nat HBenum) y).
    intros HnB.
    assert (Wsub : forall z, W (h y) z -> compl A z).
    { intros z Hz. apply Wh in Hz as [_ ?]. contradiction. }
    destruct (Hq (h y) Wsub) as [HqcA _]. exact (HqcA HqA).
Qed.

End Creative_is_complete.
