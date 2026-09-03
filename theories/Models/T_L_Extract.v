(* T_L is genuinely and uniformly extractable to L: this file gives an
   extraction-friendly reformulation of T_L, for arbitrary runtime
   (c, x, n), not just one fixed instance.

   Three extraction constraints this reformulation works around:

   1. A `fun! <n,m> => ...` pattern-let over `unembed` does not extract:
      `unembed`'s `computable` instance is registered via `computableExt`
      (extensional equality to a Fixpoint), not a direct `extract`, and
      pattern-let destructuring doesn't trigger the right unfolding for
      `extract` to see through it. Plain `fst`/`snd` projections work
      instead.

   2. A file needing `Undecidability.L.Datatypes.LTerm`'s `term`
      constructor instances for `extract`'s typeclass search must
      `Require Import` it directly -- arriving transitively is not
      enough.

   3. A recursive function pattern-matching on `term` extracts only when
      the `term` argument is the FIRST parameter and the return type is
      `term` or `option X` -- a bare `bool`/`nat` return breaks
      extraction, even for the same recursion structure over the same
      constructors. This is why the closedness check below is phrased as
      a `term -> nat -> option nat` function, not as a
      `nat -> term -> ...`-shaped boolean decision procedure. *)

Require Import SyntheticComputability.Models.CT.
Require Import Undecidability.L.Tactics.LTactics.
Require Import Undecidability.L.Datatypes.LNat.
Require Import Undecidability.L.Datatypes.LTerm.
Require Import Undecidability.L.Datatypes.LBool.
Require Import Undecidability.L.Datatypes.LOptions.
Require Import Undecidability.L.Datatypes.List.List_nat.
Require Import SyntheticComputability.Shared.embed_nat.
Require Import Undecidability.L.Functions.Eval.

(* --- Fix 1: enum_term, via fst/snd instead of pattern-let unembed ------ *)

Definition enum_term' (p : nat) : option term :=
  nth_error (list_enumerator_term (fst (unembed p))) (snd (unembed p)).

Instance enum_term'_computable : computable enum_term'.
Proof. extract. Qed.

Lemma enum_term'_eq p : enum_term' p = enum_term p.
Proof.
  unfold enum_term', enum_term.
  destruct (unembed p) as [n0 m0]. reflexivity.
Qed.

(* --- Fix 3: bound-checking, term-first argument order, option output -- *)

Fixpoint bound_o (s : term) (k : nat) : option nat :=
  match s with
  | var n => if Nat.ltb n k then Some 0 else None
  | app s t => match bound_o s k with
               | Some _ => bound_o t k
               | None => None
               end
  | lam s => bound_o s (S k)
  end.

Instance bound_o_computable : computable bound_o.
Proof. extract. Qed.

Lemma bound_o_correct s k : (exists v, bound_o s k = Some v) <-> bound k s.
Proof.
  revert k. induction s; intros k; cbn.
  - destruct (Nat.ltb_spec0 n k); split.
    + intros _. now constructor.
    + eauto.
    + intros [? [=]].
    + inversion 1; lia.
  - destruct (bound_o s1 k) as [v1|] eqn:E1.
    + assert (H1 : bound k s1) by (apply IHs1; eauto).
      split.
      * intros [v Hv]. constructor; auto. apply IHs2; eauto.
      * intros Hb. inversion Hb; subst. apply IHs2; auto.
    + assert (H1 : ~ bound k s1) by (intros H; apply IHs1 in H; destruct H; congruence).
      split.
      * intros [? [=]].
      * intros Hb. inversion Hb; subst. tauto.
  - rewrite IHs. split; [now constructor | now inversion 1].
Qed.

(* --- enum_closed, extractable ------------------------------------------ *)

Definition enum_closed' (n : nat) : option term :=
  match enum_term' n with
  | Some t => match bound_o t 0 with Some _ => Some t | None => None end
  | None => None
  end.

Instance enum_closed'_computable : computable enum_closed'.
Proof. extract. Qed.

Lemma enum_closed'_eq n : enum_closed' n = enum_closed n.
Proof.
  unfold enum_closed', enum_closed. rewrite enum_term'_eq.
  destruct (enum_term n) as [t|]; [| reflexivity].
  destruct (bound_o t 0) as [v|] eqn:E.
  - destruct bound_dec as [Hd|Hd]; [reflexivity |].
    exfalso. apply Hd. apply bound_o_correct. eauto.
  - destruct bound_dec as [Hd|Hd]; [| reflexivity].
    exfalso. apply bound_o_correct in Hd. destruct Hd. congruence.
Qed.

(* --- The payoff: T_L itself, extractable, for arbitrary runtime (c,x,n) *)

Definition T_L' (c x n : nat) : option nat :=
  match enum_closed' c with
  | Some t => match eva n (L.app t (enc x)) with
              | Some t' => nat_unenc t'
              | None => None
              end
  | None => None
  end.

Instance T_L'_computable : computable T_L'.
Proof. extract. Qed.

Lemma T_L'_eq c x n : T_L' c x n = T_L c x n.
Proof.
  unfold T_L', T_L. rewrite enum_closed'_eq. reflexivity.
Qed.
