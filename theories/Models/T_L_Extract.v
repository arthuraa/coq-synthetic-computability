(* Resolves the long-standing blocker on Models/CT.v's commented-out
   `T_L_computable`/`enum_term_computable` TODOs: T_L is, in fact,
   genuinely and uniformly extractable to L, for arbitrary runtime
   (c, x, n) -- not just a single known instance (contra the earlier,
   more limited per-instance workaround in the now-removed
   Models/PerInstanceGuard.v).

   Kept as a standalone file (not folded into CT.v) so CT.v's original
   TODOs can be filled in later by hand, at leisure, rather than
   immediately overwritten here.

   Three narrow, specific fixes were needed, found by bisecting against
   already-working extractions (subst, eva):

   1. enum_term's `fun! <n,m> => ...` notation expands to a *pattern-let*
      `let (n,m) := unembed p in ...`, and `extract` cannot see through
      that pattern-let for `unembed` specifically -- its `computable`
      instance was registered via `computableExt` (extensional equality
      to a Fixpoint), not a direct `extract`, and pattern-let destructuring
      doesn't trigger the right unfolding. Rewriting via plain `fst`/`snd`
      applications instead of let-pattern destructuring fixes this.

   2. `Undecidability.L.Datatypes.LTerm` needs a direct, explicit `Require
      Import` -- relying on it arriving transitively (e.g. via CT.v) is
      not enough for `extract`'s own typeclass search to find term's
      constructor instances.

   3. The real one: a *recursive* function pattern-matching on `term`
      only extracts successfully when (a) the `term` argument is the
      FIRST parameter (not preceded by a `nat`, as the natural
      `bound_dec`-style signature `nat -> term -> ...` writes it), and
      (b) the return type is `term` or `option X` -- a bare `bool`/`nat`
      return breaks extraction, even though the very same recursion
      structure over the very same three constructors, with return type
      `term`, extracts fine (as `subst` and `strip_lams`-style functions
      demonstrate). So the closedness check `enum_closed` needs (whether
      `bound 0 t` holds) has to be phrased as an `option`-returning
      function of type `term -> nat -> option nat`, with that exact
      argument order, rather than `Undecidability.L.Util.L_facts.bound_dec
      : nat -> term -> dec (bound k s)` (which extracts nowhere at all,
      being a hand-rolled decidability proof, not a plain recursive
      boolean function to begin with). *)

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
