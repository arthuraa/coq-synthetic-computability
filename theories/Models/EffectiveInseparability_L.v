(* Axiom-free effective inseparability, built natively over T_L (the L
   calculus's step-indexed evaluator from Models/CT.v), instead of over an
   abstract EA instance. See ReducibilityDegrees/EffectiveInseparability.v
   for the abstract version this mirrors; see there for the overall
   structure of the argument.

   Fully proved, no Admitted/axioms: eff_insep_A0_B1_L_via_generic at the
   bottom of this file is the deliverable. η_L is built via LMuRecursion.mu (an
   L-level unbounded-search combinator) applied to a hand-extracted race
   predicate (raceBitOn/winnerBitOn); see the comment above
   SyntheticComputability.Models.LMuRecursion's Require, below, for why
   this replaced an earlier Por-based construction. *)

Require Import SyntheticComputability.Models.CT.
Require Import Undecidability.L.L.
Require Import Undecidability.L.Util.L_facts.
Require Import Undecidability.L.Tactics.LTactics.
Require Import SyntheticComputability.Shared.partial.
Require Import SyntheticComputability.Shared.embed_nat.
Require Import SyntheticComputability.Shared.mu_nat.
Require Import SyntheticComputability.Synthetic.Definitions.
Require Import SyntheticComputability.Synthetic.EnumerabilityFacts.
From SyntheticComputability.ReducibilityDegrees Require Import EffectiveInseparabilityGeneric.
Require Import SyntheticComputability.Axioms.EA.

(* Deliberately NOT importing SyntheticComputability.Models.LMuRecursion or
   Undecidability.L.Computability.Por here: both bring an L-term named `mu`
   into unqualified scope, shadowing partial.mu (which raceVal_L etc. use
   throughout this file). When η_L's real construction needs them, refer
   to LMuRecursion.mu / Por.Por by their qualified names instead of
   importing unqualified. *)

Require Import ssreflect.

(* Something transitively imported (partial.v's own definitions are marked
   Local, but apparently something else isn't) leaves "Set Implicit
   Arguments" active here, which silently makes explicit i/j/y-style
   parameters of lemmas below implicit whenever they're also inferable from
   a later hypothesis. Neutralize it so explicit arguments behave as
   written. *)
Unset Implicit Arguments.

(* CT.v already does `Import partial.implementation. Global Existing
   Instance monotonic_functions.` -- deliberately not repeating the
   `Import` here, since it pulls the *concrete* bind/mu/ret/hasvalue into
   scope, shadowing the abstract class-projection versions that generic
   lemmas like bind_hasvalue/mu_hasvalue are stated about. The Instance
   itself is inherited globally, so typeclass resolution still finds it. *)

(* --- 0. W_L / semidec_of_L, directly from θ_L's convergence ----------- *)

Definition W_L (c x : nat) : Prop := ter (θ_L c x).

Definition semidec_of_L (c x n : nat) : bool :=
  match T_L c x n with Some _ => true | None => false end.

Lemma semidec_of_L_spec c : semi_decider (semidec_of_L c) (W_L c).
Proof.
intros x; unfold semidec_of_L, W_L, ter; split.
- intros [v [n Hn]].
  cbn in Hn.
  exists n. rewrite Hn. reflexivity.
- intros [n Hn].
  destruct (T_L c x n) as [v|] eqn:E; [| discriminate].
  exists v, n. cbn. exact E.
Qed.

(* --- 1. raceVal_L / θ_L ------------------------------------------------ *)

Definition raceVal_L (i j y : nat) : part nat :=
  bind (mu (fun n => ret (orb (semidec_of_L i (embed (y,y)) n) (semidec_of_L j (embed (y,y)) n))))
       (fun n => if semidec_of_L i (embed (y,y)) n then ret 0 else ret 1).

Definition A0_L (z : nat) : Prop := θ_L (fst (unembed z)) (snd (unembed z)) =! 1.
Definition B1_L (z : nat) : Prop := θ_L (fst (unembed z)) (snd (unembed z)) =! 0.

(* --- 3. THE NEW PIECE: η_L represents raceVal_L as an actual L-term,
   built via LMuRecursion.mu (an L-level unbounded-search combinator)
   applied to a hand-extracted "race predicate", rather than by racing two
   raw L-terms via Por. (An earlier attempt raced tcode i / tcode j
   directly via Por and hit a real obstacle: Por's raw convergence doesn't
   match T_L/semidec_of_L's convergence, since T_L additionally requires
   the result to decode as a nat, which Por's doesHaltIn doesn't check;
   patching that gap for a *dynamically produced* value would need genuine
   self-interpretation, since checking whether a runtime value's syntax
   matches a Church numeral requires its *quoted* representation, which we
   have no way to compute for a value produced by *running* another
   program.) T_L/semidec_of_L's nat-decoding check is itself just an
   ordinary Rocq function (composing `eva` with `nat_unenc`), so it
   extracts to L-code directly and cleanly when built as ONE combined
   function -- no separate CBV-force-then-reflect step needed.

   Required, not Imported: LMuRecursion brings an L-term named `mu` into
   scope that would shadow partial.mu (used bare, e.g. in raceVal_L,
   elsewhere in this file) -- refer to it via LMuRecursion.mu. *)

Require SyntheticComputability.Models.LMuRecursion.

(* tcode c: the closed term coded by c, or a term that never converges on
   any input if c isn't a valid code. Always closed, but not necessarily
   already a value (lambda) -- enum_closed only guarantees closedness. *)
Definition tcode (c : nat) : term :=
  match enum_closed c with Some t => t | None => lam Omega end.

Lemma tcode_closed c : closed (tcode c).
Proof.
unfold tcode. destruct (enum_closed c) as [t|] eqn:E.
- eapply enum_closed_proc; eauto.
- Lproc.
Qed.

Require Import Undecidability.L.Datatypes.LNat.
Require Import Undecidability.L.Datatypes.LOptions.
Require Import Undecidability.L.Datatypes.LBool.
(* Deliberately NOT Import: Undecidability.L.Functions.Eval transitively
   re-exports Undecidability.L.Computability.Seval, which also defines
   `seval`, shadowing the *abstract* part-level `seval`
   (SyntheticComputability.Shared.partial's class field). Refer to
   eva/eva_equiv/eva_seval/app_converges/Omega_diverges via the qualified
   name Seval.<name> instead (nothing here needs doesHaltIn, Eval.v's own
   distinctive content, unqualified). *)
Require Undecidability.L.Functions.Eval.
Require Undecidability.L.Computability.Seval.
Require Import Undecidability.L.Tactics.Lbeta_nonrefl.
(* Same reasoning as Seval above: Require, not Import, to avoid pulling in
   Computability.Computability's own re-export of Computability.Seval
   (hence `seval` again). enc_extinj is used unqualified below via this
   Notation alias (aliasing is fine despite enc_extinj's implicit args). *)
Require Undecidability.L.Computability.Computability.
Notation enc_extinj := Undecidability.L.Computability.Computability.enc_extinj.
From SyntheticComputability Require Import Unenc.

Lemma seval_lambda {n : nat} {s v : term} : Seval.seval n s v -> lambda v.
Proof.
induction 1; eauto using lambda_lam.
Qed.

Lemma tcode_None_no_eva c (x : nat) n :
  enum_closed c = None -> Seval.eva n (L.app (tcode c) (enc x)) = None.
Proof.
intros Hc.
assert (Htc : tcode c = lam Omega) by (unfold tcode; rewrite Hc; reflexivity).
rewrite Htc.
destruct (Seval.eva n (L.app (lam Omega) (enc x))) as [w|] eqn:E; [exfalso | reflexivity].
pose proof (Seval.eva_equiv E) as Hw.
pose proof (seval_lambda (Seval.eva_seval E)) as Hlw.
destruct Hlw as [w' ->].
eapply Seval.Omega_diverges. rewrite <- Hw. symmetry. now redSteps.
Qed.

(* semidecHaltIn s n: does s converge within n eva-steps to a value that
   decodes as a nat -- unlike Por's plain doesHaltIn, this matches
   semidec_of_L/T_L's own notion of convergence exactly (semidec_semidecHaltIn
   below), and extracts cleanly as ONE combined function (eva composed with
   nat_unenc), since it never needs to reflect on a value produced *outside*
   itself -- eva's own internal result feeds nat_unenc within the same
   extracted computation. *)
Definition semidecHaltIn (s : term) (n : nat) : bool :=
  match Seval.eva n s with Some w => isSome (nat_unenc w) | None => false end.

Global Instance semidecHaltIn_computable : computable semidecHaltIn.
Proof.
extract.
Qed.

Lemma semidec_semidecHaltIn c x n :
  semidec_of_L c x n = semidecHaltIn (L.app (tcode c) (enc x)) n.
Proof.
unfold semidec_of_L, semidecHaltIn, T_L.
destruct (enum_closed c) as [t|] eqn:E.
- assert (Htc : tcode c = t) by (unfold tcode; now rewrite E).
  rewrite Htc. destruct (Seval.eva n (L.app t (enc x))) as [w|]; reflexivity.
- now rewrite (tcode_None_no_eva _ x n E).
Qed.

(* raceBitOn s t y n: does s or t win the race by step n, at the shared
   diagonal input embed (y,y) -- s, t held as opaque fixed term parameters
   (matching reify_app's earlier pattern), so extract never needs to
   reflect on how a term-valued Rocq function like tcode computes -- it
   only ever sees s, t as already-given constants. *)
Definition raceBitOn (s t : term) (y n : nat) : bool :=
  orb (semidecHaltIn (L.app s (enc (embed (y,y)))) n)
      (semidecHaltIn (L.app t (enc (embed (y,y)))) n).

Global Instance raceBitOn_computable s t : computable (raceBitOn s t).
Proof.
extract.
Qed.

(* winnerBitOn s y n: given the race (s vs whatever it's racing against)
   has resolved by step n, did s win. Deliberately bool-valued, not
   nat-valued -- a bool -> nat conversion function (0/1) reliably fails to
   extract once Models.CT is in scope (confirmed by direct probing: the
   exact same shape extracts fine in isolation, but "could not simplify
   some occuring term, shelved instead" once CT.v's transitive imports are
   present -- root cause not fully identified, but bool-valued functions
   of this same shape (semidecHaltIn, raceBitOn) extract cleanly even with
   CT.v in scope, so the fix is to stay bool-valued throughout and do the
   final "which nat does this bool mean" step via a Church-boolean
   selector spliced directly into η_L_body (winnerBit_branch below),
   exactly the technique used for Church-boolean branching everywhere else
   in this L-calculus library. *)
Definition winnerBitOn (s : term) (y n : nat) : bool :=
  semidecHaltIn (L.app s (enc (embed (y,y)))) n.

Global Instance winnerBitOn_computable s : computable (winnerBitOn s).
Proof.
extract.
Qed.

Lemma winnerBit_branch (b : bool) (v : nat) :
  L.app (L.app (ext b) (enc 0)) (enc 1) == enc v <-> (if b then v = 0 else v = 1).
Proof.
destruct b; cbn.
- split.
  + intros H. assert (Hb : L.app (L.app (ext true) (enc 0)) (enc 1) == enc 0) by now Lsimpl.
    rewrite Hb in H. symmetry in H. now apply enc_extinj in H.
  + intros ->. now Lsimpl.
- split.
  + intros H. assert (Hb : L.app (L.app (ext false) (enc 0)) (enc 1) == enc 1) by now Lsimpl.
    rewrite Hb in H. symmetry in H. now apply enc_extinj in H.
  + intros ->. now Lsimpl.
Qed.

(* raceP i j y: the search predicate `LMuRecursion.mu` actually needs --
   MUST be syntactically a `lam` (a value), not a bare application, since
   `mu`'s own `P_proc : proc P` hypothesis requires `P` to already be a
   lambda. η_L_body below builds this same shape inline (referencing the
   not-yet-substituted y via a de Bruijn index); η_L_body_inner_reduce
   connects the two once y is substituted in. *)
Definition raceP (i j y : nat) : term :=
  lam (L.app (L.app (ext (raceBitOn (tcode i) (tcode j))) (enc y)) (var 0)).

Lemma raceBit_proc0 i j : proc (ext (raceBitOn (tcode i) (tcode j))).
Proof.
exact (proc_ext (raceBitOn_computable (tcode i) (tcode j))).
Qed.

Lemma raceP_proc i j y : proc (raceP i j y).
Proof.
pose proof (raceBit_proc0 i j).
unfold raceP. Lproc.
Qed.

Definition η_L_body (i j : nat) : term :=
  lam (
    L.app
      (L.app
        (L.app (L.app (ext (winnerBitOn (tcode i))) (var 0))
               (L.app LMuRecursion.mu
                      (lam (L.app (L.app (ext (raceBitOn (tcode i) (tcode j))) (var 1)) (var 0)))))
        (enc 0))
      (enc 1)
  ).

Definition η_L (i j : nat) : nat := I_term (η_L_body i j).

Lemma η_L_body_proc i j : proc (η_L_body i j).
Proof.
pose proof LMuRecursion.mu_proc. pose proof (raceBit_proc0 i j).
unfold η_L_body. Lproc.
Qed.

Lemma η_L_body_inner_reduce i j y :
  L.app (η_L_body i j) (enc y) ==
  L.app (L.app (L.app (L.app (ext (winnerBitOn (tcode i))) (enc y)) (L.app LMuRecursion.mu (raceP i j y))) (enc 0)) (enc 1).
Proof.
unfold η_L_body, raceP.
apply star_equiv, step_star.
apply step_beta; [| Lproc].
cbn -[ext winnerBitOn raceBitOn tcode enc LMuRecursion.mu].
assert (Hc1 : subst (ext (winnerBitOn (tcode i))) 0 (enc y) = ext (winnerBitOn (tcode i)))
  by (apply SyntheticComputability.Models.CT.closed_subst, proc_closed, proc_ext).
assert (Hc2 : subst LMuRecursion.mu 0 (enc y) = LMuRecursion.mu)
  by (apply SyntheticComputability.Models.CT.closed_subst, proc_closed, LMuRecursion.mu_proc).
assert (Hc3 : subst (ext (raceBitOn (tcode i) (tcode j))) 1 (enc y) = ext (raceBitOn (tcode i) (tcode j)))
  by (apply SyntheticComputability.Models.CT.closed_subst, proc_closed, proc_ext).
assert (Hc4 : subst (enc 0) 0 (enc y) = enc 0)
  by (apply SyntheticComputability.Models.CT.closed_subst, proc_closed, proc_enc).
assert (Hc5 : subst (enc 1) 0 (enc y) = enc 1)
  by (apply SyntheticComputability.Models.CT.closed_subst, proc_closed, proc_enc).
rewrite Hc1. rewrite Hc2. rewrite Hc3. rewrite Hc4. rewrite Hc5.
reflexivity.
Qed.

(* --- 5. raceVal_L value unfolds via mu_hasvalue + semidec_of_L -------- *)

Lemma raceVal_iff_race_L i j y v :
  raceVal_L i j y =! v <->
    exists n,
      (semidec_of_L i (embed (y,y)) n = true \/ semidec_of_L j (embed (y,y)) n = true) /\
      (forall m, m < n -> semidec_of_L i (embed (y,y)) m = false
                        /\ semidec_of_L j (embed (y,y)) m = false) /\
      (if semidec_of_L i (embed (y,y)) n then v = 0 else v = 1).
Proof.
unfold raceVal_L.
split.
- intros [n [Hmu Hbranch]] % bind_hasvalue.
  apply mu_hasvalue in Hmu as [Htrue Hforall].
  simpl in Htrue, Hbranch, Hforall.
  apply (@ret_hasvalue_inv partial.implementation.monotonic_functions) in Htrue.
  apply Bool.orb_true_iff in Htrue.
  exists n. split; [exact Htrue |]. split.
  + intros m Hlt.
    specialize (Hforall m Hlt).
    apply (@ret_hasvalue_inv partial.implementation.monotonic_functions) in Hforall.
    apply Bool.orb_false_iff in Hforall.
    exact Hforall.
  + destruct (semidec_of_L i (embed (y, y)) n) eqn:EA.
    * apply (@ret_hasvalue_inv partial.implementation.monotonic_functions) in Hbranch. symmetry. exact Hbranch.
    * apply (@ret_hasvalue_inv partial.implementation.monotonic_functions) in Hbranch. symmetry. exact Hbranch.
- intros [n [Hor [Hlt Hval]]].
  apply bind_hasvalue.
  exists n. split.
  + apply mu_hasvalue. split.
    * simpl. apply (@ret_hasvalue' partial.implementation.monotonic_functions). apply Bool.orb_true_iff. exact Hor.
    * intros m Hm. simpl. apply (@ret_hasvalue' partial.implementation.monotonic_functions). apply Bool.orb_false_iff. exact (Hlt m Hm).
  + simpl. destruct (semidec_of_L i (embed (y,y)) n) eqn:EA.
    * rewrite Hval. apply (@ret_hasvalue partial.implementation.monotonic_functions).
    * rewrite Hval. apply (@ret_hasvalue partial.implementation.monotonic_functions).
Qed.

(* --- 4. θ_η_L: θ_L(η_L i j) agrees with raceVal_L exactly, via
   LMuRecursion.mu_sound/mu_complete applied to raceBitOn (tcode i) (tcode j) y,
   plus the semidec_semidecHaltIn correspondence tying
   raceBitOn/winnerOn back to semidec_of_L. ------------------------------ *)

Lemma raceP_dec' i j y : forall n : nat, exists b : bool, L.app (raceP i j y) (ext n) == ext b.
Proof.
intros n. unfold raceP. eexists. now Lsimpl.
Qed.

Lemma η_L_reduce i j y v :
  L.app (η_L_body i j) (enc y) == enc v
  <-> exists n, L.app LMuRecursion.mu (raceP i j y) == enc n
                /\ (if winnerBitOn (tcode i) y n then v = 0 else v = 1).
Proof.
rewrite η_L_body_inner_reduce.
split.
- intros H.
  assert (Hconv0 : converges (L.app (L.app (L.app (L.app (ext (winnerBitOn (tcode i))) (enc y)) (L.app LMuRecursion.mu (raceP i j y))) (enc 0)) (enc 1)))
    by (eexists; split; [exact H | Lproc]).
  apply Seval.app_converges in Hconv0 as [Hconv1 _].
  apply Seval.app_converges in Hconv1 as [Hconv2 _].
  apply Seval.app_converges in Hconv2 as [_ Hconv].
  destruct Hconv as [vn [Hvn Hlvn]].
  destruct (LMuRecursion.mu_sound (raceP_proc i j y) (raceP_dec' i j y) Hlvn Hvn) as [n [-> _]].
  exists n. split; [exact Hvn |].
  assert (Hcore : L.app (L.app (ext (winnerBitOn (tcode i))) (enc y)) (enc n) == ext (winnerBitOn (tcode i) y n))
    by now Lsimpl.
  rewrite Hvn in H. rewrite Hcore in H.
  now apply winnerBit_branch.
- intros [n [Hmu Hif]].
  rewrite Hmu.
  transitivity (L.app (L.app (ext (winnerBitOn (tcode i) y n)) (enc 0)) (enc 1)); [now Lsimpl |].
  now apply winnerBit_branch.
Qed.

Lemma θ_η_L i j y v : θ_L (η_L i j) y =! v <-> raceVal_L i j y =! v.
Proof.
unfold θ_L.
transitivity (L.app (η_L_body i j) (enc y) == enc v).
{ split.
  - intros [n Hn]. cbn in Hn. apply T_L_iff. apply η_L_body_proc. exists n. exact Hn.
  - intros H. destruct (T_L_iff y v (η_L_body_proc i j)) as [_ Hb].
    destruct (Hb H) as [n Hn]. exists n. cbn. exact Hn. }
rewrite η_L_reduce.
rewrite raceVal_iff_race_L.
split.
- intros [n [Hmu Hw]].
  destruct (LMuRecursion.mu_sound (raceP_proc i j y) (raceP_dec' i j y)
              (proc_lambda (proc_enc n)) Hmu) as [n' [Heq [Htrue Hmin]]].
  rewrite ext_is_enc in Heq. apply inj_enc in Heq. subst n'.
  assert (Htrue' : semidec_of_L i (embed (y,y)) n = true \/ semidec_of_L j (embed (y,y)) n = true).
  { unfold raceP in Htrue. LsimplHypo. Lrewrite in Htrue. symmetry in Htrue.
    apply enc_extinj in Htrue. symmetry in Htrue. unfold raceBitOn in Htrue. rewrite <- !semidec_semidecHaltIn in Htrue.
    now apply Bool.orb_true_iff in Htrue. }
  assert (Hmin' : forall m, m < n -> semidec_of_L i (embed (y,y)) m = false /\ semidec_of_L j (embed (y,y)) m = false).
  { intros m Hlt. specialize (Hmin m Hlt). unfold raceP in Hmin. LsimplHypo. Lrewrite in Hmin. symmetry in Hmin.
    apply enc_extinj in Hmin. symmetry in Hmin. unfold raceBitOn in Hmin. rewrite <- !semidec_semidecHaltIn in Hmin.
    now apply Bool.orb_false_iff in Hmin. }
  exists n. split; [exact Htrue' |]. split; [exact Hmin' |].
  unfold winnerBitOn in Hw. rewrite <- semidec_semidecHaltIn in Hw. exact Hw.
- intros [n [Hor [Hmin Hv]]].
  assert (Htrue : raceBitOn (tcode i) (tcode j) y n = true).
  { unfold raceBitOn. rewrite <- !semidec_semidecHaltIn. now apply Bool.orb_true_iff. }
  assert (Hminb : forall m, m < n -> raceBitOn (tcode i) (tcode j) y m = false).
  { intros m Hlt. unfold raceBitOn. rewrite <- !semidec_semidecHaltIn. apply Bool.orb_false_iff. exact (Hmin m Hlt). }
  exists n. split.
  + assert (HPtrue : L.app (raceP i j y) (ext n) == ext true) by (unfold raceP; Lsimpl; now rewrite Htrue).
    destruct (LMuRecursion.mu_complete (raceP_proc i j y) (raceP_dec' i j y) HPtrue) as [n0 Hn0].
    destruct (LMuRecursion.mu_sound (raceP_proc i j y) (raceP_dec' i j y) (proc_lambda (proc_enc n0)) Hn0)
      as [n0' [Heq0 [Htrue0 Hmin0]]].
    rewrite ext_is_enc in Heq0. apply inj_enc in Heq0. subst n0'.
    assert (Htrue0' : raceBitOn (tcode i) (tcode j) y n0 = true).
    { unfold raceP in Htrue0. LsimplHypo. Lrewrite in Htrue0. symmetry in Htrue0. now apply enc_extinj in Htrue0. }
    assert (Hmin0' : forall m, m < n0 -> raceBitOn (tcode i) (tcode j) y m = false).
    { intros m Hm. specialize (Hmin0 m Hm). unfold raceP in Hmin0. LsimplHypo. Lrewrite in Hmin0. symmetry in Hmin0. now apply enc_extinj in Hmin0. }
    assert (Hn0n : n0 = n) by (eapply minimal_unique; eauto).
    subst n0. exact Hn0.
  + unfold winnerBitOn. rewrite <- semidec_semidecHaltIn. exact Hv.
Qed.

(* --- Payoff: eff_insep_A0_B1_L_via_generic is exactly
   eff_insep_A0_B1_generic (ReducibilityDegrees/
   EffectiveInseparabilityGeneric.v) instantiated with
   W_L/semidec_of_L/θ_L/η_L -- the *same* instantiation recipe
   ReducibilityDegrees/EffectiveInseparability.v uses with
   W/semidec_of/Θ_num/η, formally tying this construction to that
   shared generic argument rather than being an independently-proved
   lookalike. ------------------------------------------------------- *)

Lemma eff_insep_A0_B1_L_via_generic : eff_insep_shape W_L A0_L B1_L.
Proof.
  exact (eff_insep_A0_B1_generic W_L semidec_of_L semidec_of_L_spec θ_L η_L θ_η_L).
Qed.
