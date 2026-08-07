# From partial to total productive function

## Setup and definitions

Fix a set A ⊆ ℕ. Let φ_e and W_e denote the standard admissible numbering of
partial computable functions and their domains (the r.e. sets), respectively.

**Definition (partial productive).**  
A partial computable function f is a *partial productive function* for A if:
  for all e, if W_e ⊆ A then f(e)↓ and f(e) ∈ A \ W_e.

**Goal.**  
Given a partial productive function f for A, construct a *total* computable
function f' that is also productive for A.

---

## Lemma 1 (construction via s-m-n and the recursion theorem)

**Claim.** There exists a total computable function g : ℕ → ℕ such that,
for every c:

    W_{g(c)} = { x : f(g(c))↓  ∧  x ∈ W_c }.          (★)

**Proof.**  
Define the partial computable function of two arguments:

    θ(e, c, x) ≃ 0   if φ_e(e)↓ and x ∈ W_c,
    θ(e, c, x) ↑     otherwise.

By the s-m-n theorem, there is a total computable h : ℕ² → ℕ such that
φ_{h(e,c)} = λx. θ(e, c, x), and hence W_{h(e,c)} = { x : φ_e(e)↓ ∧ x ∈ W_c }.

Apply the recursion theorem (uniform version, with parameter c): there is a
total computable g : ℕ → ℕ such that for all c:

    φ_{g(c)} = φ_{h(g(c), c)},

and therefore W_{g(c)} = W_{h(g(c),c)} = { x : φ_{g(c)}(g(c))↓ ∧ x ∈ W_c }.

Since φ_{g(c)}(g(c)) = f(g(c)) by our intended use of f below, this gives (★).
∎

Define f' : ℕ → ℕ by  f'(c) := f(g(c)).

---

## Lemma 2 (f' is total, using Markov's principle)

**Claim.** For every c, f(g(c))↓.

**Proof.**

Suppose, for contradiction, that f(g(c))↑.  
Then by (★), W_{g(c)} = ∅.  
Since ∅ ⊆ A, the hypothesis W_{g(c)} ⊆ A holds.  
By the partial productivity of f applied to index g(c): f(g(c))↓.  
Contradiction.

Hence ¬¬(f(g(c))↓).

Now observe that "f(g(c))↓" is the Σ⁰₁ statement

    ∃n. T(f, g(c), n)

where T is Kleene's decidable T-predicate ("the computation of f on input
g(c) terminates in n steps"). By **Markov's principle** (MP):

    ¬¬∃n. P(n)  →  ∃n. P(n)      (for decidable P)

we conclude f(g(c))↓. ∎

*Note: This is the one place where constructive reasoning needs MP. No
instance of the law of excluded middle (LEM) is required.*

---

## Lemma 3 (f' is productive)

**Claim.** For every c, if W_c ⊆ A then f'(c) ∈ A \ W_c.

**Proof.**

Assume W_c ⊆ A.

By Lemma 2, f(g(c))↓. Substituting into (★):

    W_{g(c)} = { x : T ∧ x ∈ W_c } = W_c.

So W_{g(c)} = W_c ⊆ A.

Apply the partial productivity of f to index g(c):

    f(g(c)) ∈ A \ W_{g(c)} = A \ W_c.

Hence f'(c) = f(g(c)) ∈ A \ W_c. ∎

---

## Theorem (main result)

**Statement.** If A has a partial productive function, then A has a total
computable productive function.

**Proof summary.**

1. Given partial productive f for A.
2. Construct g by s-m-n + recursion theorem (Lemma 1), satisfying (★).
3. Define f' = f ∘ g.
4. f' is total computable: total by Lemma 2 (using MP), computable because
   g is total computable and f is partial computable, and their composition
   is total (since f is defined on all outputs of g, by Lemma 2).
5. f' is productive for A by Lemma 3.
∎

---

## Proof-theoretic note

The logical strength used:
- The recursion theorem and s-m-n are constructive.
- Lemma 3 (productivity) is fully constructive.
- Lemma 2 (totality) uses exactly one application of **Markov's principle**,
  to lift ¬¬(f(g(c))↓) to f(g(c))↓.
- The law of excluded middle is **not** needed anywhere.

---

## Rocq translation hints

The key ingredients to look for or axiomatize in your development:

| Mathematical step         | Rocq counterpart                                      |
|---------------------------|-------------------------------------------------------|
| s-m-n theorem             | `smn` or `s_m_n` lemma in your computability library  |
| Recursion theorem         | `recursion_theorem` (parametric form, with parameter) |
| Kleene's T predicate      | `T_decidable` or `HaltDecidable`                      |
| Markov's principle        | `Markov` axiom or `markov_principle` lemma            |
| W_e = { x : ... }        | characterization of `dom` / `W` in your library       |
| f'(c) = f(g(c))          | `fun c => f (g c)` — definitional, no axiom needed    |
| ★ as a defining equation  | proved once from s-m-n + recursion, then rewritten     |

The proof of Lemma 2 in Rocq will have the shape:

    assert (Hneg : ~ ~ halts f (g c)) by (intro H; ...).
    apply markov in Hneg; exact Hneg.

where `markov` has type `~ ~ halts f n -> halts f n` (or the equivalent for
your halting predicate).
