# Project-authored additions

This is a fork of Yannick Forster et al.'s general-purpose synthetic
computability library (see `README.md` for the original project). Some
content under `theories/Models/` and `theories/ReducibilityDegrees/` was
added specifically to support a separate project -- a Rocq formalization of
undecidability results for commutative Kleene algebra
(`commutative-kleene-algebra`, a sibling repo under the same parent
directory as this one) -- but is genuinely general-purpose synthetic
computability content, not specific to that project, and lives here rather
than there for that reason.

This file is not a complete authorship history (see `git log` for that);
it's a pointer for anyone wondering why files like `T_L_Bridge.v` or
`EA_L_Myhill.v` exist, whose purpose isn't otherwise obvious from this
library's own original scope.

## `theories/Models/`

- **`CT.v`**: `T_L`/`θ_L`, a step-indexed interpreter for Rocq's own `L`
  calculus, `CT_L` (Church's Thesis restricted to `L`) and its equivalent
  formulations, and `SMN_for T_L` (an axiom-free S-M-N/currying theorem).
- **`T_L_Extract.v`**: makes `T_L` itself uniformly extractable to `L`
  (needed for it to be usable as a genuine Church's-Thesis witness, not
  just an object studied from outside `L`).
- **`T_L_Uniform.v`**: a single uniform two-argument `L`-term realizing
  `T_L c x` end to end.
- **`EffectiveInseparability_L.v`**: builds `W_L`/`η_L` and the payoff
  `eff_insep_A0_B1_L_via_generic`, instantiating the generic skeleton
  below directly over `T_L`.
- **`EA_L.v`** (added 2026-08-31, moved from `commutative-kleene-algebra`):
  builds a genuine `EA` instance from `CT_L` + `SMN_for T_L`, letting the
  library's existing abstract-`EA` machinery
  (`ReducibilityDegrees/{simple,EffectiveInseparability}.v`) be reused
  directly against `T_L` instead of re-derived from scratch.
- **`EA_L_Myhill.v`** (added 2026-08-31, moved from the same repo, renamed
  from `Myhill.v` to avoid colliding with `Basic/Myhill.v`'s Myhill
  *isomorphism* theorem -- a different classical result): derives
  `creative`/`m-complete` from `eff_insep_shape W_L P B1_L` for an
  arbitrary `P`, given `CT_L` and `MP`.
- **`T_L_Bridge.v`** (added 2026-08-31, moved from the same repo): bridges
  `T_L` to the `mu`-search-shaped `T_L_Uniform.R_TL`, plus a generic
  "`R_TL`/`mu` connection implies effective inseparability" argument
  (`K_of`/`GenericK`) parametrized over an arbitrary target predicate.

## `theories/ReducibilityDegrees/`

- **`EffectiveInseparabilityGeneric.v`**: the shared skeleton factoring out
  the race/diagonal construction common to both the abstract-`EA` and
  `T_L`-specific effective-inseparability arguments, parametrized over an
  abstract numbering and witness function (`Θ_num`, renamed from
  `Θ_ours` 2026-08-31 -- the old name was uninformative).
- **`EffectiveInseparabilityTransport.v`**: the superset-transport lemma
  (`eff_insep_shape_superset`, Kuznetsov's Proposition 9) for the bundled
  `eff_insep_shape` notion.
- **`EffectiveInseparabilityCore.v`** (added 2026-08-31, moved from
  `commutative-kleene-algebra`): the *unbundled* effective-inseparability
  notion (`eff_insep_core`, disjointness plus a witness function, no
  enumerability required) and its own superset-transport lemma
  (`eff_insep_core_superset`) -- genuinely different from, not a duplicate
  of, `EffectiveInseparabilityTransport.v`'s bundled version, since
  `eff_insep_core` itself asks for strictly less than `eff_insep_shape`
  does.

## `theories/Basic/Recursion.v`

Kleene's Uniform Recursion Theorem (`URec_Θ`/`URec_W`), used by
`ReducibilityDegrees/simple.v`'s proof of Myhill's theorem
(`creative_to_m_complete`). Predates the `T_L`-specific work above.
