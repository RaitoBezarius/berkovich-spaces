
# First approach

Our first approach was to exacly formalize [1], which gives
a direct proof of Ostrowski's theorem on $\mathbb{Q}$.
The proof that is given there is easily understandable, as it only
uses basic mathematical tools : Bézout's identity, simple limits, and
basic calculus.

Yet we found it cumbersome to formalize : translating simple calculations
in a formal language is nontrivial, and may yield long and technical proofs.
The code for the bounded case took around 300 lines, and only contained ad-hoc
statements that could only be useful for our proof.

Althought our initial goal, namely formalizing Ostrowski's theorem, was achieved,
we found that our proof wasn't entierely satisfactory. The problem was that
the proof we gave lacked _generality_.

# Generalization

We went looking for another more general approache that would

 * Make Ostrowski's theorem ``fall on its own'' from the general theory and
   allow for generalizations (_e.g._ Ostrowski on $\mathbb{F}(X)$
 * Use some general theory that would be relevant for Mathlib, that would
   benefit other users

In other words, we wanted to both simplify our proof and provide Mathlib
more pieces of theory.

## Second approach

When $|\cdot|$ is an absolute value on $R$, we say that $|\cdot|$ is _bounded_
when $\forall x \in R, |x| \le 1$.

We went from an algebraic point of view and developped some theory that
characterized the behavior of bounded absolute values on general rings.

The main theorem is `abv_bounded_padic`, which states that a bounded absolute value
on a principal ideal domain $R$ is a $p$-adic absolute value for some prime $p$ of $R$.
```lean
theorem abv_bounded_padic {α} [integral_domain α] [is_principal_ideal_ring α]
    [normalization_monoid α]
    (abv: α → ℝ) [is_absolute_value abv]
    (bounded: ∀ a: α, abv a ≤ 1)
    (nontrivial: ∃ a: α, a ≠ 0 ∧ abv a ≠ 1):
      ∃ (p: α) (p_prime: prime p), abvs_equiv abv (sample_padic_abv p p_prime) :=
```

We also use the following lemma :
```lean
theorem ext_hom_primes {α} [comm_monoid_with_zero α] [wf_dvd_monoid α]
  {β} [monoid_with_zero β]
  (φ₁ φ₂: monoid_with_zero_hom α β)
  (h_units: ∀ u: units α, φ₁ u = φ₂ u)
  (h_irreducibles: ∀ a: α, irreducible a → φ₁ a = φ₂ a):
    φ₁ = φ
```
which states that if $R$ is a principal ideal domain, if two multiplicative functions
agree on the units of $R$ and on it's primes, then they agree everywhere.

The scheme of the proof is as follows :

 * Let $|\cdot|$ be a bounded absolute value on $R$.
 * As $|\cdot|$ is bounded, the set $\{x \in R | |x| < 1 \}$ is a prime ideal of $R$
   (this fact lies in another lemma).
 * $R$ is a principal ideal domain, therefore there is some prime $p \in R$ that
   generates $\{x \in R | |x| < 1 \}$ (another lemma states that an ideal is prime
   iff it admits a prime generator).
 * It suffices to show that $|\cdot|$ and $|\cdot|_p$ are equivalent
 * It is sufficient, using `ext_hom_primes`, to show that tere is some $\alpha > 0$
   such that for all prime $q \in R$, $|q|^\alpha = |q|_p$.
 * This is easy to show, because when $q$ is prime :
    * If $p$ and $q$ aren't associated, then $|q|_p = 1$;
    * If $p$ and $q$ are associated, we denote $q = p * u$ where $u$ is invertible,
      and we get $|q| = |p| * |u| = |p|$.
   Then we find that $\alpha = \mathrm{ln}(|p|_p) / \mathrm{ln}(|p|)$ is suitable, which
   ends the proof.

Once the rights lemmas are provided, the proof is only about assembling the pieces together.
This show that we fulfilled our goal of providing the rights abstractions so that the
proof would ``fall on its own''.

The only difficulty that is left is that the proof requires switching views from
_valuations_ to _multiplicative functions_. The problem lies in the fact that these
two objects are _not_ the same in Lean. We had to write code to manually bridge the
two worlds. It would be interesting, in some future work, to find a way to
automatize this process.

## Ostrowski on $\mathbb{Q}$

With the tools that we developped in this second approach, it was easy to get Ostrowski's
theorem on $\mathbb{Z}$. To prove the theorem on $\mathbb{Q}$, we only needed to extend the
absolute values to all of the field. This is in theory fairly easy because of the multiplicativity
of absolute values.

In practice, we found that there remained a lot of work to do by hand to actually lift the
result from $\mathbb{Z}$ to $\mathbb{Q}$. Yet we do not consider this as a failure of
our first goal (to make the theorem an easy corollary of some general theory) because
it seems like what we have done by hand could be automated. We didn't take the time to
test this hypothesis and leave it as future work.

## Ostrowski on $\mathbb{F}(X)$

We proved a theorem that is slightly les powerful that Ostrowski, in that it does not actually
cover _all_ the possible absolute values, but only the absolute values that are trivial on $\mathbb{F}$.

Given $|\cdot|$ an absolute value on $\mathbb{K}(X)$ that is trivial on $\mathbb{K}$, we prove the following :

 * If $|\cdot|$ is bounded, then it is a $p$-adic absolute value for some prime $p \in \mathbb{K}(X)$.
 * Otherwise, it is equivalent to the degree.

Both cases were fairly easy to formalize given the tools that we already developped, which
again comforts our view that we succeeded in giving a general theory that greatly simplifies
the proofs.

We only needed one extra lemma :
```lean
theorem nonarchimedian_iff_integers_bounded
  {α} [comm_ring α] [nontrivial α] (abv: α → ℝ) [is_absolute_value abv]:
  (∃ C: ℝ, 0 < C ∧ ∀ n: ℕ, abv n ≤ C) ↔ (∀ a b: α, abv (a + b) ≤ max (abv a) (abv b)
```
This states that an absolute value is bounded on all integers ($0$, $1$, $\ldots$,
not _algebraic_ integers) iff it is nonarchimedian.

The proofs of this lemma is very calculatory. It takes at most a dozen of lines on the paper
but it took us arount 200 lines to formalize. We believe there is an interesing development
to make on how to simplify such calculatory proofs, but we leave it as future work.

# Conclusion

Our first naive approach was very calculatory and led us into writing proofs that were
too long and unsatisfactory. Once we switched to an algebraic point of view, the
proofs became smaller, cleaner and easier to write.

We noticed that wherever calculus and analysis came, we encountered problems due to
the length of the proofs that it made us write. This suggests that there is some
interesting work to do on how to make analysis easier to work with in proof assistants.

# Notes to ourselves

Is it relevant to detail all of the proof ?

analytic vs algebraic pov

ref to wf_dvd_monoid.well_founded_dvd_not_unit

