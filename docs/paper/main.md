---
title: |
    Formalization of Ostrowski theorems \
    in Lean theorem prover
abstract: |
    Ostrowski theorems provide classification of all absolute values in certain fields and lies at the foundations of Berkovich space theory.
    In particular, over $\Q$, all absolute values are either the trivial, the usual or a $p$-adic.
    This statement entirely determines the Berkovich spectrum of integers.

    We formalize Ostrowski theorems in the Lean theorem prover, in two attempts, one aiming to understand the challenges and determining a reachable generalization target.
    The second attempt reaches this target and shows everything the first attempt does in a simpler and cleaner way. Following this road, we identify low-hanging fruits missing the Lean mathematical library and develop a self-contained reusable general theory to formalize Ostrowski theorems in general contexts.
    Our proofs show the discrepancy between how easy it is to use algebra versus how tedious it is to conduct analytical reasoning with inequalities and calculus, and calls for a thorough examination on how to drastically simplify analysis in these contexts.

author:
    - Ryan Lahfa:
       email: ryan.lahfa@ens.fr
       institute: ens_ulm
       correspondence: "yes"
       equal_contributor: "yes"
    - Julien Marquet:
       email: julien.marquet@ens.fr
       institute: ens_ulm
       equal_contributor: "yes"
    - Hadrien Barral:
       email: hadrien.barral@ens.fr
       institute: ens_ulm
institute:
    - ens_ulm: DIENS, École Normale Supérieure, CNRS, PSL University, Paris, France
advanced-cs: true
advanced-maths: true
numbersections: true
biblio-style: alphabetic
bibliography:
- ./Formalization.bib
- ./Berkovich.bib
biblatex: true
biblio-title: References
leanlst: true
---

<!-- TODO:
- relire pour les fautes.
- utiliser les références vers nos objets: les définitions, les contributions, les sections.
- parler un peu plus de certaines preuves & réduire le blablabla à certains endroits en même temps.
- post-submission: fixer les citations pourries par des métadonnées nazes
-->

# Introduction

## Background work

The formalization of mathematics has seen a lot of projects: \cite{wiedijkQEDManifestoRevisited}, [@abelruffinicoq], [@feitthompsoncoq], [@buzzard2020perfectoids], [@lewis2019hensel], [@commelin2021witt], most of them treat of undergraduate mathematics and seldom of research-level mathematics.
In particular, the surrounding mathlib [@The_mathlib_Community_2020] formalization projects are progressing at a fast pace, with Witt vectors [@commelin2021witt], schemes [@buzzard2021schemes], the Liquid Tensor Experiment [@scholze2021liquid].
Yet, formalizing research-level theories remain very difficult, especially when the theory requires non-trivial metaprogrammation and tactics to simplify proof terms.

In [@buzzard2020perfectoids], the definition of perfectoid spaces is formalized entirely and required 33 files and more than 3000 lines of code which should have been in the mathematical library (so-called `for_mathlib` folder), upstreaming back such amount of contributions is also a non-trivial problem [@van_Doorn_2020]. Their formalization also used ad-hoc automation, notably with non-classical objects like algebraic structure "with zero".

In this paper, we will formalize the very start of an alternative theory: Berkovich spaces.
This paper follows those ideas and provides an attempt to open up a formalization of Berkovich's young theory.
To the best of our knowledge, this formalization has never made its way in any proof assistant.

We also show along the way that picking up a research-level theory produces many undergraduate-level theorems the Lean mathematical library lacks and how it can provide for better interfaces for further formalizations.

## Ostrowski theorem and Berkovich spaces

This work will provide an in-depth view on the process of formalizing Ostrowski theorem and its variants.
In this section, we will first re-introduce the mathematical contents.
In section \ref{sec:first_attempt}, we detail our bruteforce attempt to formalizing the basic version of the theorem with minimal tooling.
In section \ref{sec:smart_attempt}, we use lessons learnt from the previous section to generalize our tooling so that the Ostrowski theorem and its variants can be derived while reusing as much as possible the steps and arguments.
In section \ref{sec:conclusion}, we provide our feedback on the process and discuss future work to improve such formalizations and this work.

The core objects of Ostrowski's theorem are **absolute values**:

\begin{definition}[absolute value] \label{def:absolute_value}
    An absolute value on a ring $R$ is a function $\abs{\cdot}: R \to \R$ such that
    \begin{enumerate}
        \item{} $\forall x \in R, \abs{x} = 0 \iff x = 0$
        \item{} $\forall x, y \in R, \abs{xy} = \abs{x} \abs{y}$
        \item{} $\forall x, y \in R, \abs{x + y} \le \abs{x} + \abs{y}$
    \end{enumerate}
\end{definition}

The usual absolute value is an absolute value with respect to Definition \ref{def:absolute_value}.

These objects allow to build a completion of $\Q$ in an algebraically interesting way.
The usual completion of $\Q$ is $\R$, and is obtained with the usual absolute value.
Absolute values retain just the right amount of properties of the usual absolute value to show _both_ analytical and algebraic interest.

In this paper, we focus on the following class of absolute values:

\begin{definition}[$p$-adic absolute value] \label{def:padic_abv}
    With $p \in \N$ prime, we denote $\abs{\cdot}_p$ the $p$-adic absolute value on $\Z$,
    where $\textrm{v}_p(k)$ is the multiplicity of $p$ in $k$:
    \begin{equation*}
        \abs{k}_p = p^{-\textrm{v}_p(k)}
    \end{equation*}
\end{definition}

The superclass of $p$-adic absolute values is the class of the _non-Archimedean absolute value_:

\begin{definition}[non-Archimedean absolute value] \label{def:nonArchimedean}
    An absolute value $\abs{\cdot}$ is called \emph{non-Archimedean} when the following holds:
    \begin{equation*}
        \forall x, y \in R, \abs{x + y} \le \max\left(\abs{x}, \abs{y}\right)
    \end{equation*}
\end{definition}

A natural question is to classify all absolutes values over $\Q$, which are classified _up to equivalence_:

\begin{definition}[equivalence] \label{def:abv_equiv}
    Two absolute values $\abs{\cdot}_1$ and $\abs{\cdot}_2$ on a ring $R$ are said to be \emph{equivalent} when
    for some $\alpha > 0$ we have $\forall x \in R, {\abs{x}_1}^{\alpha} = \abs{x}_2$.

    When this holds, we write $\abs{\cdot}_1 \sim \abs{\cdot}_2$.
\end{definition}

It is noteworthy that equivalent absolute values are topologically equivalent: this turns Ostrowski's theorem into a bridge between algebra and analysis, completely classifying the absolute values on $\Q$.

\begin{theorem}[Ostrowski] \label{target:ostrowski}
    Given $\lambda: \Q \to \Q$ an absolute value over $\Q$, either $\lambda \sim \abs{\cdot}$, either there is some $p \in \PR$ such that $\lambda \sim \abs{\cdot}_p$.
\end{theorem}

Such a theorem shows there is an alternative to the completion of $\Q$ by taking a prime number $p$ and completing using $p$-adic absolute value, giving arise to $\Q_p$, and that these completions are the only alternatives to the usual one.

Ostrowski's theorem plays an interesting role in Berkovich space theory to completely determine the structure of the Berkovich spectrum of integers: $\mathcal{M}(\Z)$, which is the set of all norms over $\Z$ equiped with a certain topology.

Note that Ostrowski theorem has many variants where we can extend it to fields like $\F[X]$ or more complex structures. We will explore in this work how a formalization of multiple variants can be obtained efficiently.

For a more in-depth presentation of Berkovich space theory, refer to [@ducrosBerkovichSpacesApplications2015] or [@temkinIntroductionBerkovichAnalytic2015].

# Naive formalization \label{sec:first_attempt}

To understand the challenges behind Ostrowski theorem being formalized, we attempted a bruteforce formalization over $\Q$ based on [@ruiterOstrowski].

The resulting proof is easily understandable, only basic mathematical tooling was needed as in the original proof: Bézout's identity, simple limits and calculus.

Yet this proof does not fit the standard of formalized mathematics: it is far too long and would greatly benefit from:

- extraction of lemmas, and generalization of most parts,
- automation: most of the proof is calculus and could be automated with the right tactics and systems.

Concretely, the core lemma of this first attempt is around 200 lines long.
It is built mainly with the `obtain` keyword, which is the formal equivalent of saying "let us now show that \ldots".
This construct allows us to stay close to the intuition but led us to longer proofs, like in the toy example that follows.

For instance, one would start the proof of the bounded case by "let us first show that there is some $n \in \N, n > 0$ such that $\abs{n} < 1$" (in this context, $\abs{\cdot}$ is a nontrivial bounded absolute value).
To quickly prove this statement on a piece of paper, we may say that:

- assuming $\forall n \in \N^*, \abs{n} \ge 1$, then $\forall n \in \N^*, \abs{n} = 1$ ($\abs{\cdot}$ is bounded),
- this is absurd because by hypothesis, $\abs{\cdot}$ is nontrivial.

Following this exact scheme, our formalized proof starts with the following :

\begin{lstlisting}
obtain ⟨ n, zero_lt_n, abvn_lt_one ⟩: ∃ n: ℕ, 0 < n ∧ abv n < 1,
{ /- 18 lines omitted -/ }
\end{lstlisting}

<!-- Je m'amuse beaucoup dans ce paragraphe, mais peut-être que c'est un peu trop prendre le lecteur pour Le Frérot™.
     Mais ça peut aussi être sympa d'avoir un petit commentaire informel comme ça au milieu d'un papier,
     donc qu'est-ce que j'en fais ? -->

Suddenly, a two line "human" proof came out as a 18 lines long formalized version.
In fact, what we really did when we proved this property in two sentences was:

- proceed by _reducio ad absurdum_,
- realize that $\abs{\cdot}$ is equal to $1$ everywhere on $\N$,
- prove it by bounding the values of $\abs{\cdot}$ using the suitable hypotheses,
- realize that this is actually enough to prove that $\abs{\cdot}$ is trivial,
- show the contradiction by recalling our hypothesis : $\abs{\cdot}$ is nontrivial.

<!-- Surtout cette phrase où je me donne vraiment... -->
Formalizing our two-liner required getting into punctilious details, and even further formal considerations when detailing the very informal "realize that \ldots". Our readers can easily imagine how a handful of calculations became a 200 lines formal proof for the core lemma.

# Pursuing a general enough point of view \label{sec:smart_attempt}

Naturally, the previous proof lacked of generality and contained too much irrelevant detail which translated into bothersome ad-hoc statements, so we adopted two objectives from this experience:

- as much as possible, make Ostrowski theorem a natural consequence from the general theory and allow for interesting generalizations, e.g. Ostrowski over $\F[X]$,
- see how to fit parts of this general theory in the Lean mathematical library, so it can benefit other users.

Our intuition is a synthetic point of view is more suitable for formalization than an analytic approach.
Therefore, we went looking for the adequate algebraic theories to support our goals.

We take inspiration from [@artinAlgebraicNumbersAlgebraic2005] presentation of Ostrowski theorem and transform the approach in a suitable way for formalization.

## Core of the theory {#section:core_theory}

For this presentation, we will use $R$ a principal ideal domain (PID).

The core idea is to keep an algebraic point of view and develop some tools to characterize the behavior of bounded absolute values on general rings (Definition \ref{def:our_boundness}).

\begin{definition} \label{def:our_boundness}
    Given $\abs{\cdot}: R \to \R$ an absolute value, $\abs{\cdot}$ is said bounded when:
    \begin{equation*}
        \forall x \in R, \abs{x} \leq 1
    \end{equation*}
\end{definition}

Note that this is equivalent to the usual definition of boundedness (existence of some upper bound):

- if $\abs{\cdot}$ is bounded, then $1$ is an upper bound,
- otherwise there is some $x$ such that $\abs{x} > 1$, then $\abs{x^n} \xrightarrow[n \to +\infty]{} +\infty$ and $\abs{\cdot}$ has no finite upper bound.

Furthermore, we define the _trivial absolute value_ as the function that maps $0$ to $0$ and any other element to $1$.

We will need one extra lemma for the core theorem, stating that an absolute value is bounded over $\N$ if and only if it is non-Archimedean:

\begin{lstlisting}[label={contrib:nonArchimedean_iff_integers_bounded}]
theorem nonArchimedean_iff_integers_bounded
  {α} [comm_ring α] [nontrivial α] (abv: α → ℝ) [is_absolute_value abv]:
  (∃ C: ℝ, 0 < C ∧ ∀ n: ℕ, abv n ≤ C) ↔ (∀ a b: α, abv (a + b) ≤ max (abv a) (abv b))
\end{lstlisting}

Proving this lemma revealed to be challenging: on the paper, it takes at most a dozen of lines, but the formalization took around 200 lines.
The reasons are the same as in section \ref{sec:first_attempt}.
We have isolated a corner of the theory where calculus cannot be avoided, like we moved the problem that lied in section \ref{sec:first_attempt} from one place to another.
As future work, these lines would greatly benefit from new calculus tactics.

The main theorem is `abv_bounded_padic`, which states that a non-trivial bounded absolute value
on a principal ideal domain $R$ is a $p$-adic absolute value for some prime $p$ of $R$.
\begin{lstlisting}[label={contrib:abv_bounded_padic}]
theorem abv_bounded_padic {α} [integral_domain α] [is_principal_ideal_ring α]
    [normalization_monoid α]
    (abv: α → ℝ) [is_absolute_value abv]
    (bounded: ∀ a: α, abv a ≤ 1)
    (nontrivial: ∃ a: α, a ≠ 0 ∧ abv a ≠ 1):
      ∃ (p: α) (p_prime: prime p), abvs_equiv abv (sample_padic_abv p p_prime)
\end{lstlisting}

The typeclasses \lstinline{[integral_domain α]} and \lstinline{[is_principal_ideal_ring α]} ensure that $\alpha$ is a principal integral domain (PID).

\lstinline{[normalization_monoid α]} means that the elements of $\alpha$ admit a normal form (say, in $\Z$, the positive integers, and in $\K[X]$, the monics).
This is required by some of the lemmas we use, but can be omitted for the scope of this paper.

`abvs_equiv` is the relation of equivalence between absolute values.

`sample_padic_abv p p_prime` is an $p$-adic absolute value (`p_prime` is a proof that $p$ is indeed prime).

Keeping in mind that according to \lstinline{nonArchimedian_iff_integers_bounded}, $\abs{\cdot}$ is non-Archimedian, the strategy to prove the core lemma (`abv_bounded_padic`) is as follows:

- Take $\{ x \in R \mid \abs{x} < 1 \}$, this is a prime ideal of $R$;
- As $R$ is a PID, there is some prime $p \in R$ that generates the previous set;
- Now, it is sufficient to prove the equivalence between $\abs{\cdot}$ and $\abs{\cdot}_p$ to finish;
- By the primes extensionality lemma (see \ref{section:a_lemma}), it suffices to prove there is some $\alpha > 0$ such that for all prime $q \in R$, $\abs{q}^{\alpha} = \abs{q}_p$;
- To clear this goal, a case analysis on whether $p$ and $q$ are associated is enough and helps to find the suitable $\alpha$ in terms of logarithms of absolute values of $p$.

The core lemma is easy to prove as it is the result of composable and reusable lemmas and proves our point regarding the need of finding general enough abstractions so that the proofs tend towards an assembling game.

<!-- mef -->
\nopagebreak[4]

## A lemma {#section:a_lemma}

We also encountered a very useful extensionality lemma for morphisms over monoids with zero, of which we give the Lean definition:
\begin{lstlisting}[label={contrib:ext_hom_primes}]
theorem ext_hom_primes {α} [comm_monoid_with_zero α] [wf_dvd_monoid α]
  {β} [monoid_with_zero β]
  (φ₁ φ₂: monoid_with_zero_hom α β)
  (h_units: ∀ u: units α, φ₁ u = φ₂ u)
  (h_irreducibles: ∀ a: α, irreducible a → φ₁ a = φ₂ a):
    φ₁ = φ₂
\end{lstlisting}

\lstinline{[monoid_with_zero β]} states that $\beta$ is a monoid that contains a "zero", _i.e._ an absorbing element.
These objects may seem peculiar to a mathematician, but are useful in the context of formalized mathematics.
We will not discuss the use of "monoids with zero", as they are outside of the scope of this article. <!-- une référence vers les monoides à zéro -->

\lstinline{[comm_monoid_with_zero α]} further states that $\alpha$ is commutative.

\lstinline{φ : monoid_with_zero_hom α β} states that $\varphi$ is a homomorphism of monoid with zero with source $\alpha$ and target $\beta$.

\lstinline{[wf_dvd_monoid α]} states that the division on $\alpha$ is a well-founded order. This is key to the lemma:
we only need to proceed by induction. This makes this lemma apply well to principal ideal domains, because
the division in such rings the inclusion is well-founded.

Mathematically, this lemma states that if

- $R$ is a principal ideal domain
- Two multiplicative functions agree on the units of $R$ and on its primes

Then, they coincide everywhere.

This nontrivial lemma may be useful to anyone working with multiplicative functions and was added to mathlib [@The_mathlib_Community_2020].
We therefore fulfilled one of our two goals: formalizing mathematics which may be useful to future users.

We brought the problem into statements about multiplicative functions, but have yet to lift our original statement which has a valuation flavor in these terms.
Note that valuations and multiplicative functions (actually, homomorphisms) are unfortunately very different objects in Lean: the former are just functions that are refined using a typeclass, while the latter are _structures_ (in a nutshell, tuples containing objects and proofs).
This implies that switching from the valuation point of view to homomorphisms and back is cumbersome.
To solve this problem, we had to write some boilerplate to bridge this gap.
As future work, it might be possible to automate the process of switching of point of view on this kind of objects, certainly through meta-programming [@commelin2021witt].

## Application: Ostrowski on $\mathbb{Q}$

Once the core lemmas are laid out, Ostrowski's theorem on $\Z$ is almost immediate. Now, obtaining it over $\Q$ requires the extension of absolute values to the entire field.
In theory, it is also almost immediate because of the multiplicative property of absolute values.

In practice, some manual work remained to lift results from $\Z$ to $\Q$, yet, this is not a failure of the previous goal to pursue a general enough theory but rather what we would believe to be a lack of automation in the proof assistant which could be alleviated by meta-programming. That being said, we did not pursue this venture and test our hypothesis and will discuss it later.

## Application: Ostrowski on $\mathbb{F}[X]$

We proved a statement that is slightly less powerful in spirit, in that it does not actually
cover _all_ the possible absolute values, but only the absolute values that are trivial on $\mathbb{F}$.

\begin{theorem}[Ostrowski variant] \label{contrib:ostrowski_variant}
    Given $\abs{\cdot}$ an absolute value on $\F[X]$, trivial on $\F$.
    Exactly one of the following is true:

    \begin{itemize}
    \item $\abs{\cdot}$ is bounded and for some prime $p \in \F[X]$, $\abs{\cdot} = \abs{\cdot}_p$.
    \item $\abs{\cdot}$ is equivalent to the degree.
    \end{itemize}
\end{theorem}

Comforting our intuition, both cases were straightforward reusing the tools in section \ref{section:core_theory}.

# Conclusion \label{sec:conclusion}

<!-- mef -->
\vspace*{-0.2em}

## Results

We wanted to examine the difficulties of formalizing Ostrowski's theorem which constitutes the first step towards Berkovich space theory formalization.

With a bruteforce method, we encountered many tedious computations of analytical nature which led us to hide all the complexity inside algebra which was easier to handle in the proof assistant. The second part presents an approach which worked effectively and gave us with fewer efforts more theorems and provided us with insights on how to pursue the generalization.

Nevertheless, this suggests that calculus and analysis might benefit from a local framework which might help with their manipulation, non-standard analysis seems a promising avenue already explored in Isabelle/HOL with [@fleuriot2000mechanization], but also, the Lean theorem prover in its version 4 might help with its treatment of coercions and performance improvements [@Lean4_2021].

<!-- mef -->
\vspace*{-0.2em}

## Outlook

We notice formalization is not only a process that helps you verify a proof but also to understand and provide insights on results surrounding a theory and sustain the improvements on the system being used beyond classical computer science aspects like performance or user experience.

In particular, we identified pain points using the Lean theorem prover which constitutes interesting future works, namely automation to:

- combine analysis and inequalities/equalities reasoning, e.g. taking limits on a side or both sides,
- bridge points of view or even theories, _e.g._ the former discussion on valuations and homomorphisms.

Despite these bothersome points, we found that adopting a synthetic approach alleviates us from most of the hardships that we encountered with an analytic approach.

<!--
Also, on the mathematical content, we are led to think these results might not be general enough and to the best of our knowledge, literature did not provide with precise statements of which general forms of Ostrowski theorems exist.
-->

Finally, now that Ostrowski theorems are formalized, it is possible to produce the basic objects of Berkovich space theory, notably the Berkovich spectrum and give a non-trivial example: $\mathcal{M}(\Z)$.

<!-- mef -->
\vspace*{-0.5em}
