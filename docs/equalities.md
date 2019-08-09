# Equalities in Iris

Using Iris involves dealing with a few subtly different equivalence and equality
relations, especially among propositions.
This document summarizes these relations and the subtle distinctions among them.
This is not a general introduction to Iris: instead, we discuss the different
Iris equalities and the interface to their Coq implementation. In particular, we
discuss:
- Equality from Iris metatheory vs Coq equality and setoid equivalence;
- N-equivalence on OFEs;
- Iris internal equality;
- Iris entailment and bi-entailment.

## Leibniz equality and setoids

First off, in the metalogic (Coq) we have both the usual propositional (or
Leibniz) equality `=`, and setoid equality `equiv` / `≡` (defined in `stdpp`).
Notations for metalogic connectives like `≡` are declared in Coq scope
`stdpp_scope`, which is "open" by default.

Setoid equality for a type `A` is defined by the instance of `Equiv A`; this
allows defining quotient setoids. To deal with setoids, we use Coq's
[generalized
rewriting](https://coq.inria.fr/refman/addendum/generalized-rewriting.html)
facilities.

Setoid equality can coincide with Leibniz equality:
- `equivL` defines a setoid equality coinciding with Leibniz equality.
- Some types enjoy `LeibnizEquiv`, which makes `equiv` be equivalent to `eq`.

Given setoids `A` and `B` and a function `f : A → B`, an instance `Proper ((≡)
==> (≡)) f` declares that `f` respects setoid equality, as usual in Coq. Such
instances enable rewriting with setoid equalities.

Here, stdpp adds the following facilities:
- `solve_proper` for automating proofs of `Proper` instances.
- `f_equiv` generalizes `f_equal` to other relations; it will for instance turn
  goal `R (f a) (f b)` into `R a b` given an appropriate `Proper` instance
  (here, `Proper (R ==> R) f`).

## Equivalences on OFEs

On paper, OFEs involve two relations, equality "=" and distance "=_n". In Coq,
equality "=" is formalized as setoid equality, written `≡` or `equiv`, as before;
distance "=_n" is formalized as relation `dist n`, also written `≡{n}≡`.
Tactics `solve_proper` and `f_equiv` also support distance.

Some OFE constructors choose interesting equalities.
- `discreteO` constructs discrete OFEs (where distance coincides with setoid equality).
- `leibnizO` constructs discrete OFEs (like `discreteO`) but using `equivL`, so
  that both distance and setoid equality coincide with Leibniz equality.

Given OFEs `A` and `B`, non-expansive functions from `A` to `B` are functions
`f : A → B` with a proof of `NonExpansive f` (that is, `(∀ n, Proper (dist n
==> dist n) f)`). The two can be packaged together via `A -n> B`.

Non-expansive functions from Leibniz OFEs can be given type `A -d> B` instead of
`leibnizO A -n> B`; this spares the need for bundled `NonExpansive` instances.
Moreover, `discreteO A -n> B` is isomorphic to `f : A -d> B` plus an instance
for `∀ n, Proper ((≡) ==> (≡{ n }≡)) f`. However, in the second case the
`Proper` instance can be omitted for proof convenience unless actively used.

In both OFE function spaces (`A -n> B` and `A -d> B`), setoid equality is
defined to be pointwise equality, so that functional extensionality holds for `≡`.

## Inside the Iris logic

Next, we introduce notions internal to the Iris logic. Such notions often
overload symbols used for external notions; however, those overloaded notations
are declared in scope `bi_scope`; when writing `(P)%I`, notations in `P` are
resolved in `bi_scope` in preference over `stdpp_scope`.
We also use `bi_scope` for the arguments of all variants of Iris entailments.

The Iris logic has an internal concept of equality. If `a` and `b` are Iris
terms of type `A`, then their internal equality is written (on paper) "a =_A b";
in Coq, that's written `a ≡ b` (notation for `sbi_internal_eq` in scope `bi_scope`).

As shown in the Iris appendix, an internal equality `a ≡ b` is interpreted using
OFE distance. Many types have `_equivI` lemmas characterizing internal
equality on them. For instance, if `f, g : A -d> B`, lemma
`discrete_fun_equivI` shows that `f ≡ g` is equivalent to `∀ x, f x ≡ g x`.
Typically, each `_equivI` lemma for type `T` lifts to internal equality on
`T` properties of the distance on `T`.

## Relations among Iris propositions

In this section, we discuss relations among internal propositions.
Even though some of these notes generalize to all internal logics (other
`sbi`s), we focus on Iris propositions (`iProp Σ`), to discuss both their proof
theory and their model.
As Iris propositions form a separation logic, we assume some familiarity with
separation logics, connectives such as `-∗`, `∗`, `emp` and `→`, and the idea
that propositions in separation logics are interpreted with predicates over
resources (see for instance Sec. 2.1 of the MoSEL paper).

In the metalogic, Iris defines the entailment relation between uniform
predicates: intuitively, `P` entails `Q` (written `P ⊢ Q`) means that `P` implies
`Q` on _every_ resource (for details see Iris appendix [Sec. 6]).
Entailment `P ⊢ Q` is distinct from the magic wand, `(P -∗ Q)%I`, but
equivalent, as `P ⊢ Q` is equivalent to `emp ⊢ P -∗ Q` (per Iris lemmas
`entails_wand` and `wand_entails`).
Notation `P ⊢ Q` is declared in `stdpp_scope`, but takes arguments in
`bi_scope`, so that we can write conveniently `P ⊢ Q -∗ R` in `stdpp_scope`.
For additional convenience, `P ⊢ Q` can also be written `P -∗ Q` in
`stdpp_scope`, so that we can write `P -∗ Q -∗ R` instead of `P ⊢ Q -∗ R` or of
the equivalent `emp ⊢ P -∗ Q -∗ R`.
Using entailment, Iris defines an implicit coercion `bi_emp_valid`, mapping any
Iris propositions `P` into the Coq propositions `emp ⊢ P`.

On paper, uniform predicates are defined by quotienting by an equivalence
relation ([Iris appendix, Sec. 3.3]); that relation is used in Coq as setoid
equivalence. That relation is also equivalent to bi-entailment (or entailment in
both directions), per lemma `equiv_spec`:
```coq
Lemma equiv_spec P Q : P ≡ Q ↔ (P ⊢ Q) ∧ (Q ⊢ P).
```

Hence, setoid equality `≡` on propositions is also written `⊣⊢`. For instance,
our earlier lemma `discrete_fun_equivI` is stated using `⊣⊢`:

```coq
Lemma discrete_fun_equivI {A} {B : A → ofeT} (f g : discrete_fun B) :
  f ≡ g ⊣⊢ ∀ x, f x ≡ g x.
```

Inside the logic, we can use internal equality `≡` (in `bi_scope`), which
translates to distance as usual. Here is a pitfall: internal equality `≡` is in
general strictly stronger than `∗-∗`, because `Q1 ≡ Q2` means that `Q1` and `Q2`
are equivalent _independently of the available resources_.
- When proving `P -∗ Q1 ∗-∗ Q2`, we can use `P` to show that `Q1` and `Q2` are
  equivalent.
- Instead, to prove `P -∗ Q1 ≡ Q2`, we cannot use `P` unless it's a plain
  proposition (so, one that holds on the empty resource). Crucially, pure
  propositions `⌜ φ ⌝` are plain.

We can explain internal equality using the Iris plainly modality:
```coq
Lemma prop_ext P Q : P ≡ Q ⊣⊢ ■ (P ∗-∗ Q).
```
Looking at the Iris semantics for the plainly modality, to prove internal equality
`P ≡ Q`, we must prove that `P` and `Q` are equivalent _without any resources
available_.

Last, metalevel propositions `φ : Prop` can be embedded as pure Iris
propositions `⌜ φ ⌝`, and this allows embedding equalities from the metalogic.
For instance, `⌜ a1 = a2 ⌝` can be useful for making some proofs more
convenient, as Leibniz equality is the strongest equivalence available, is
respected by all Coq functions, and can be used for rewriting in the absence of
`Proper` instances. On the other hand, on-paper Iris does not allow writing
`⌜ a1 = a2 ⌝`, only `⌜ a1 ≡ a2 ⌝`, unless setoid equality and Leibniz equality
coincide.
