section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro hp
  intro hnp
  have negation := hnp hp
  exact negation

theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro hnp
  by_cases hp : P
  case pos =>
    exact hp
  case neg =>
    have boom := hnp hp
    contradiction

theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  apply Iff.intro -- Ataque de uma equivalência === ataque de uma conjunção
  case mp =>
    exact doubleneg_elim P
  case mpr =>
    exact doubleneg_intro P


------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro hporq
  rcases hporq with (hp | hq)
  case inl =>
    right
    exact hp
  case inr =>
    left
    exact hq

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  constructor   -- Ckomando para separar o jogo em dois novos jogos
  case intro.left =>
    exact hq
  case intro.right =>
    exact hp


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro hnporq
  intro hp
  rcases hnporq with (hnp | hq)
  case inl =>
    have boom := hnp hp
    contradiction
  case inr =>
    exact hq

theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro hporq
  intro hnp
  rcases hporq with (hp | hq)
  case inl =>
    have boom := hnp hp
    contradiction
  case inr =>
    exact hq


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro hpq
  intro hnq
  intro hp
  have hq := hpq hp
  have boom := hnq hq
  exact boom

theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro hnqnp
  intro hp
  by_cases hq : Q
  case pos =>
    exact hq
  case neg =>
    have hnp := hnqnp hq
    have boom := hnp hp
    contradiction

theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  apply Iff.intro
  case mp =>
    exact impl_as_contrapositive P Q
  case mpr =>
    exact impl_as_contrapositive_converse P Q


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by
  intro (h1 : ¬ (P ∨ ¬ P))
  have h2 : (P ∨ ¬ P) := by  -- Equivalente ao "Vou demonstrar (P ∨ ¬ P)"
    right
    intro (h2 : P)
    have h3 : (P ∨ ¬ P) := by
      left
      exact h2
    have boom := h1 h3
    contradiction
  have boom := h1 h2
  contradiction


------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro (hpqp : ((P → Q) → P))
  intro (hnp : ¬ P)
  have hpq : (P → Q) := by
    intro (hp : P)
    have boom := hnp hp
    contradiction
  have hp := hpqp hpq
  have boom := hnp hp
  contradiction


------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
  by_cases hnp : P
  case pos =>
    right
    intro hp
    exact hnp
  case neg =>
    left
    intro hp
    have boom := hnp hp
    contradiction



------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro (porq : P ∨ Q)
  intro (npnq : (¬ P ∧ ¬ Q))
  rcases npnq with ⟨(hnp : ¬ P), (hnq : ¬ Q)⟩
  rcases porq with ((hp : P) | (hq : Q))
  case intro.inl =>
    have boom := hnp hp
    contradiction
  case intro.inr =>
    have boom := hnq hq
    contradiction


theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro (pandq : P ∧ Q)
  intro (npornq : ¬ P ∨ ¬ Q)
  rcases pandq with ⟨(hp : P), (hq : Q)⟩
  rcases npornq with ((hnp : ¬ P) | (hnq : ¬ Q))
  case intro.inl =>
    have boom := hnp hp
    contradiction
  case intro.inr =>
    have boom := hnq hq
    contradiction


------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro (nporq : ¬ (P ∨ Q))
  constructor
  case left =>
    intro (hp : P)
    have porq : (P ∨ Q) := by
      left
      exact hp
    have boom := nporq porq
    contradiction
  case right =>
    intro (hq : Q)
    have porq : (P ∨ Q) := by
      right
      exact hq
    have boom := nporq porq
    contradiction


theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro hpq
  intro porq
  rcases hpq with ⟨hnp, hnq⟩
  cases porq
  case inl hp =>
    have boom := hnp hp
    exact boom
  case inr hq =>
    have boom := hnq hq
    exact boom

theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  sorry

theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  sorry

theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  sorry

theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  sorry


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  sorry

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  sorry

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  sorry

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  sorry


------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  sorry

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  sorry


------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  sorry


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  sorry

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  sorry

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  sorry

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  sorry


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  sorry

theorem conj_idem :
  (P ∧ P) ↔ P := by
  sorry


------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  intro boom
  contradiction

theorem true_top :
  P → True  := by
  intro hp
  trivial


end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Type)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  sorry

theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  sorry

theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
