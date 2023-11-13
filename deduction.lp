require open Logic.Construkti.logic;

// Natural deduction rules

symbol imp_i (p q : Prop) : (Prf p → Prf q) → Prf (p ⇒ q);
symbol imp_e (p q : Prop) : Prf (p ⇒ q) → Prf p → Prf q;
symbol and_i (p q : Prop) : Prf p → Prf q → Prf (p ∧ q);
symbol and_e_l (p q : Prop) : Prf (p ∧ q) → Prf p;
symbol and_e_r (p q : Prop) : Prf (p ∧ q) → Prf q;
symbol or_i_l (p : Prop) : Prf p → Π q : Prop, Prf (p ∨ q);
symbol or_i_r (q : Prop) : Prf q → Π p : Prop, Prf (p ∨ q);
symbol or_e (p q : Prop) : Prf (p ∨ q) → Π r : Prop, (Prf p → Prf r) → (Prf q → Prf r) → Prf r;
symbol neg_i (p : Prop) : (Prf p → Prf ⊥) → Prf (¬ p);
symbol neg_e (p : Prop) : Prf (¬ p) → Prf p → Prf ⊥;
symbol top_i : Prf ⊤;
symbol bot_e : Prf ⊥ → Π p : Prop, Prf p;
symbol fa_i [a : Set] (p : El a → Prop) : (Π x : El a, Prf (p x)) → Prf (∀ (λ x, p x));
symbol fa_e [a : Set] (p : El a → Prop) : Prf (∀ (λ x, p x)) → Π x : El a, Prf (p x);
symbol ex_i [a : Set] (p : El a → Prop) : Π t : El a, Prf (p t) → Prf (∃ (λ x, p x));
symbol ex_e [a : Set] (p : El a → Prop) : Prf (∃ (λ x, p x)) → Π r : Prop, (Π x : El a, Prf (p x) → Prf r) → Prf r;

symbol absurd (p : Prop) : Prf (¬ p ⇒ ⊥) → Prf p; // Classical deduction rule

