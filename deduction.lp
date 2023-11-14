require open Logic.Construkti.logic;

// Implication
symbol imp_i (p q : Prop) : (Prf p → Prf q) → Prf (p ⇒ q);
symbol imp_e (p q : Prop) : Prf (p ⇒ q) → Prf p → Prf q;

// Conjunction
symbol and_i (p q : Prop) : Prf p → Prf q → Prf (p ∧ q);
symbol and_e_l (p q : Prop) : Prf (p ∧ q) → Prf p;
symbol and_e_r (p q : Prop) : Prf (p ∧ q) → Prf q;


// Disjunction
symbol or_i_l (p : Prop) : Prf p → Π q : Prop, Prf (p ∨ q);
symbol or_i_r (q : Prop) : Prf q → Π p : Prop, Prf (p ∨ q);
symbol or_e (p q : Prop) : Prf (p ∨ q) → Π r : Prop, (Prf p → Prf r) → (Prf q → Prf r) → Prf r;

// Negation
symbol neg_i (p : Prop) : (Prf p → Prf ⊥) → Prf (¬ p);
symbol neg_e (p : Prop) : Prf (¬ p) → Prf p → Prf ⊥;

// Tautology and contradiction
symbol top_i : Prf ⊤;
symbol bot_e : Prf ⊥ → Π p : Prop, Prf p;

// Universal quantifier
symbol fa_i [a : Set] (p : El a → Prop) : (Π x : El a, Prf (p x)) → Prf (∀ p);
symbol fa_e [a : Set] (p : El a → Prop) : Prf (∀ p) → Π x : El a, Prf (p x);

// Existential quantifier
symbol ex_i [a : Set] (p : El a → Prop) : Π t : El a, Prf (p t) → Prf (∃ p);
symbol ex_e [a : Set] (p : El a → Prop) : Prf (∃ p) → Π r : Prop, (Π x : El a, Prf (p x) → Prf r) → Prf r;

// Reductio ad absurdum (classical rule)
symbol absurd (p : Prop) : Prf (¬ p ⇒ ⊥) → Prf p;

