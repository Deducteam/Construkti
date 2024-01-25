// Base of the encoding

constant symbol Prop : TYPE;
injective symbol Prf : Prop → TYPE;
constant symbol Set : TYPE;
injective symbol El : Set → TYPE;


// Higher order

constant symbol o : Set;
rule El o ↪ Prop;
constant symbol ⤳ : Set → Set → Set; notation ⤳ infix right 10;
rule El ($x ⤳ $y) ↪ El $x → El $y;


// Connectives and quantifiers

constant symbol ⇒ : Prop → Prop → Prop; notation ⇒ infix right 10;
constant symbol ∧ : Prop → Prop → Prop; notation ∧ infix right 30;
constant symbol ∨ : Prop → Prop → Prop; notation ∨ infix right 20;
constant symbol ⊤ : Prop;
constant symbol ⊥ : Prop;
constant symbol ∀ [a : Set] : (El a → Prop) → Prop; notation ∀ quantifier;
constant symbol ∃ [a : Set] : (El a → Prop) → Prop; notation ∃ quantifier;
constant symbol ¬ : Prop → Prop; notation ¬ prefix 40;
symbol ⇔ p q ≔ (p ⇒ q) ∧ (q ⇒ p); notation ⇔ infix right 5;


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

symbol all_i [a : Set] (p : El a → Prop) : (Π x : El a, Prf (p x)) → Prf (∀ p);
symbol all_e [a : Set] (p : El a → Prop) : Prf (∀ p) → Π x : El a, Prf (p x);

symbol ex_i [a : Set] (p : El a → Prop) : Π t : El a, Prf (p t) → Prf (∃ p);
symbol ex_e [a : Set] (p : El a → Prop) : Prf (∃ p) → Π r : Prop, (Π x : El a, Prf (p x) → Prf r) → Prf r;

symbol excluded_middle : Π p : Prop, Prf (p ∨ ¬ p);