// Base of the encoding

constant symbol Prop : TYPE;
symbol Prf : Prop → TYPE;
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

symbol ¬ : Prop → Prop; notation ¬ prefix 40;