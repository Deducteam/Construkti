// Logic (source: https://github.com/Deducteam/lambdapi-logics/tree/master/U)


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


// Intuitionistic connectives and quantifiers

constant symbol ⇒ : Prop → Prop → Prop; notation ⇒ infix right 10;
rule Prf ($x ⇒ $y) ↪ Prf $x → Prf $y;

constant symbol ∧ : Prop → Prop → Prop; notation ∧ infix right 30;
//rule Prf ($p ∧ $q) ↪ Π r, (Prf $p → Prf $q → Prf r) → Prf r;

constant symbol ∨ : Prop → Prop → Prop; notation ∨ infix right 20;
//rule Prf ($p ∨ $q) ↪ Π r, (Prf $p → Prf r) → (Prf $q → Prf r) → Prf r;

constant symbol ⊤ : Prop;
//rule Prf ⊤ ↪ Π r, Prf r → Prf r;

constant symbol ⊥ : Prop;
//rule Prf ⊥ ↪ Π r, Prf r;

constant symbol ∀ [a : Set] : (El a → Prop) → Prop; notation ∀ quantifier;
rule Prf (∀ $p) ↪ Π x, Prf ($p x);

constant symbol ∃ [a : Set] : (El a → Prop) → Prop; //notation ∃ quantifier;
//rule Prf (∃ $p) ↪ Π r, (Π x, Prf ($p x) → Prf r) → Prf r;

symbol ¬ : Prop → Prop; notation ¬ prefix 40;
rule ¬ $p ↪ $p ⇒ ⊥;

symbol ⇔ : Prop → Prop → Prop; notation ⇔ infix right 5;
rule ($p ⇔ $q) ↪ ($p ⇒ $q) ∧ ($q ⇒ $p);