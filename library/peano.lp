require open Construkti.logic;
require open Construkti.library.equality;


// Peano arithmetic 

constant symbol nat : Set;
constant symbol 0 : El nat;
constant symbol S : El nat → El nat;
constant symbol + : El nat → El nat → El nat; notation + infix left 45;
constant symbol * : El nat → El nat → El nat; notation * infix left 50;

symbol peano1 : Prf (`∀ x, ¬ (S x = 0));

symbol peano2 : Prf (`∀ x, `∀ y, (S x = S y) ⇒ (x = y));

symbol peano3 : Prf (`∀ x, x + 0 = 0);

symbol peano4 : Prf (`∀ x, `∀ y, x + S y = S (x + y));

symbol peano5 : Prf (`∀ x, x * 0 = 0);

symbol peano6 : Prf (`∀ x, `∀ y, x * S y = x * y + x);

symbol induction_axiom : Prf (`∀ P, (P 0 ∧ (`∀ n, P n ⇒ P (S n))) ⇒ `∀ n, P n);


// Some result

opaque symbol addZleft : Prf (`∀ x, 0 + x = x) ≔
begin
    refine imp_e ((0 + 0 = 0) ∧ (`∀ n, (0 + n = n) ⇒ (0 + S n = S n))) (`∀ x, 0 + x = x) _ _ 
    {refine all_e (λ P, (P 0 ∧ (`∀ n, P n ⇒ P (S n))) ⇒ `∀ n, P n) induction_axiom (λ x, 0 + x = x)}
    {refine and_i ((0 + 0) = 0) (`∀ n, ((0 + n) = n) ⇒ ((0 + S n) = S n)) _ _ 
    {refine all_e (λ x, x + 0 = 0) peano3 0}
    {refine all_i (λ n, ((0 + n) = n) ⇒ ((0 + S n) = S n)) _;
    assume n;
    refine imp_i ((0 + n) = n) ((0 + S n) = S n) _;
    assume H;
    refine imp_e ((0 + S n = S (0 + n)) ∧ (S (0 + n) = S n)) ((0 + S n) = S n) _ _ 
    {refine all_e (λ z, ((0 + S n = S (0 + n)) ∧ (S (0 + n) = z)) ⇒ (0 + S n = z)) _ (S n);
    refine all_e (λ y, `∀ z, ((0 + S n = y) ∧ y = z) ⇒ (0 + S n = z)) _ (S (0 + n));
    refine all_e (λ x, `∀ y, `∀ z, ((x = y) ∧ (y = z)) ⇒ (x = z)) _ (0 + S n);
    refine eq_trans nat}
    {refine and_i (0 + S n = S (0 + n)) (S (0 + n) = S n) _ _
    {refine all_e (λ y, 0 + S y = S (0 + y)) _ n;
    refine all_e (λ x, `∀ y, (x + S y) = S (x + y)) _ 0;
    refine peano4}
    {refine imp_e ((0 + n) = n) (S (0 + n) = S n) _ _ 
    {refine all_e (λ y, ((0 + n = y) ⇒ (S (0 + n) = S y))) _ n;
    refine all_e (λ x, `∀ y, ((x = y) ⇒ (S x = S y))) _ (0 + n);
    refine all_e (λ f, `∀ x, `∀ y, ((x = y) ⇒ (f x = f y))) _ S;
    refine eq_f nat nat}
    {refine H}}}}}
end;
