require open Logic.Construkti.properties;
require open Logic.Construkti.kuroda;
require open Logic.Construkti.logic;
require open Logic.Construkti.deduction;
require open Logic.Construkti.library_c.equality;


// Peano arithmetic 

constant symbol nat : Set;
constant symbol 0 : El nat;
constant symbol S : El nat → El nat;
constant symbol + : El nat → El nat → El nat; notation + infix left 45;
constant symbol * : El nat → El nat → El nat; notation * infix left 50;

symbol peano1 : Prf ¬ ¬ (`∀_c x, ¬ (S x = 0));

symbol peano2 : Prf ¬ ¬ (`∀_c x, `∀_c y, (S x = S y) ⇒ (x = y));

symbol peano3 : Prf ¬ ¬ (`∀_c x, x + 0 = 0);

symbol peano4 : Prf ¬ ¬ (`∀_c x, `∀_c y, x + S y = S (x + y));

symbol peano5 : Prf ¬ ¬ (`∀_c x, x * 0 = 0);

symbol peano6 : Prf ¬ ¬ (`∀_c x, `∀_c y, x * S y = x * y + x);

symbol induction_axiom : Prf ¬ ¬ (`∀_c P, (P 0 ∧ (`∀_c n, P n ⇒ P (S n))) ⇒ `∀_c n, P n);


// Some result

opaque symbol addZleft : Prf ¬ ¬ (`∀_c x, 0 + x = x) ≔
begin
    refine imp_e_c ((0 + 0 = 0) ∧ (`∀_c n, (0 + n = n) ⇒ (0 + S n = S n))) (`∀_c x, 0 + x = x) _ _ 
    {refine fa_e_c (λ P, (P 0 ∧ (`∀_c n, P n ⇒ P (S n))) ⇒ `∀_c n, P n) induction_axiom (λ x, 0 + x = x)}
    {refine and_i_c ((0 + 0) = 0) (`∀_c n, ((0 + n) = n) ⇒ ((0 + S n) = S n)) _ _ 
    {refine fa_e_c (λ x, x + 0 = 0) peano3 0}
    {refine fa_i_c (λ n, ((0 + n) = n) ⇒ ((0 + S n) = S n)) _;
    assume n;
    refine imp_i_c ((0 + n) = n) ((0 + S n) = S n) _;
    assume H;
    refine imp_e_c ((0 + S n = S (0 + n)) ∧ (S (0 + n) = S n)) ((0 + S n) = S n) _ _ 
    {refine fa_e_c (λ z, ((0 + S n = S (0 + n)) ∧ (S (0 + n) = z)) ⇒ (0 + S n = z)) _ (S n);
    refine fa_e_c (λ y, `∀_c z, ((0 + S n = y) ∧ y = z) ⇒ (0 + S n = z)) _ (S (0 + n));
    refine fa_e_c (λ x, `∀_c y, `∀_c z, ((x = y) ∧ (y = z)) ⇒ (x = z)) _ (0 + S n);
    refine eq_trans nat}
    {refine and_i_c (0 + S n = S (0 + n)) (S (0 + n) = S n) _ _
    {refine fa_e_c (λ y, 0 + S y = S (0 + y)) _ n;
    refine fa_e_c (λ x, `∀_c y, (x + S y) = S (x + y)) _ 0;
    refine peano4}
    {refine imp_e_c ((0 + n) = n) (S (0 + n) = S n) _ _ 
    {refine fa_e_c (λ y, ((0 + n = y) ⇒ (S (0 + n) = S y))) _ n;
    refine fa_e_c (λ x, `∀_c y, ((x = y) ⇒ (S x = S y))) _ (0 + n);
    refine fa_e_c (λ f, `∀_c x, `∀_c y, ((x = y) ⇒ (f x = f y))) _ S;
    refine eq_f nat nat}
    {refine H}}}}}
end;