require open Logic.Construkti.logic;
require open Logic.Construkti.deduction;


// Polymorphic equality 


constant symbol = [a] : El a → El a → Prop;
notation = infix 4;
rule Prf (@= $a $x $y) ↪ Π (P : El $a → Prop), Prf (P $x) → Prf (P $y);

opaque symbol eq_refl : Π (a : Set), Prf (`∀ x : El a, x = x) ≔
begin
    assume a;
    refine fa_i (λ x : El a, x = x) _;
    assume x;
    assume P Py;
    refine Py
end;

opaque symbol eq_sym : Π (a : Set), Prf (`∀ x : El a, `∀ y : El a, (x = y) ⇒ (y = x)) ≔ 
begin
    assume a;
    refine fa_i (λ x : El a, `∀ y : El a, (x = y) ⇒ (y = x)) _;
    assume x;
    refine fa_i (λ y : El a, (x = y) ⇒ (y = x)) _;
    assume y;
    refine imp_i (x = y) (y = x) _;
    assume Pxy P;
    refine imp_e (P y) (P x) _;
    refine Pxy (λ z, (P z) ⇒ (P x)) _;
    refine imp_i (P x) (P x) _;
    assume Px;
    refine Px
end;

opaque symbol eq_trans : Π (a : Set), Prf (`∀ x : El a, `∀ y : El a, `∀ z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) ≔ 
begin
    assume a;
    refine fa_i (λ x : El a, `∀ y : El a, `∀ z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) _;
    assume x;
    refine fa_i (λ y : El a, `∀ z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) _;
    assume y;
    refine fa_i (λ z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) _;
    assume z;
    refine imp_i ((x = y) ∧ (y = z)) (x = z) _;
    assume Pxyz;
    assume P Px;
    refine (and_e_r (x = y) (y = z) Pxyz) P ((and_e_l (x = y) (y = z) Pxyz) P Px)
end;