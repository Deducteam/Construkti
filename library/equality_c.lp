require open Logic.Construkti.properties;
require open Logic.Construkti.kuroda;
require open Logic.Construkti.logic;
require open Logic.Construkti.deduction;


// Polymorphic equality 

constant symbol = [a] : El a → El a → Prop;
notation = infix 4;
rule Prf ¬ ¬ (@= $a $x $y) ↪ Π (P : El $a → Prop), Prf ¬ ¬ (P $x) → Prf ¬ ¬ (P $y);

opaque symbol eq_refl : Π (a : Set), Prf ¬ ¬ (`∀_c x : El a, x = x) ≔
begin
    assume a;
    refine fa_i_c (λ x : El a, x = x) _;
    assume x;
    assume P Py;
    refine Py
end;

opaque symbol eq_sym : Π (a : Set), Prf ¬ ¬ (`∀_c x : El a, `∀_c y : El a, (x = y) ⇒ (y = x)) ≔ 
begin
    assume a;
    refine fa_i_c (λ x : El a, `∀_c y : El a, (x = y) ⇒ (y = x)) _;
    assume x;
    refine fa_i_c (λ y : El a, (x = y) ⇒ (y = x)) _;
    assume y;
    refine imp_i_c (x = y) (y = x) _;
    assume Pxy P;
    refine imp_e_c (P y) (P x) _;
    refine Pxy (λ z, (P z) ⇒ (P x)) _;
    refine imp_i_c (P x) (P x) _;
    assume Px;
    refine Px
end;

opaque symbol eq_trans : Π (a : Set), Prf ¬ ¬ (`∀_c x : El a, `∀_c y : El a, `∀_c z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) ≔ 
begin
    assume a;
    refine fa_i_c (λ x : El a, `∀_c y : El a, `∀_c z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) _;
    assume x;
    refine fa_i_c (λ y : El a, `∀_c z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) _;
    assume y;
    refine fa_i_c (λ z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) _;
    assume z;
    refine imp_i_c ((x = y) ∧ (y = z)) (x = z) _;
    assume Pxyz;
    assume P Px;
    refine (and_e_r_c (x = y) (y = z) Pxyz) P ((and_e_l_c (x = y) (y = z) Pxyz) P Px)
end;

opaque symbol eq_f : Π (a b : Set), Prf ¬ ¬ (`∀_c f : El a → El b, `∀_c x : El a, `∀_c y : El a, ((x = y) ⇒ (f x = f y))) ≔ 
begin
    assume a b;
    refine fa_i_c (λ f : El a → El b, `∀_c x : El a, `∀_c y : El a, ((x = y) ⇒ (f x = f y))) _;
    assume f;
    refine fa_i_c (λ x : El a, `∀_c y : El a, ((x = y) ⇒ (f x = f y))) _;
    assume x;
    refine fa_i_c (λ y : El a, ((x = y) ⇒ (f x = f y))) _;
    assume y;
    refine imp_i_c (x = y) (f x = f y) _;
    assume Pxy;
    assume P;
    refine Pxy (λ w : El a, P (f w))
end;

opaque symbol eq_f2 : Π (a1 a2 b : Set), Prf ¬ ¬ (`∀_c f : El a1 → El a2 → El b, `∀_c x1 : El a1, `∀_c x2 : El a2, `∀_c y1 : El a1, `∀_c y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) ≔ 
begin
    assume a1 a2 b;
    refine fa_i_c (λ f : El a1 → El a2 → El b, `∀_c x1 : El a1, `∀_c x2 : El a2, `∀_c y1 : El a1, `∀_c y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume f;
    refine fa_i_c (λ x1 : El a1, `∀_c x2 : El a2, `∀_c y1 : El a1, `∀_c y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume x1;
    refine fa_i_c (λ x2 : El a2, `∀_c y1 : El a1, `∀_c y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume x2;
    refine fa_i_c (λ y1 : El a1, `∀_c y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume y1;
    refine fa_i_c (λ y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume y2;
    refine imp_i_c (x1 = y1) ((x2 = y2) ⇒ (f x1 x2 = f y1 y2)) _;
    assume Pxy1;
    refine imp_i_c (x2 = y2) (f x1 x2 = f y1 y2) _;
    assume Pxy2;
    assume P Pfx;
    refine Pxy1 (λ w : El a1, P (f w y2)) _;
    refine Pxy2 (λ w : El a2, P (f x1 w)) Pfx
end;

opaque symbol eq_fg : Π (a b c : Set), Prf ¬ ¬ (`∀_c f : El b → El c, `∀_c g : El a → El b, `∀_c x : El a, `∀_c y : El a, ((x = y) ⇒ (f (g x) = f (g y)))) ≔ 
begin
    assume a b c;
    refine fa_i_c (λ f : El b → El c, `∀_c g : El a → El b, `∀_c x : El a, `∀_c y : El a, ((x = y) ⇒ (f (g x) = f (g y)))) _;
    assume f;
    refine fa_i_c (λ g : El a → El b, `∀_c x : El a, `∀_c y : El a, ((x = y) ⇒ (f (g x) = f (g y)))) _;
    assume g;
    refine fa_e_c (λ f : El a → El c, `∀_c x : El a, `∀_c y : El a, ((x = y) ⇒ (f x = f y))) (eq_f a c) (λ w, f (g w))
end;