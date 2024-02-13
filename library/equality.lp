require open Construkti.logic;


// Polymorphic equality 

constant symbol = [a] : El a → El a → Prop;
notation = infix 40;
rule Prf (@= $a $x $y) ↪ Π (P : El $a → Prop), Prf (P $x) → Prf (P $y);

opaque symbol eq_refl : Π (a : Set), Prf (`∀ x : El a, x = x) ≔
begin
    assume a;
    refine all_i (λ x : El a, x = x) _;
    assume x;
    assume P Py;
    refine Py
end;

opaque symbol eq_sym : Π (a : Set), Prf (`∀ x : El a, `∀ y : El a, (x = y) ⇒ (y = x)) ≔ 
begin
    assume a;
    refine all_i (λ x : El a, `∀ y : El a, (x = y) ⇒ (y = x)) _;
    assume x;
    refine all_i (λ y : El a, (x = y) ⇒ (y = x)) _;
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
    refine all_i (λ x : El a, `∀ y : El a, `∀ z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) _;
    assume x;
    refine all_i (λ y : El a, `∀ z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) _;
    assume y;
    refine all_i (λ z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) _;
    assume z;
    refine imp_i ((x = y) ∧ (y = z)) (x = z) _;
    assume Pxyz;
    assume P Px;
    refine (and_er (x = y) (y = z) Pxyz) P ((and_el (x = y) (y = z) Pxyz) P Px)
end;

opaque symbol eq_f : Π (a b : Set), Prf (`∀ f : El a → El b, `∀ x : El a, `∀ y : El a, ((x = y) ⇒ (f x = f y))) ≔ 
begin
    assume a b;
    refine all_i (λ f : El a → El b, `∀ x : El a, `∀ y : El a, ((x = y) ⇒ (f x = f y))) _;
    assume f;
    refine all_i (λ x : El a, `∀ y : El a, ((x = y) ⇒ (f x = f y))) _;
    assume x;
    refine all_i (λ y : El a, ((x = y) ⇒ (f x = f y))) _;
    assume y;
    refine imp_i (x = y) (f x = f y) _;
    assume Pxy;
    assume P;
    refine Pxy (λ w : El a, P (f w))
end;

opaque symbol eq_f2 : Π (a1 a2 b : Set), Prf (`∀ f : El a1 → El a2 → El b, `∀ x1 : El a1, `∀ x2 : El a2, `∀ y1 : El a1, `∀ y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) ≔ 
begin
    assume a1 a2 b;
    refine all_i (λ f : El a1 → El a2 → El b, `∀ x1 : El a1, `∀ x2 : El a2, `∀ y1 : El a1, `∀ y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume f;
    refine all_i (λ x1 : El a1, `∀ x2 : El a2, `∀ y1 : El a1, `∀ y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume x1;
    refine all_i (λ x2 : El a2, `∀ y1 : El a1, `∀ y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume x2;
    refine all_i (λ y1 : El a1, `∀ y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume y1;
    refine all_i (λ y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume y2;
    refine imp_i (x1 = y1) ((x2 = y2) ⇒ (f x1 x2 = f y1 y2)) _;
    assume Pxy1;
    refine imp_i (x2 = y2) (f x1 x2 = f y1 y2) _;
    assume Pxy2;
    assume P Pfx;
    refine Pxy1 (λ w : El a1, P (f w y2)) _;
    refine Pxy2 (λ w : El a2, P (f x1 w)) Pfx
end;

opaque symbol eq_fg : Π (a b c : Set), Prf (`∀ f : El b → El c, `∀ g : El a → El b, `∀ x : El a, `∀ y : El a, ((x = y) ⇒ (f (g x) = f (g y)))) ≔ 
begin
    assume a b c;
    refine all_i (λ f : El b → El c, `∀ g : El a → El b, `∀ x : El a, `∀ y : El a, ((x = y) ⇒ (f (g x) = f (g y)))) _;
    assume f;
    refine all_i (λ g : El a → El b, `∀ x : El a, `∀ y : El a, ((x = y) ⇒ (f (g x) = f (g y)))) _;
    assume g;
    refine all_e (λ f : El a → El c, `∀ x : El a, `∀ y : El a, ((x = y) ⇒ (f x = f y))) (eq_f a c) (λ w, f (g w))
end;
