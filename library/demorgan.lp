require open Construkti.logic;
require open Construkti.library.doubleneg;
require open Construkti.library.classic;


// De Morgan's laws

opaque symbol demorgan_and : Π (A B : Prop), Prf (¬ (A ∧ B) ⇔ ¬ A ∨ ¬ B) ≔
begin
    assume A B;
    refine and_i (¬ (A ∧ B) ⇒ (¬ A ∨ ¬ B)) _ ((¬ A ∨ ¬ B) ⇒ ¬ (A ∧ B)) _ 
    {refine imp_i (¬ (A ∧ B)) (¬ A ∨ ¬ B) _;
    assume pNAB;
    refine imp_e (¬ ¬ (¬ A ∨ ¬ B)) (¬ A ∨ ¬ B) (double_neg_elim (¬ A ∨ ¬ B)) _;
    refine neg_i (¬ (¬ A ∨ ¬ B)) _;
    assume pNNANB;
    refine neg_e (A ∧ B) pNAB _;
    refine and_i A _ B _ 
    {refine imp_e (¬ ¬ A) A (double_neg_elim A) _;
    refine neg_i (¬ A) _;
    assume pNA;
    refine neg_e (¬ A ∨ ¬ B) pNNANB _;
    refine or_il (¬ A) pNA (¬ B)}
    {refine imp_e (¬ ¬ B) B (double_neg_elim B) _;
    refine neg_i (¬ B) _;
    assume pNB;
    refine neg_e (¬ A ∨ ¬ B) pNNANB _;
    refine or_ir (¬ A) (¬ B) pNB}}
    {refine imp_i (¬ A ∨ ¬ B) (¬ (A ∧ B)) _;
    assume pNANB;
    refine neg_i (A ∧ B) _;
    assume pAB;
    refine or_e (¬ A) (¬ B) pNANB ⊥ _ _ 
    {assume pNA;
    refine neg_e A pNA (and_el A B pAB)}
    {assume pNB;
    refine neg_e B pNB (and_er A B pAB)}}
end;

opaque symbol demorgan_or : Π (A B : Prop), Prf (¬ (A ∨ B) ⇔ ¬ A ∧ ¬ B) ≔
begin
    assume A B;
    refine and_i (¬ (A ∨ B) ⇒ (¬ A ∧ ¬ B)) _ ((¬ A ∧ ¬ B) ⇒ ¬ (A ∨ B)) _ 
    {refine neg_or1 A B}
    {refine neg_or2 A B}
end;


// De Morgan's laws for quantifiers

opaque symbol demorgan_all : Π (a : Set), Π (p : El a → Prop), Prf (¬ ∀ p ⇔ ∃ (λ x, ¬ (p x))) ≔ 
begin
    assume a p;
    refine and_i (¬ (∀ p) ⇒ (`∃ x, ¬ (p x))) _ ((`∃ x, ¬ (p x)) ⇒ ¬ (∀ p)) _ 
    {refine imp_i (¬ (∀ p)) (`∃ x, ¬ (p x)) _;
    assume pNFP;
    refine imp_e (¬ ¬ (`∃ x, ¬ (p x))) (`∃ x, ¬ (p x)) (double_neg_elim (`∃ x, ¬ (p x))) _;
    refine neg_i (¬ (`∃ x, ¬ (p x))) _;
    assume pNENP;
    refine neg_e (∀ p) pNFP _;
    refine all_i p _;
    assume t;
    refine imp_e (¬ ¬ (p t)) (p t) (double_neg_elim (p t)) _;
    refine neg_i (¬ (p t)) _;
    assume pNPt;
    refine neg_e (`∃ x, ¬ (p x)) pNENP _;
    refine ex_i  (λ x, ¬ (p x)) t pNPt}
    {refine imp_i (`∃ x, ¬ (p x)) (¬ (∀ p)) _;
    assume pENP;
    refine neg_i (∀ p) _;
    assume pFP;
    refine ex_e (λ x, ¬ (p x)) pENP ⊥ _;
    assume t pNPt;
    refine neg_e (p t) pNPt _;
    refine all_e p pFP t}
end;

opaque symbol demorgan_ex : Π (a : Set), Π (p : El a → Prop), Prf (¬ ∃ p ⇔ ∀ (λ x, ¬ (p x))) ≔ 
begin
    assume a p;
    refine and_i (¬ ∃ p ⇒ ∀ (λ x, ¬ (p x))) _ ((∀ (λ x, ¬ (p x))) ⇒ ¬ ∃ p) _ 
    {refine neg_ex1 a p}
    {refine neg_ex2 a p}
end;
