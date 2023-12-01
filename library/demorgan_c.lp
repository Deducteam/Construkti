require open Logic.Construkti.properties;
require open Logic.Construkti.kuroda;
require open Logic.Construkti.logic;
require open Logic.Construkti.deduction;
require open Logic.Construkti.library.doubleneg_c;
require open Logic.Construkti.library.classic_c;


// De Morgan's laws

opaque symbol demorgan_and : Π (A B : Prop), Prf ¬ ¬ (¬ (A ∧ B) ⇔ ¬ A ∨ ¬ B) ≔
begin
    assume A B;
    refine and_i_c (¬ (A ∧ B) ⇒ (¬ A ∨ ¬ B)) ((¬ A ∨ ¬ B) ⇒ ¬ (A ∧ B)) _ _ 
    {refine imp_i_c (¬ (A ∧ B)) (¬ A ∨ ¬ B) _;
    assume pNAB;
    refine imp_e_c (¬ ¬ (¬ A ∨ ¬ B)) (¬ A ∨ ¬ B) (double_neg_elim (¬ A ∨ ¬ B)) _;
    refine neg_i_c (¬ (¬ A ∨ ¬ B)) _;
    assume pNNANB;
    refine neg_e_c (A ∧ B) pNAB _;
    refine and_i_c A B _ _ 
    {refine imp_e_c (¬ ¬ A) A (double_neg_elim A) _;
    refine neg_i_c (¬ A) _;
    assume pNA;
    refine neg_e_c (¬ A ∨ ¬ B) pNNANB _;
    refine or_i_l_c (¬ A) pNA (¬ B)}
    {refine imp_e_c (¬ ¬ B) B (double_neg_elim B) _;
    refine neg_i_c (¬ B) _;
    assume pNB;
    refine neg_e_c (¬ A ∨ ¬ B) pNNANB _;
    refine or_i_r_c (¬ B) pNB (¬ A)}}
    {refine imp_i_c (¬ A ∨ ¬ B) (¬ (A ∧ B)) _;
    assume pNANB;
    refine neg_i_c (A ∧ B) _;
    assume pAB;
    refine or_e_c (¬ A) (¬ B) pNANB ⊥ _ _ 
    {assume pNA;
    refine neg_e_c A pNA (and_e_l_c A B pAB)}
    {assume pNB;
    refine neg_e_c B pNB (and_e_r_c A B pAB)}}
end;

opaque symbol demorgan_or : Π (A B : Prop), Prf ¬ ¬ (¬ (A ∨ B) ⇔ ¬ A ∧ ¬ B) ≔
begin
    assume A B;
    refine and_i_c (¬ (A ∨ B) ⇒ (¬ A ∧ ¬ B)) ((¬ A ∧ ¬ B) ⇒ ¬ (A ∨ B)) _ _ 
    {refine neg_or1 A B}
    {refine neg_or2 A B}
end;


// De Morgan's laws for quantifiers

opaque symbol demorgan_fa : Π (a : Set), Π (p : El a → Prop), Prf ¬ ¬ (¬ ∀_c p ⇔ ∃ (λ x, ¬ (p x))) ≔ 
begin
    assume a p;
    refine and_i_c (¬ (∀_c p) ⇒ (`∃ x, ¬ (p x))) ((`∃ x, ¬ (p x)) ⇒ ¬ (∀_c p)) _ _ 
    {refine imp_i_c (¬ (∀_c p)) (`∃ x, ¬ (p x)) _;
    assume pNFP;
    refine imp_e_c (¬ ¬ (`∃ x, ¬ (p x))) (`∃ x, ¬ (p x)) (double_neg_elim (`∃ x, ¬ (p x))) _;
    refine neg_i_c (¬ (`∃ x, ¬ (p x))) _;
    assume pNENP;
    refine neg_e_c (∀_c p) pNFP _;
    refine fa_i_c p _;
    assume t;
    refine imp_e_c (¬ ¬ (p t)) (p t) (double_neg_elim (p t)) _;
    refine neg_i_c (¬ (p t)) _;
    assume pNPt;
    refine neg_e_c (`∃ x, ¬ (p x)) pNENP _;
    refine ex_i_c  (λ x, ¬ (p x)) t pNPt}
    {refine imp_i_c (`∃ x, ¬ (p x)) (¬ (∀_c p)) _;
    assume pENP;
    refine neg_i_c (∀_c p) _;
    assume pFP;
    refine ex_e_c (λ x, ¬ (p x)) pENP ⊥ _;
    assume t pNPt;
    refine neg_e_c (p t) pNPt _;
    refine fa_e_c p pFP t}
end;

opaque symbol demorgan_ex : Π (a : Set), Π (p : El a → Prop), Prf ¬ ¬ (¬ ∃ p ⇔ ∀_c (λ x, ¬ (p x))) ≔ 
begin
    assume a p;
    refine and_i_c (¬ ∃ p ⇒ ∀_c (λ x, ¬ (p x))) ((∀_c (λ x, ¬ (p x))) ⇒ ¬ ∃ p) _ _ 
    {refine neg_ex1 a p}
    {refine neg_ex2 a p}
end;