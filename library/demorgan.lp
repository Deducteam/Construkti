require open Logic.Construkti.logic;
require open Logic.Construkti.deduction;
require open Logic.Construkti.library.doubleneg;
require open Logic.Construkti.library.classic;


// De Morgan's laws

opaque symbol demorgan_and : Π (A B : Prop), Prf (¬ (A ∧ B) ⇔ ¬ A ∨ ¬ B) ≔
begin
    assume A B;
    refine and_i (¬ (A ∧ B) ⇒ (¬ A ∨ ¬ B)) ((¬ A ∨ ¬ B) ⇒ ¬ (A ∧ B)) _ _ 
    {refine imp_i (¬ (A ∧ B)) (¬ A ∨ ¬ B) _;
    assume pNAB;
    refine imp_e (¬ ¬ (¬ A ∨ ¬ B)) (¬ A ∨ ¬ B) (double_neg_elim (¬ A ∨ ¬ B)) _;
    refine neg_i (¬ (¬ A ∨ ¬ B)) _;
    assume pNNANB;
    refine neg_e (A ∧ B) pNAB _;
    refine and_i A B _ _ 
    {refine imp_e (¬ ¬ A) A (double_neg_elim A) _;
    refine neg_i (¬ A) _;
    assume pNA;
    refine neg_e (¬ A ∨ ¬ B) pNNANB _;
    refine or_i_l (¬ A) pNA (¬ B)}
    {refine imp_e (¬ ¬ B) B (double_neg_elim B) _;
    refine neg_i (¬ B) _;
    assume pNB;
    refine neg_e (¬ A ∨ ¬ B) pNNANB _;
    refine or_i_r (¬ B) pNB (¬ A)}}
    {refine imp_i (¬ A ∨ ¬ B) (¬ (A ∧ B)) _;
    assume pNANB;
    refine neg_i (A ∧ B) _;
    assume pAB;
    refine or_e (¬ A) (¬ B) pNANB ⊥ _ _ 
    {assume pNA;
    refine neg_e A pNA (and_e_l A B pAB)}
    {assume pNB;
    refine neg_e B pNB (and_e_r A B pAB)}}
end;

opaque symbol demorgan_or : Π (A B : Prop), Prf (¬ (A ∨ B) ⇔ ¬ A ∧ ¬ B) ≔
begin
    assume A B;
    refine and_i (¬ (A ∨ B) ⇒ (¬ A ∧ ¬ B)) ((¬ A ∧ ¬ B) ⇒ ¬ (A ∨ B)) _ _ 
    {refine prop_neg_or1 A B}
    {refine prop_neg_or2 A B}
end;


// De Morgan's laws for quantifiers

opaque symbol demorgan_fa : Π (a : Set), Π (p : El a → Prop), Prf (¬ ∀ p ⇔ ∃ (λ x, ¬ (p x))) ≔ 
begin
    assume a p;
    refine and_i (¬ (∀ p) ⇒ (`∃ x, ¬ (p x))) ((`∃ x, ¬ (p x)) ⇒ ¬ (∀ p)) _ _ 
    {refine imp_i (¬ (∀ p)) (`∃ x, ¬ (p x)) _;
    assume pNFP;
    refine imp_e (¬ ¬ (`∃ x, ¬ (p x))) (`∃ x, ¬ (p x)) (double_neg_elim (`∃ x, ¬ (p x))) _;
    refine neg_i (¬ (`∃ x, ¬ (p x))) _;
    assume pNENP;
    refine neg_e (∀ p) pNFP _;
    refine fa_i p _;
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
    refine fa_e p pFP t}
end;

opaque symbol demorgan_ex : Π (a : Set), Π (p : El a → Prop), Prf (¬ ∃ p ⇔ ∀ (λ x, ¬ (p x))) ≔ 
begin
    assume a p;
    refine and_i (¬ ∃ p ⇒ ∀ (λ x, ¬ (p x))) ((∀ (λ x, ¬ (p x))) ⇒ ¬ ∃ p) _ _ 
    {refine prop_neg_ex1 a p}
    {refine prop_neg_ex2 a p}
end;