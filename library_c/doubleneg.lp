require open Logic.Construkti.properties;
require open Logic.Construkti.kuroda;
require open Logic.Construkti.logic;
require open Logic.Construkti.deduction;


// Some results about double negations

opaque symbol double_neg (p : Prop) : Prf ¬ ¬ (p ⇒ ¬ ¬ p) ≔ 
begin
    assume p;
    refine imp_i_c p (¬ ¬ p) _;
    assume pP;
    refine neg_i_c (¬ p) _;
    assume pNP;
    refine neg_e_c p _ _ 
    {refine pNP}
    {refine pP}
end;

opaque symbol neg_imp (p q : Prop) : Prf ¬ ¬ ((p ⇒ q) ⇒ (¬ q ⇒ ¬ p)) ≔ 
begin
    assume p q;
    refine imp_i_c (p ⇒ q) (¬ q ⇒ ¬ p) _;
    assume pPQ;
    refine imp_i_c (¬ q) (¬ p) _;
    assume pNQ;
    refine neg_i_c p _;
    assume pP;
    refine neg_e_c q _ _ 
    {refine pNQ}
    {refine (imp_e_c p q pPQ) pP}
end;

opaque symbol neg_imp1 (p q : Prop) : Prf ¬ ¬ ((¬ ¬ p ⇒ ¬ ¬ q) ⇒ ¬ ¬ (p ⇒ q)) ≔ 
begin
    assume p q;
    refine imp_i_c (¬ ¬ p ⇒ ¬ ¬ q) (¬ ¬ (p ⇒ q)) _;
    assume pPQ;
    refine neg_i_c (¬ (p ⇒ q)) _;
    assume pNPQ;
    refine neg_e_c (p ⇒ q) _ _ 
    {refine pNPQ}
    {refine imp_i_c p q _;
    assume pP;
    refine bot_e_c _ q;
    refine neg_e_c (¬ q) _ _ 
    {refine imp_e_c (¬ ¬ p) (¬ ¬ q) pPQ _;
    refine imp_e_c p (¬ ¬ p) (double_neg p) pP}
    {refine neg_i_c q _;
    assume pQ;
    refine neg_e_c (p ⇒ q) _ _ 
    {refine pNPQ}
    {refine imp_i_c p q _;
    assume pP2;
    refine pQ}}}
end;

opaque symbol neg_imp2 (p q : Prop) : Prf ¬ ¬ (¬ ¬ (p ⇒ q) ⇒ (¬ ¬ p ⇒ ¬ ¬ q)) ≔ 
begin
    assume p q;
    refine imp_i_c (¬ ¬ (p ⇒ q)) (¬ ¬ p ⇒ ¬ ¬ q) _;
    assume pNNPQ;
    refine imp_i_c (¬ ¬ p) (¬ ¬ q) _;
    assume pNNP;
    refine neg_i_c (¬ q) _;
    assume pNQ;
    refine neg_e_c (¬ (p ⇒ q)) _ _ 
    {refine pNNPQ}
    {refine neg_i_c (p ⇒ q) _ ;
    assume pPQ;
    refine neg_e_c (¬ p) _ _ 
    {refine pNNP}
    {refine neg_i_c p _;
    assume pP;
    refine neg_e_c q _ _ 
    {refine pNQ}
    {refine imp_e_c p q pPQ pP}}}
end;

opaque symbol neg_and1 (p q : Prop) : Prf ¬ ¬ ((¬ ¬ p ∧ ¬ ¬ q) ⇒ ¬ ¬ (p ∧ q)) ≔ 
begin
    assume p q;
    refine imp_i_c (¬ ¬ p ∧ ¬ ¬ q) (¬ ¬ (p ∧ q)) _;
    assume pNNPQ;
    refine neg_i_c (¬ (p ∧ q)) _;
    assume pNPQ;
    refine neg_e_c (¬ q) _ _
    {refine and_e_r_c (¬ (¬ p)) (¬ (¬ q)) pNNPQ}
    {refine neg_i_c q _;
    assume pQ;
    refine neg_e_c (¬ p) _ _
    {refine and_e_l_c (¬ (¬ p)) (¬ (¬ q)) pNNPQ}
    {refine neg_i_c p _;
    assume pP;
    refine neg_e_c (p ∧ q) _ _
    {refine pNPQ}
    {refine and_i_c p q pP pQ}}}
end;

opaque symbol neg_and2 (p q : Prop) : Prf ¬ ¬ (¬ ¬ (p ∧ q) ⇒ (¬ ¬ p ∧ ¬ ¬ q)) ≔ 
begin
    assume p q; 
    refine imp_i_c (¬ ¬ (p ∧ q)) (¬ ¬ p ∧ ¬ ¬ q) _;
    assume pNNPQ;
    refine and_i_c (¬ ¬ p) (¬ ¬ q) _ _
    {refine neg_i_c (¬ p) _;
    assume pNP;
    refine neg_e_c (¬ (p ∧ q)) _ _ 
    {refine pNNPQ}
    {refine neg_i_c (p ∧ q) _;
    assume pPQ;
    refine neg_e_c p _ _ 
    {refine pNP}
    {refine and_e_l_c p q pPQ}}}
    {refine neg_i_c (¬ q) _;
    assume pNQ;
    refine neg_e_c (¬ (p ∧ q)) _ _ 
    {refine pNNPQ}
    {refine neg_i_c (p ∧ q) _;
    assume pPQ;
    refine neg_e_c q _ _ 
    {refine pNQ}
    {refine and_e_r_c p q pPQ}}}
end;

opaque symbol neg_or1 (p q : Prop) : Prf ¬ ¬ (¬ (p ∨ q) ⇒ (¬ p ∧ ¬ q)) ≔ 
begin
    assume p q;
    refine imp_i_c (¬ (p ∨ q)) (¬ p ∧ ¬ q) _;
    assume pNPQ;
    refine and_i_c (¬ p) (¬ q) _ _
    {refine neg_i_c p _;
    assume pP;
    refine neg_e_c (p ∨ q) _ _ 
    {refine pNPQ}
    {refine or_i_l_c p pP q}}
    {refine neg_i_c q _;
    assume pQ;
    refine neg_e_c (p ∨ q) _ _ 
    {refine pNPQ}
    {refine or_i_r_c q pQ p}}
end;

opaque symbol neg_or2 (p q : Prop) : Prf ¬ ¬ ((¬ p ∧ ¬ q) ⇒ ¬ (p ∨ q)) ≔ 
begin
    assume p q;
    refine imp_i_c (¬ p ∧ ¬ q) (¬ (p ∨ q)) _;
    assume pNPQ;
    refine neg_i_c (p ∨ q) _;
    assume pPQ;
    refine or_e_c p q pPQ ⊥ _ _ 
    {assume pP;
    refine neg_e_c p _ pP;
    refine and_e_l_c (¬ p) (¬ q) pNPQ}
    {assume pQ;
    refine neg_e_c q _ pQ;
    refine and_e_r_c (¬ p) (¬ q) pNPQ}
end;

opaque symbol neg_fa (a : Set) (p : El a → Prop) : Prf ¬ ¬ (¬ ¬ ∀_c p ⇒ ∀_c (λ x, ¬ ¬ (p x))) ≔ 
begin
    assume a p;
    refine imp_i_c (¬ ¬ ∀_c p) (∀_c (λ x, ¬ ¬ (p x))) _;
    assume pNNP;
    refine fa_i_c (λ x, ¬ ¬ (p x)) _;
    assume x;
    refine neg_i_c (¬ (p x)) _;
    assume pNP;
    refine neg_e_c (¬ (∀_c p)) _ _ 
    {refine pNNP}
    {refine neg_i_c (∀_c p) _;
    assume pP;
    refine neg_e_c (p x) _ _ 
    {refine pNP}
    {refine fa_e_c  p pP x}}
end;

opaque symbol neg_ex1 (a : Set) (p : El a → Prop) : Prf ¬ ¬ (¬ ∃ p ⇒ ∀_c (λ x, ¬ (p x))) ≔ 
begin
    assume a p;
    refine imp_i_c (¬ ∃ p) (∀_c (λ x, ¬ (p x))) _;
    assume pNP;
    refine fa_i_c (λ x, ¬ (p x)) _;
    assume x;
    refine neg_i_c (p x) _;
    assume pP;
    refine neg_e_c (∃ p) _ _ 
    {refine pNP}
    {refine ex_i_c p x pP}
end;

opaque symbol neg_ex2 (a : Set) (p : El a → Prop) : Prf ¬ ¬ (∀_c (λ x, ¬ (p x)) ⇒ ¬ ∃ p) ≔ 
begin
    assume a p;
    refine imp_i_c (∀_c (λ x, ¬ (p x))) (¬ ∃ p) _;
    assume pNP;
    refine neg_i_c (∃ p) _;
    assume pP;
    refine ex_e_c p pP ⊥ _;
    assume t pPt;
    refine neg_e_c (p t) _ _ 
    {refine fa_e_c (λ x, ¬ (p x)) pNP t}
    {refine pPt}
end;

opaque symbol triple_neg (p : Prop) : Prf ¬ ¬ (¬ ¬ ¬ p ⇒ ¬ p) ≔ 
begin
    assume p;
    refine imp_i_c (¬ ¬ ¬ p) (¬ p) _;
    assume pNNNP;
    refine neg_i_c p _;
    assume pP;
    refine neg_e_c (¬ ¬ p) _ _ 
    {refine pNNNP}
    {refine imp_e_c p (¬ ¬ p) (double_neg p) pP}
end;

opaque symbol neg_bot : Prf ¬ ¬ (¬ ¬ ⊥ ⇒ ⊥) ≔ 
begin
    refine imp_i_c (¬ ¬ ⊥) ⊥ _;
    assume pB;
    refine neg_e_c (¬ ⊥) _ _ 
    {refine pB}
    {refine neg_i_c ⊥ _;
    assume pN; 
    refine pN}
end;

opaque symbol neg_top : Prf ¬ ¬ (¬ ¬ ⊤ ⇒ ⊤) ≔ 
begin
    refine imp_i_c (¬ ¬ ⊤) ⊤ _;
    assume pT;
    refine top_i_c
end;

opaque symbol neg_iff (p q : Prop) : Prf ¬ ¬ ((¬ ¬ p ⇔ ¬ ¬ q) ⇒ ¬ ¬ (p ⇔ q)) ≔ 
begin
    assume p q;
    refine imp_i_c (¬ ¬ p ⇔ ¬ ¬ q) (¬ ¬ (p ⇔ q)) _;
    assume pH;
    refine imp_e_c (¬ ¬ (p ⇒ q) ∧ ¬ ¬ (q ⇒ p)) (¬ ¬ ((p ⇒ q) ∧ (q ⇒ p))) (neg_and1 (p ⇒ q) (q ⇒ p)) _;
    refine and_i_c (¬ ¬ (p ⇒ q)) (¬ ¬ (q ⇒ p)) _ _ 
    {refine imp_e_c (¬ ¬ p ⇒ ¬ ¬ q) (¬ ¬ (p ⇒ q)) (neg_imp1 p q) _;
    refine and_e_l_c (¬ ¬ p ⇒ ¬ ¬ q) (¬ ¬ q ⇒ ¬ ¬ p) pH}
    {refine imp_e_c (¬ ¬ q ⇒ ¬ ¬ p) (¬ ¬ (q ⇒ p)) (neg_imp1 q p) _;
    refine and_e_r_c (¬ ¬ p ⇒ ¬ ¬ q) (¬ ¬ q ⇒ ¬ ¬ p) pH}
end;