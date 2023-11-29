require open Logic.Construkti.logic;
require open Logic.Construkti.deduction;

// Some results

opaque symbol prop_double_neg (p : Prop) : Prf (p ⇒ ¬ ¬ p) ≔ 
begin
    assume p;
    refine imp_i p (¬ ¬ p) _;
    assume pP;
    refine neg_i (¬ p) _;
    assume pNP;
    refine neg_e p _ _ 
    {refine pNP}
    {refine pP}
end;

opaque symbol prop_neg_imp (p q : Prop) : Prf ((p ⇒ q) ⇒ (¬ q ⇒ ¬ p)) ≔ 
begin
    assume p q;
    refine imp_i (p ⇒ q) (¬ q ⇒ ¬ p) _;
    assume pPQ;
    refine imp_i (¬ q) (¬ p) _;
    assume pNQ;
    refine neg_i p _;
    assume pP;
    refine neg_e q _ _ 
    {refine pNQ}
    {apply (imp_e p q pPQ) pP}
end;

opaque symbol prop_neg_imp1 (p q : Prop) : Prf ((¬ ¬ p ⇒ ¬ ¬ q) ⇒ ¬ ¬ (p ⇒ q)) ≔ 
begin
    assume p q;
    refine imp_i (¬ ¬ p ⇒ ¬ ¬ q) (¬ ¬ (p ⇒ q)) _;
    assume pPQ;
    refine neg_i (¬ (p ⇒ q)) _;
    assume pNPQ;
    refine neg_e (p ⇒ q) _ _ 
    {refine pNPQ}
    {refine imp_i p q _;
    assume pP;
    refine bot_e _ q;
    refine neg_e (¬ q) _ _ 
    {refine imp_e (¬ ¬ p) (¬ ¬ q) pPQ _;
    refine imp_e p (¬ ¬ p) (prop_double_neg p) pP}
    {refine neg_i q _;
    assume pQ;
    refine neg_e (p ⇒ q) _ _ 
    {refine pNPQ}
    {refine imp_i p q _;
    assume pP2;
    apply pQ}}}
end;

opaque symbol prop_neg_imp2 (p q : Prop) : Prf (¬ ¬ (p ⇒ q) ⇒ (¬ ¬ p ⇒ ¬ ¬ q)) ≔ 
begin
    assume p q;
    refine imp_i (¬ ¬ (p ⇒ q)) (¬ ¬ p ⇒ ¬ ¬ q) _;
    assume pNNPQ;
    refine imp_i (¬ ¬ p) (¬ ¬ q) _;
    assume pNNP;
    refine neg_i (¬ q) _;
    assume pNQ;
    refine neg_e (¬ (p ⇒ q)) _ _ 
    {refine pNNPQ}
    {refine neg_i (p ⇒ q) _ ;
    assume pPQ;
    refine neg_e (¬ p) _ _ 
    {refine pNNP}
    {refine neg_i p _;
    assume pP;
    refine neg_e q _ _ 
    {refine pNQ}
    {apply imp_e p q pPQ pP}}}
end;

opaque symbol prop_neg_and1 (p q : Prop) : Prf ((¬ ¬ p ∧ ¬ ¬ q) ⇒ ¬ ¬ (p ∧ q)) ≔ 
begin
    assume p q;
    refine imp_i (¬ ¬ p ∧ ¬ ¬ q) (¬ ¬ (p ∧ q)) _;
    assume pNNPQ;
    refine neg_i (¬ (p ∧ q)) _;
    assume pNPQ;
    refine neg_e (¬ q) _ _
    {refine and_e_r (¬ (¬ p)) (¬ (¬ q)) pNNPQ}
    {refine neg_i q _;
    assume pQ;
    refine neg_e (¬ p) _ _
    {refine and_e_l (¬ (¬ p)) (¬ (¬ q)) pNNPQ}
    {refine neg_i p _;
    assume pP;
    refine neg_e (p ∧ q) _ _
    {refine pNPQ}
    {refine and_i p q pP pQ}}}
end;

opaque symbol prop_neg_and2 (p q : Prop) : Prf (¬ ¬ (p ∧ q) ⇒ (¬ ¬ p ∧ ¬ ¬ q)) ≔ 
begin
    assume p q; 
    refine imp_i (¬ ¬ (p ∧ q)) (¬ ¬ p ∧ ¬ ¬ q) _;
    assume pNNPQ;
    refine and_i (¬ ¬ p) (¬ ¬ q) _ _
    {refine neg_i (¬ p) _;
    assume pNP;
    refine neg_e (¬ (p ∧ q)) _ _ 
    {refine pNNPQ}
    {refine neg_i (p ∧ q) _;
    assume pPQ;
    refine neg_e p _ _ 
    {refine pNP}
    {apply and_e_l p q pPQ}}}
    {refine neg_i (¬ q) _;
    assume pNQ;
    refine neg_e (¬ (p ∧ q)) _ _ 
    {refine pNNPQ}
    {refine neg_i (p ∧ q) _;
    assume pPQ;
    refine neg_e q _ _ 
    {refine pNQ}
    {apply and_e_r p q pPQ}}}
end;

opaque symbol prop_neg_or1 (p q : Prop) : Prf (¬ (p ∨ q) ⇒ (¬ p ∧ ¬ q)) ≔ 
begin
    assume p q;
    refine imp_i (¬ (p ∨ q)) (¬ p ∧ ¬ q) _;
    assume pNPQ;
    refine and_i (¬ p) (¬ q) _ _
    {refine neg_i p _;
    assume pP;
    refine neg_e (p ∨ q) _ _ 
    {refine pNPQ}
    {apply or_i_l p pP q}}
    {refine neg_i q _;
    assume pQ;
    refine neg_e (p ∨ q) _ _ 
    {refine pNPQ}
    {apply or_i_r q pQ p}}
end;

opaque symbol prop_neg_or2 (p q : Prop) : Prf ((¬ p ∧ ¬ q) ⇒ ¬ (p ∨ q)) ≔ 
begin
    assume p q;
    refine imp_i (¬ p ∧ ¬ q) (¬ (p ∨ q)) _;
    assume pNPQ;
    refine neg_i (p ∨ q) _;
    assume pPQ;
    refine or_e p q pPQ ⊥ _ _ 
    {assume pP;
    refine neg_e p _ pP;
    refine and_e_l (¬ p) (¬ q) pNPQ}
    {assume pQ;
    refine neg_e q _ pQ;
    refine and_e_r (¬ p) (¬ q) pNPQ}
end;

opaque symbol prop_neg_fa (a : Set) (p : El a → Prop) : Prf (¬ ¬ ∀ p ⇒ ∀ (λ x, ¬ ¬ (p x))) ≔ 
begin
    assume a p;
    refine imp_i (¬ ¬ ∀ p) (∀ (λ x, ¬ ¬ (p x))) _;
    assume pNNP;
    refine fa_i (λ x, ¬ ¬ (p x)) _;
    assume x;
    refine neg_i (¬ (p x)) _;
    assume pNP;
    refine neg_e (¬ (∀ p)) _ _ 
    {refine pNNP}
    {refine neg_i (∀ p) _;
    assume pP;
    refine neg_e (p x) _ _ 
    {refine pNP}
    {apply fa_e  p pP x}}
end;

opaque symbol prop_neg_ex1 (a : Set) (p : El a → Prop) : Prf (¬ ∃ p ⇒ ∀ (λ x, ¬ (p x))) ≔ 
begin
    assume a p;
    refine imp_i (¬ ∃ p) (∀ (λ x, ¬ (p x))) _;
    assume pNP;
    refine fa_i (λ x, ¬ (p x)) _;
    assume x;
    refine neg_i (p x) _;
    assume pP;
    refine neg_e (∃ p) _ _ 
    {refine pNP}
    {refine ex_i p x pP}
end;

opaque symbol prop_neg_ex2 (a : Set) (p : El a → Prop) : Prf (∀ (λ x, ¬ (p x)) ⇒ ¬ ∃ p) ≔ 
begin
    assume a p;
    refine imp_i (∀ (λ x, ¬ (p x))) (¬ ∃ p) _;
    assume pNP;
    refine neg_i (∃ p) _;
    assume pP;
    refine ex_e p pP ⊥ _;
    assume t pPt;
    refine neg_e (p t) _ _ 
    {refine fa_e (λ x, ¬ (p x)) pNP t}
    {refine pPt}
end;

opaque symbol prop_triple_neg (p : Prop) : Prf (¬ ¬ ¬ p ⇒ ¬ p) ≔ 
begin
    assume p;
    refine imp_i (¬ ¬ ¬ p) (¬ p) _;
    assume pNNNP;
    refine neg_i p _;
    assume pP;
    refine neg_e (¬ ¬ p) _ _ 
    {refine pNNNP}
    {refine imp_e p (¬ ¬ p) (prop_double_neg p) pP}
end;

opaque symbol prop_neg_bot : Prf (¬ ¬ ⊥ ⇒ ⊥) ≔ 
begin
    refine imp_i (¬ ¬ ⊥) ⊥ _;
    assume pB;
    refine neg_e (¬ ⊥) _ _ 
    {refine pB}
    {refine neg_i ⊥ _;
    assume pN; 
    refine pN}
end;

opaque symbol prop_neg_top : Prf (¬ ¬ ⊤ ⇒ ⊤) ≔ 
begin
    refine imp_i (¬ ¬ ⊤) ⊤ _;
    assume pT;
    refine top_i
end;

opaque symbol prop_neg_iff (p q : Prop) : Prf ((¬ ¬ p ⇔ ¬ ¬ q) ⇒ ¬ ¬ (p ⇔ q)) ≔ 
begin
    assume p q;
    refine imp_i (¬ ¬ p ⇔ ¬ ¬ q) (¬ ¬ (p ⇔ q)) _;
    assume pH;
    refine imp_e (¬ ¬ (p ⇒ q) ∧ ¬ ¬ (q ⇒ p)) (¬ ¬ ((p ⇒ q) ∧ (q ⇒ p))) (prop_neg_and1 (p ⇒ q) (q ⇒ p)) _;
    refine and_i (¬ ¬ (p ⇒ q)) (¬ ¬ (q ⇒ p)) _ _ 
    {refine imp_e (¬ ¬ p ⇒ ¬ ¬ q) (¬ ¬ (p ⇒ q)) (prop_neg_imp1 p q) _;
    refine and_e_l (¬ ¬ p ⇒ ¬ ¬ q) (¬ ¬ q ⇒ ¬ ¬ p) pH}
    {refine imp_e (¬ ¬ q ⇒ ¬ ¬ p) (¬ ¬ (q ⇒ p)) (prop_neg_imp1 q p) _;
    refine and_e_r (¬ ¬ p ⇒ ¬ ¬ q) (¬ ¬ q ⇒ ¬ ¬ p) pH}
end;