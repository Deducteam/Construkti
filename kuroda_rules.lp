require open Logic.Construkti.logic;
require open Logic.Construkti.deduction;
require open Logic.Construkti.properties_rules;


// Classical connectives and quantifiers

symbol Prf_c : Prop → TYPE;
rule Prf_c $p ↪ Prf (¬ ¬ $p);

symbol ∀_c [a : Set] : (El a → Prop) → Prop; notation ∀_c quantifier;
rule @∀_c $a $p ↪ @∀ $a (λ x : El $a, ¬ ¬ ($p x)); 


// Kuroda's translation

opaque symbol imp_i_c (p q : Prop) : (Prf_c p → Prf_c q) → Prf_c (p ⇒ q) ≔ 
begin
    assume p q;
    assume pPQ;
    apply prop_neg_imp1 p q pPQ;
end;

opaque symbol imp_e_c (p q : Prop) : Prf_c (p ⇒ q) → (Prf_c p → Prf_c q) ≔ 
begin
    assume p q;
    assume pPQ;
    refine prop_neg_imp2 p q pPQ;
end;

opaque symbol and_i_c (p q : Prop) : Prf_c p → Prf_c q → Prf_c (p ∧ q) ≔
begin
    assume p q pP pQ;
    refine prop_neg_and1 p q _;
    refine and_i (¬ (¬ p)) (¬ (¬ q)) pP pQ;
end;

opaque symbol and_e_l_c (p q : Prop) : Prf_c (p ∧ q) → Prf_c p ≔
begin
    assume p q pPQ; 
    refine and_e_l (¬ (¬ p)) (¬ (¬ q)) _;
    refine prop_neg_and2 p q pPQ;
end;

opaque symbol and_e_r_c (p q : Prop) : Prf_c (p ∧ q) → Prf_c q ≔
begin
    assume p q pPQ; 
    refine and_e_r (¬ (¬ p)) (¬ (¬ q)) _;
    refine prop_neg_and2 p q pPQ;
end;

opaque symbol or_i_l_c (p : Prop) : Prf_c p → Π q : Prop, Prf_c (p ∨ q) ≔
begin
    assume p pP q;
    assume pPQ;
    refine neg_e (¬ p) _ _ 
    {refine pP}
    {refine and_e_l (¬ p) (¬ q) _;
    refine prop_neg_or1 p q pPQ}
end;

opaque symbol or_i_r_c (q : Prop) : Prf_c q → Π p : Prop, Prf_c (p ∨ q) ≔
begin
    assume q pQ p;
    assume pPQ;
    refine neg_e (¬ q) _ _ 
    {refine pQ}
    {refine and_e_r (¬ p) (¬ q) _;
    refine prop_neg_or1 p q pPQ}
end;

opaque symbol or_e_c (p q : Prop) : Prf_c (p ∨ q) → Π r : Prop, (Prf_c p → Prf_c r) → (Prf_c q → Prf_c r) → Prf_c r ≔
begin
    assume p q pPQ r pPR pQR;
    assume pR;
    refine neg_e (¬ (¬ p ∧ ¬ q)) _ _ 
    {refine prop_neg_and1 (¬ p) (¬ q) _;
    refine and_i (¬ ¬ ¬ p) (¬ ¬ ¬ q) _ _ 
    {assume pP;
    refine neg_e (¬ r) _ _ 
    {refine pPR pP}
    {refine pR}}
    {assume pQ;
    refine neg_e (¬ r) _ _ 
    {refine pQR pQ}
    {refine pR}}}
    {refine prop_neg_imp (¬ p ∧ ¬ q) (¬ (p ∨ q)) (prop_neg_or2 p q) _;
    refine pPQ}
end;

opaque symbol neg_i_c (p : Prop) : (Prf_c p → Prf_c ⊥) → Prf_c (¬ p) ≔
begin
    assume p pP;
    refine neg_i (¬ ¬ p) _;
    assume pN;
    apply prop_neg_bot _;
    refine pP pN
end;

opaque symbol neg_e_c (p : Prop) : Prf_c (¬ p) → Prf_c p → Prf_c ⊥ ≔
begin
    assume p pNP pP;
    refine prop_double_neg ⊥ _;
    apply neg_e (¬ ¬ p) pNP pP;
end;

opaque symbol top_i_c : Prf_c ⊤ ≔
begin
    refine prop_double_neg ⊤ _;
    apply top_i
end;

opaque symbol bot_e_c : Prf_c ⊥ → Π p : Prop, Prf_c p ≔
begin
    assume pB p;
    refine bot_e _ (¬ ¬ p);
    apply prop_neg_bot pB
end;

opaque symbol fa_i_c [a : Set] (p : El a → Prop) : (Π x : El a, Prf_c (p x)) → Prf_c (∀_c (λ x, p x)) ≔ 
begin
    assume a p pPx;
    refine prop_double_neg (∀_c (λ x, p x)) _;
    refine fa_i (λ x : El a, ¬ ¬ (p x)) _;
    assume x;
    refine (pPx x)
end;

opaque symbol fa_e_c [a : Set] (p : El a → Prop) : Prf_c (∀_c (λ x, p x)) → Π x : El a, Prf_c (p x) ≔ 
begin
    assume a p pP t;
    refine prop_triple_neg (¬ (p t)) _;
    refine fa_e (λ x : El a, ¬ ¬ ¬ ¬ (p x)) _ t;
    refine prop_neg_fa a (λ x : El a, ¬ ¬ (p x)) pP
end;

opaque symbol ex_i_c [a : Set] (p : El a → Prop) : Π t : El a, Prf_c (p t) → Prf_c (∃ p) ≔ 
begin
    assume a p t pP;
    refine prop_neg_imp (¬ ∃ p) (∀ (λ x, ¬ (p x))) (prop_neg_ex1 a p) _;
    refine neg_i (∀ (λ x, ¬ (p x))) _;
    assume pNP;
    refine neg_e (¬ (p t)) _ _
    {refine pP}
    {refine fa_e (λ x, ¬ (p x)) pNP t}
end;

opaque symbol ex_e_c [a : Set] (p : El a → Prop) : Prf_c (∃ p) → Π r : Prop, (Π x : El a, Prf_c (p x) → Prf_c r) → Prf_c r ≔ 
begin
    assume a p pP r pPR;
    refine neg_i (¬ r) _;
    assume pR;
    refine neg_e (¬ ∀ (λ x, ¬ (p x))) _ _ 
    {refine prop_double_neg (∀ (λ x, ¬ (p x))) _;
    refine fa_i (λ x, ¬ (p x)) _;
    assume x;
    refine prop_triple_neg (p x) _;
    refine neg_i (¬ ¬ (p x)) _;
    assume pNP;
    refine neg_e (¬ r) _ _ 
    {refine pPR x pNP}
    {refine pR}}
    {refine prop_neg_imp (∀ (λ x, ¬ (p x))) (¬ ∃ p) (prop_neg_ex2 a p) _;
    refine pP}
end;

opaque symbol absurd_c (p : Prop) : Prf_c (¬ p ⇒ ⊥) → Prf_c p ≔ 
begin
    assume p pP;
    refine prop_triple_neg (¬ p) _;
    refine neg_i (¬ ¬ ¬ p) _;
    assume pT;
    apply prop_neg_bot;
    refine imp_e (¬ ¬ ¬ p) (¬ ¬ ⊥) _ pT;
    refine prop_neg_imp2 (¬ p) ⊥ pP
end;
