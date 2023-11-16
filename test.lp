require open Logic.Construkti.logic;
require open Logic.Construkti.deduction;

opaque symbol ex1 : Prf (`∀ A, A ⇒ A) ≔ 
begin
    refine fa_i (λ A, A ⇒ A) _;
    assume A;
    refine imp_i A A _;
    assume pA;
    refine pA
end;

opaque symbol ex2 : Prf (`∀ A, `∀ B, (A ∧ B) ⇒ (B ∧ A)) ≔ 
begin
    refine fa_i (λ A, `∀ B, (A ∧ B) ⇒ (B ∧ A)) _;
    assume A;
    refine fa_i (λ B, (A ∧ B) ⇒ (B ∧ A)) _;
    assume B; 
    refine imp_i (A ∧ B) (B ∧ A) _;
    assume pA;
    refine and_i B A _ _
    {refine and_e_r A B pA}
    {refine and_e_l A B pA}
end;

opaque symbol ex3 : Prf (`∀ A, `∀ B, `∃ P, (P ⇒ A) ∧ (P ⇒ B)) ≔ 
begin
    refine fa_i (λ A, `∀ B, `∃ P, (P ⇒ A) ∧ (P ⇒ B)) _;
    assume A;
    refine fa_i (λ B, `∃ P, (P ⇒ A) ∧ (P ⇒ B)) _;
    assume B;
    apply ex_i (λ P, (P ⇒ A) ∧ (P ⇒ B)) (A ∧ B) _;
    apply and_i ((A ∧ B) ⇒ A) ((A ∧ B) ⇒ B) _ _
    {refine imp_i (A ∧ B) A _;
    assume pAB;
    apply and_e_l A B pAB}
    {refine imp_i (A ∧ B) B _;
    assume pAB;
    apply and_e_r A B pAB}
end;

opaque symbol excluded_middle : Prf (`∀ A, A ∨ ¬ A) ≔
begin
    refine fa_i (λ A, A ∨ ¬ A) _;
    assume A;
    refine absurd (A ∨ ¬ A) _;
    refine imp_i (¬ (A ∨ ¬ A)) ⊥ _;
    assume pANA;
    refine neg_e (A ∨ ¬ A) _ _ 
    {refine pANA}
    {refine or_i_r (¬ A) _ A;
    refine neg_i A _;
    assume pA;
    refine neg_e (A ∨ ¬ A) _ _ 
    {refine pANA}
    {refine or_i_l A pA (¬ A)}}
end;

opaque symbol double_neg_elim : Prf (`∀ A, ¬ ¬ A ⇒ A) ≔
begin
    refine fa_i (λ A, ¬ ¬ A ⇒ A) _;
    assume A;
    refine imp_i (¬ ¬ A) A _;
    assume pNNA;
    refine or_e A (¬ A) _ A _ _ 
    {refine fa_e (λ x, x ∨ ¬ x) excluded_middle A}
    {assume pA;
    refine pA}
    {assume pNA;
    refine bot_e _ A;
    refine neg_e (¬ A) pNNA pNA}
end;