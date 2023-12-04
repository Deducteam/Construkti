require open Logic.Construkti.properties;
require open Logic.Construkti.kuroda;
require open Logic.Construkti.logic;
require open Logic.Construkti.deduction;


// Excluded middle and double negation elimination

opaque symbol excluded_middle : Π A : Prop, Prf ¬ ¬ (A ∨ ¬ A) ≔
begin
    assume A;
    refine absurd_c (A ∨ ¬ A) _;
    refine imp_i_c (¬ (A ∨ ¬ A)) ⊥ _;
    assume pANA;
    refine neg_e_c (A ∨ ¬ A) _ _ 
    {refine pANA}
    {refine or_i_r_c (¬ A) _ A;
    refine neg_i_c A _;
    assume pA;
    refine neg_e_c (A ∨ ¬ A) _ _ 
    {refine pANA}
    {refine or_i_l_c A pA (¬ A)}}
end;

opaque symbol double_neg_elim : Π A : Prop, Prf ¬ ¬ (¬ ¬ A ⇒ A) ≔
begin
    assume A;
    refine imp_i_c (¬ ¬ A) A _;
    assume pNNA;
    refine or_e_c A (¬ A) _ A _ _ 
    {refine excluded_middle A}
    {assume pA;
    refine pA}
    {assume pNA;
    refine bot_e_c _ A;
    refine neg_e_c (¬ A) pNNA pNA}
end;


// Other classical laws

opaque symbol clavius : Prf ¬ ¬ (`∀_c A, (¬ A ⇒ A) ⇒ A) ≔
begin
    refine fa_i_c (λ A, (¬ A ⇒ A) ⇒ A) _;
    assume A;
    refine imp_i_c (¬ A ⇒ A) A _;
    assume pNAA;
    refine or_e_c A (¬ A) (excluded_middle A) A _ _ 
    {assume pA;
    refine pA}
    {assume pNA;
    refine imp_e_c (¬ A) A pNAA pNA}
end;

opaque symbol tarski : Prf ¬ ¬ (`∀_c A, `∀_c B, A ∨ (A ⇒ B)) ≔
begin
    refine fa_i_c (λ A, `∀_c B, A ∨ (A ⇒ B)) _;
    assume A;
    refine fa_i_c (λ B, A ∨ (A ⇒ B)) _;
    assume B;
    refine or_e_c A (¬ A) (excluded_middle A) (A ∨ (A ⇒ B)) _ _ 
    {assume pA;
    refine or_i_l_c A _ (A ⇒ B);
    refine pA}
    {assume pNA;
    refine or_i_r_c (A ⇒ B) _ A;
    refine imp_i_c A B _;
    assume pA;
    refine bot_e_c _ B;
    refine neg_e_c A pNA pA}
end;

opaque symbol weak_peirce : Prf ¬ ¬ (`∀_c A, ((A ⇒ ⊥) ⇒ A) ⇒ A) ≔
begin
    refine fa_i_c (λ A, ((A ⇒ ⊥) ⇒ A) ⇒ A) _;
    assume A;
    refine imp_i_c ((A ⇒ ⊥) ⇒ A) A _;
    assume pAFA;
    refine or_e_c A (¬ A) (excluded_middle A) A _ _ 
    {assume pA;
    refine pA}
    {assume pNA;
    refine imp_e_c (A ⇒ ⊥) A pAFA _;
    refine imp_i_c A ⊥ _;
    assume pA;
    refine neg_e_c A pNA pA}
end;

opaque symbol peirce : Prf ¬ ¬ (`∀_c A, `∀_c B, ((A ⇒ B) ⇒ A) ⇒ A) ≔
begin
    refine fa_i_c (λ A, `∀_c B, ((A ⇒ B) ⇒ A) ⇒ A) _;
    assume A;
    refine fa_i_c (λ B, ((A ⇒ B) ⇒ A) ⇒ A) _;
    assume B;
    refine imp_i_c ((A ⇒ B) ⇒ A) A _;
    assume pABA;
    refine imp_e_c ((A ⇒ ⊥) ⇒ A) A _ _ 
    {refine fa_e_c (λ A, ((A ⇒ ⊥) ⇒ A) ⇒ A) weak_peirce A}
    {refine imp_i_c (A ⇒ ⊥) A _;
    assume pAF;
    refine imp_e_c (A ⇒ B) A pABA _;
    refine imp_i_c A B _;
    assume pA;
    refine bot_e_c _ B;
    refine imp_e_c A ⊥ pAF pA}
end;