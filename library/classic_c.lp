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