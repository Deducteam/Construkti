require open Logic.Construkti.logic;
require open Logic.Construkti.deduction;


// Excluded middle and double negation elimination

opaque symbol excluded_middle : Π A : Prop, Prf (A ∨ ¬ A) ≔
begin
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

opaque symbol double_neg_elim : Π A : Prop, Prf (¬ ¬ A ⇒ A) ≔
begin
    assume A;
    refine imp_i (¬ ¬ A) A _;
    assume pNNA;
    refine or_e A (¬ A) _ A _ _ 
    {refine excluded_middle A}
    {assume pA;
    refine pA}
    {assume pNA;
    refine bot_e _ A;
    refine neg_e (¬ A) pNNA pNA}
end;