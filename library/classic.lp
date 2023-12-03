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


// Other classical laws

opaque symbol clavius : Prf (`∀ A, (¬ A ⇒ A) ⇒ A) ≔
begin
    refine fa_i (λ A, (¬ A ⇒ A) ⇒ A) _;
    assume A;
    refine imp_i (¬ A ⇒ A) A _;
    assume pNAA;
    refine or_e A (¬ A) (excluded_middle A) A _ _ 
    {assume pA;
    refine pA}
    {assume pNA;
    refine imp_e (¬ A) A pNAA pNA}
end;

opaque symbol tarski : Prf (`∀ A, `∀ B, A ∨ (A ⇒ B)) ≔
begin
    refine fa_i (λ A, `∀ B, A ∨ (A ⇒ B)) _;
    assume A;
    refine fa_i (λ B, A ∨ (A ⇒ B)) _;
    assume B;
    refine or_e A (¬ A) (excluded_middle A) (A ∨ (A ⇒ B)) _ _ 
    {assume pA;
    refine or_i_l A _ (A ⇒ B);
    refine pA}
    {assume pNA;
    refine or_i_r (A ⇒ B) _ A;
    refine imp_i A B _;
    assume pA;
    refine bot_e _ B;
    refine neg_e A pNA pA}
end;

opaque symbol weak_peirce : Prf (`∀ A, ((A ⇒ ⊥) ⇒ A) ⇒ A) ≔
begin
    refine fa_i (λ A, ((A ⇒ ⊥) ⇒ A) ⇒ A) _;
    assume A;
    refine imp_i ((A ⇒ ⊥) ⇒ A) A _;
    assume pAFA;
    refine or_e A (¬ A) (excluded_middle A) A _ _ 
    {assume pA;
    refine pA}
    {assume pNA;
    refine imp_e (A ⇒ ⊥) A pAFA _;
    refine imp_i A ⊥ _;
    assume pA;
    refine neg_e A pNA pA}
end;

opaque symbol peirce : Prf (`∀ A, `∀ B, ((A ⇒ B) ⇒ A) ⇒ A) ≔
begin
    refine fa_i (λ A, `∀ B, ((A ⇒ B) ⇒ A) ⇒ A) _;
    assume A;
    refine fa_i (λ B, ((A ⇒ B) ⇒ A) ⇒ A) _;
    assume B;
    refine imp_i ((A ⇒ B) ⇒ A) A _;
    assume pABA;
    refine imp_e ((A ⇒ ⊥) ⇒ A) A _ _ 
    {refine fa_e (λ A, ((A ⇒ ⊥) ⇒ A) ⇒ A) weak_peirce A}
    {refine imp_i (A ⇒ ⊥) A _;
    assume pAF;
    refine imp_e (A ⇒ B) A pABA _;
    refine imp_i A B _;
    assume pA;
    refine bot_e _ B;
    refine imp_e A ⊥ pAF pA}
end;