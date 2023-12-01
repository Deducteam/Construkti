require open Logic.Construkti.properties;
require open Logic.Construkti.kuroda;
require open Logic.Construkti.logic;
require open Logic.Construkti.deduction;


// Some results about logical connectives

opaque symbol imp_refl : Prf ¬ ¬ (`∀_c A, A ⇒ A) ≔ 
begin
    refine fa_i_c (λ A, A ⇒ A) _;
    assume A;
    refine imp_i_c A A _;
    assume pA;
    refine pA
end;

opaque symbol imp_trans : Prf ¬ ¬ (`∀_c A, `∀_c B, `∀_c C, ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)) ≔ 
begin
    refine fa_i_c (λ A, `∀_c B, `∀_c C, ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)) _;
    assume A;
    refine fa_i_c (λ B, `∀_c C, ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)) _;
    assume B;
    refine fa_i_c (λ C, ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)) _;
    assume C;
    refine imp_i_c ((A ⇒ B) ∧ (B ⇒ C)) (A ⇒ C) _;
    assume pABBC;
    refine imp_i_c A C _;
    assume pA;
    refine imp_e_c B C (and_e_r_c (A ⇒ B) (B ⇒ C) pABBC) _;
    refine imp_e_c A B (and_e_l_c (A ⇒ B) (B ⇒ C) pABBC) pA;
end;

opaque symbol and_comm : Prf ¬ ¬ (`∀_c A, `∀_c B, (A ∧ B) ⇒ (B ∧ A)) ≔ 
begin
    refine fa_i_c (λ A, `∀_c B, (A ∧ B) ⇒ (B ∧ A)) _;
    assume A;
    refine fa_i_c (λ B, (A ∧ B) ⇒ (B ∧ A)) _;
    assume B; 
    refine imp_i_c (A ∧ B) (B ∧ A) _;
    assume pA;
    refine and_i_c B A _ _
    {refine and_e_r_c A B pA}
    {refine and_e_l_c A B pA}
end;

opaque symbol and_assoc : Prf ¬ ¬ (`∀_c A, `∀_c B, `∀_c C, (A ∧ B) ∧ C ⇔ A ∧ B ∧ C) ≔ 
begin
    refine fa_i_c (λ A, `∀_c B, `∀_c C, (A ∧ B) ∧ C ⇔ A ∧ B ∧ C) _;
    assume A;
    refine fa_i_c (λ B, `∀_c C, (A ∧ B) ∧ C ⇔ A ∧ B ∧ C) _;
    assume B;
    refine fa_i_c (λ C, (A ∧ B) ∧ C ⇔ A ∧ B ∧ C) _;
    assume C;
    refine and_i_c ((A ∧ B) ∧ C ⇒ A ∧ (B ∧ C)) (A ∧ (B ∧ C) ⇒ (A ∧ B) ∧ C) _ _ 
    {refine imp_i_c ((A ∧ B) ∧ C) (A ∧ (B ∧ C)) _;
    assume pABC;
    refine and_i_c A (B ∧ C) _ _ 
    {refine and_e_l_c A B (and_e_l_c (A ∧ B) C pABC)}
    {refine and_i_c B C _ _ 
    {refine and_e_r_c A B (and_e_l_c (A ∧ B) C pABC)}
    {refine and_e_r_c (A ∧ B) C pABC}}}
    {refine imp_i_c (A ∧ (B ∧ C)) ((A ∧ B) ∧ C) _;
    assume pABC;
    refine and_i_c (A ∧ B) C _ _ 
    {refine and_i_c A B _ _
    {refine and_e_l_c A (B ∧ C) pABC}
    {refine and_e_l_c B C (and_e_r_c A (B ∧ C) pABC)}}
    {refine and_e_r_c B C (and_e_r_c A (B ∧ C) pABC)}}
end;

opaque symbol prop_and : Prf ¬ ¬ (`∀_c A, `∀_c B, `∃ P, (P ⇒ A) ∧ (P ⇒ B)) ≔ 
begin
    refine fa_i_c (λ A, `∀_c B, `∃ P, (P ⇒ A) ∧ (P ⇒ B)) _;
    assume A;
    refine fa_i_c (λ B, `∃ P, (P ⇒ A) ∧ (P ⇒ B)) _;
    assume B;
    refine ex_i_c (λ P, (P ⇒ A) ∧ (P ⇒ B)) (A ∧ B) _;
    refine and_i_c ((A ∧ B) ⇒ A) ((A ∧ B) ⇒ B) _ _
    {refine imp_i_c (A ∧ B) A _;
    assume pAB;
    refine and_e_l_c A B pAB}
    {refine imp_i_c (A ∧ B) B _;
    assume pAB;
    refine and_e_r_c A B pAB}
end;

opaque symbol or_comm : Prf ¬ ¬ (`∀_c A, `∀_c B, (A ∨ B) ⇒ (B ∨ A)) ≔ 
begin
    refine fa_i_c (λ A, `∀_c B, (A ∨ B) ⇒ (B ∨ A)) _;
    assume A;
    refine fa_i_c (λ B, (A ∨ B) ⇒ (B ∨ A)) _;
    assume B; 
    refine imp_i_c (A ∨ B) (B ∨ A) _;
    assume pAB;
    refine or_e_c A B pAB (B ∨ A) _ _
    {assume pA;
    refine or_i_r_c A pA B}
    {assume pB;
    refine or_i_l_c B pB A}
end;

opaque symbol or_assoc : Prf ¬ ¬ (`∀_c A, `∀_c B, `∀_c C, (A ∨ B) ∨ C ⇔ A ∨ B ∨ C) ≔ 
begin
    refine fa_i_c (λ A, `∀_c B, `∀_c C, (A ∨ B) ∨ C ⇔ A ∨ B ∨ C) _;
    assume A;
    refine fa_i_c (λ B, `∀_c C, (A ∨ B) ∨ C ⇔ A ∨ B ∨ C) _;
    assume B;
    refine fa_i_c (λ C, (A ∨ B) ∨ C ⇔ A ∨ B ∨ C) _;
    assume C;
    refine and_i_c ((A ∨ B) ∨ C ⇒ A ∨ (B ∨ C)) (A ∨ (B ∨ C) ⇒ (A ∨ B) ∨ C) _ _ 
    {refine imp_i_c ((A ∨ B) ∨ C) (A ∨ (B ∨ C)) _;
    assume pABC;
    refine or_e_c (A ∨ B) C pABC (A ∨ B ∨ C) _ _ 
    {assume pAB;
    refine or_e_c A B pAB (A ∨ B ∨ C) _ _ 
    {assume pA;
    refine or_i_l_c A pA (B ∨ C)}
    {assume pB;
    refine or_i_r_c (B ∨ C) (or_i_l_c B pB C) A}}
    {assume pC;
    refine or_i_r_c (B ∨ C) (or_i_r_c C pC B) A}}
    {refine imp_i_c (A ∨ (B ∨ C)) ((A ∨ B) ∨ C) _;
    assume pABC;
    refine or_e_c A (B ∨ C) pABC ((A ∨ B) ∨ C) _ _ 
    {assume pA;
    refine or_i_l_c (A ∨ B) (or_i_l_c A pA B) C}
    {assume pBC;
    refine or_e_c B C pBC ((A ∨ B) ∨ C) _ _ 
    {assume pB;
    refine or_i_l_c (A ∨ B) (or_i_r_c B pB A) C}
    {assume pC;
    refine or_i_r_c C pC (A ∨ B)}}}
end;

opaque symbol iff_refl : Prf ¬ ¬ (`∀_c A, A ⇔ A) ≔ 
begin
    refine fa_i_c (λ A, A ⇔ A) _;
    assume A;
    refine and_i_c (A ⇒ A) (A ⇒ A) _ _ 
    {refine fa_e_c (λ P, P ⇒ P) imp_refl A}
    {refine fa_e_c (λ P, P ⇒ P) imp_refl A}
end;

opaque symbol iff_trans : Prf ¬ ¬ (`∀_c A, `∀_c B, `∀_c C, ((A ⇔ B) ∧ (B ⇔ C)) ⇒ (A ⇔ C)) ≔ 
begin
    refine fa_i_c (λ A, `∀_c B, `∀_c C, ((A ⇔ B) ∧ (B ⇔ C)) ⇒ (A ⇔ C)) _;
    assume A;
    refine fa_i_c (λ B, `∀_c C, ((A ⇔ B) ∧ (B ⇔ C)) ⇒ (A ⇔ C)) _;
    assume B;
    refine fa_i_c (λ C, ((A ⇔ B) ∧ (B ⇔ C)) ⇒ (A ⇔ C)) _;
    assume C;
    refine imp_i_c ((A ⇔ B) ∧ (B ⇔ C)) (A ⇔ C) _;
    assume pABBC;
    refine and_i_c (A ⇒ C) (C ⇒ A) _ _ 
    {refine imp_i_c A C _;
    assume pA;
    refine imp_e_c B C (and_e_l_c (B ⇒ C) (C ⇒ B) (and_e_r_c (A ⇔ B) (B ⇔ C) pABBC)) _;
    refine imp_e_c A B (and_e_l_c (A ⇒ B) (B ⇒ A) (and_e_l_c (A ⇔ B) (B ⇔ C) pABBC)) pA}
    {refine imp_i_c C A _;
    assume pC;
    refine imp_e_c B A (and_e_r_c (A ⇒ B) (B ⇒ A)  (and_e_l_c (A ⇔ B) (B ⇔ C) pABBC)) _;
    refine imp_e_c C B (and_e_r_c (B ⇒ C) (C ⇒ B) (and_e_r_c (A ⇔ B) (B ⇔ C) pABBC)) pC}
end;

opaque symbol iff_sym : Prf ¬ ¬ (`∀_c A, A ⇔ A) ≔ 
begin
    refine fa_i_c (λ A, A ⇔ A) _;
    assume A;
    refine and_i_c (A ⇒ A) (A ⇒ A) _ _ 
    {refine fa_e_c (λ P, P ⇒ P) imp_refl A}
    {refine fa_e_c (λ P, P ⇒ P) imp_refl A}
end;