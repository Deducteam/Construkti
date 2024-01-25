require open Construkti.logic;


// Some results about logical connectives

opaque symbol imp_refl : Prf (`∀ A, A ⇒ A) ≔ 
begin
    refine fa_i (λ A, A ⇒ A) _;
    assume A;
    refine imp_i A A _;
    assume pA;
    refine pA
end;

opaque symbol imp_trans : Prf (`∀ A, `∀ B, `∀ C, ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)) ≔ 
begin
    refine fa_i (λ A, `∀ B, `∀ C, ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)) _;
    assume A;
    refine fa_i (λ B, `∀ C, ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)) _;
    assume B;
    refine fa_i (λ C, ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)) _;
    assume C;
    refine imp_i ((A ⇒ B) ∧ (B ⇒ C)) (A ⇒ C) _;
    assume pABBC;
    refine imp_i A C _;
    assume pA;
    refine imp_e B C (and_e_r (A ⇒ B) (B ⇒ C) pABBC) _;
    refine imp_e A B (and_e_l (A ⇒ B) (B ⇒ C) pABBC) pA;
end;

opaque symbol and_comm : Prf (`∀ A, `∀ B, (A ∧ B) ⇒ (B ∧ A)) ≔ 
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

opaque symbol and_assoc : Prf (`∀ A, `∀ B, `∀ C, (A ∧ B) ∧ C ⇔ A ∧ B ∧ C) ≔ 
begin
    refine fa_i (λ A, `∀ B, `∀ C, (A ∧ B) ∧ C ⇔ A ∧ B ∧ C) _;
    assume A;
    refine fa_i (λ B, `∀ C, (A ∧ B) ∧ C ⇔ A ∧ B ∧ C) _;
    assume B;
    refine fa_i (λ C, (A ∧ B) ∧ C ⇔ A ∧ B ∧ C) _;
    assume C;
    refine and_i ((A ∧ B) ∧ C ⇒ A ∧ (B ∧ C)) (A ∧ (B ∧ C) ⇒ (A ∧ B) ∧ C) _ _ 
    {refine imp_i ((A ∧ B) ∧ C) (A ∧ (B ∧ C)) _;
    assume pABC;
    refine and_i A (B ∧ C) _ _ 
    {refine and_e_l A B (and_e_l (A ∧ B) C pABC)}
    {refine and_i B C _ _ 
    {refine and_e_r A B (and_e_l (A ∧ B) C pABC)}
    {refine and_e_r (A ∧ B) C pABC}}}
    {refine imp_i (A ∧ (B ∧ C)) ((A ∧ B) ∧ C) _;
    assume pABC;
    refine and_i (A ∧ B) C _ _ 
    {refine and_i A B _ _
    {refine and_e_l A (B ∧ C) pABC}
    {refine and_e_l B C (and_e_r A (B ∧ C) pABC)}}
    {refine and_e_r B C (and_e_r A (B ∧ C) pABC)}}
end;

opaque symbol prop_and : Prf (`∀ A, `∀ B, `∃ P, (P ⇒ A) ∧ (P ⇒ B)) ≔ 
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

opaque symbol or_comm : Prf (`∀ A, `∀ B, (A ∨ B) ⇒ (B ∨ A)) ≔ 
begin
    refine fa_i (λ A, `∀ B, (A ∨ B) ⇒ (B ∨ A)) _;
    assume A;
    refine fa_i (λ B, (A ∨ B) ⇒ (B ∨ A)) _;
    assume B; 
    refine imp_i (A ∨ B) (B ∨ A) _;
    assume pAB;
    refine or_e A B pAB (B ∨ A) _ _
    {assume pA;
    refine or_i_r A pA B}
    {assume pB;
    refine or_i_l B pB A}
end;

opaque symbol or_assoc : Prf (`∀ A, `∀ B, `∀ C, (A ∨ B) ∨ C ⇔ A ∨ B ∨ C) ≔ 
begin
    refine fa_i (λ A, `∀ B, `∀ C, (A ∨ B) ∨ C ⇔ A ∨ B ∨ C) _;
    assume A;
    refine fa_i (λ B, `∀ C, (A ∨ B) ∨ C ⇔ A ∨ B ∨ C) _;
    assume B;
    refine fa_i (λ C, (A ∨ B) ∨ C ⇔ A ∨ B ∨ C) _;
    assume C;
    refine and_i ((A ∨ B) ∨ C ⇒ A ∨ (B ∨ C)) (A ∨ (B ∨ C) ⇒ (A ∨ B) ∨ C) _ _ 
    {refine imp_i ((A ∨ B) ∨ C) (A ∨ (B ∨ C)) _;
    assume pABC;
    refine or_e (A ∨ B) C pABC (A ∨ B ∨ C) _ _ 
    {assume pAB;
    refine or_e A B pAB (A ∨ B ∨ C) _ _ 
    {assume pA;
    refine or_i_l A pA (B ∨ C)}
    {assume pB;
    refine or_i_r (B ∨ C) (or_i_l B pB C) A}}
    {assume pC;
    refine or_i_r (B ∨ C) (or_i_r C pC B) A}}
    {refine imp_i (A ∨ (B ∨ C)) ((A ∨ B) ∨ C) _;
    assume pABC;
    refine or_e A (B ∨ C) pABC ((A ∨ B) ∨ C) _ _ 
    {assume pA;
    refine or_i_l (A ∨ B) (or_i_l A pA B) C}
    {assume pBC;
    refine or_e B C pBC ((A ∨ B) ∨ C) _ _ 
    {assume pB;
    refine or_i_l (A ∨ B) (or_i_r B pB A) C}
    {assume pC;
    refine or_i_r C pC (A ∨ B)}}}
end;

opaque symbol iff_refl : Prf (`∀ A, A ⇔ A) ≔ 
begin
    refine fa_i (λ A, A ⇔ A) _;
    assume A;
    refine and_i (A ⇒ A) (A ⇒ A) _ _ 
    {refine fa_e (λ P, P ⇒ P) imp_refl A}
    {refine fa_e (λ P, P ⇒ P) imp_refl A}
end;

opaque symbol iff_trans : Prf (`∀ A, `∀ B, `∀ C, ((A ⇔ B) ∧ (B ⇔ C)) ⇒ (A ⇔ C)) ≔ 
begin
    refine fa_i (λ A, `∀ B, `∀ C, ((A ⇔ B) ∧ (B ⇔ C)) ⇒ (A ⇔ C)) _;
    assume A;
    refine fa_i (λ B, `∀ C, ((A ⇔ B) ∧ (B ⇔ C)) ⇒ (A ⇔ C)) _;
    assume B;
    refine fa_i (λ C, ((A ⇔ B) ∧ (B ⇔ C)) ⇒ (A ⇔ C)) _;
    assume C;
    refine imp_i ((A ⇔ B) ∧ (B ⇔ C)) (A ⇔ C) _;
    assume pABBC;
    refine and_i (A ⇒ C) (C ⇒ A) _ _ 
    {refine imp_i A C _;
    assume pA;
    refine imp_e B C (and_e_l (B ⇒ C) (C ⇒ B) (and_e_r (A ⇔ B) (B ⇔ C) pABBC)) _;
    refine imp_e A B (and_e_l (A ⇒ B) (B ⇒ A) (and_e_l (A ⇔ B) (B ⇔ C) pABBC)) pA}
    {refine imp_i C A _;
    assume pC;
    refine imp_e B A (and_e_r (A ⇒ B) (B ⇒ A)  (and_e_l (A ⇔ B) (B ⇔ C) pABBC)) _;
    refine imp_e C B (and_e_r (B ⇒ C) (C ⇒ B) (and_e_r (A ⇔ B) (B ⇔ C) pABBC)) pC}
end;

opaque symbol iff_sym : Prf (`∀ A, A ⇔ A) ≔ 
begin
    refine fa_i (λ A, A ⇔ A) _;
    assume A;
    refine and_i (A ⇒ A) (A ⇒ A) _ _ 
    {refine fa_e (λ P, P ⇒ P) imp_refl A}
    {refine fa_e (λ P, P ⇒ P) imp_refl A}
end;
