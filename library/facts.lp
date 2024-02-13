require open Construkti.logic;


// Some results about logical connectives

opaque symbol imp_refl : Prf (`∀ A, A ⇒ A) ≔ 
begin
    refine all_i (λ A, A ⇒ A) _;
    assume A;
    refine imp_i A A _;
    assume pA;
    refine pA
end;

opaque symbol imp_trans : Prf (`∀ A, `∀ B, `∀ C, ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)) ≔ 
begin
    refine all_i (λ A, `∀ B, `∀ C, ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)) _;
    assume A;
    refine all_i (λ B, `∀ C, ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)) _;
    assume B;
    refine all_i (λ C, ((A ⇒ B) ∧ (B ⇒ C)) ⇒ (A ⇒ C)) _;
    assume C;
    refine imp_i ((A ⇒ B) ∧ (B ⇒ C)) (A ⇒ C) _;
    assume pABBC;
    refine imp_i A C _;
    assume pA;
    refine imp_e B C (and_er (A ⇒ B) (B ⇒ C) pABBC) _;
    refine imp_e A B (and_el (A ⇒ B) (B ⇒ C) pABBC) pA;
end;

opaque symbol and_comm : Prf (`∀ A, `∀ B, (A ∧ B) ⇒ (B ∧ A)) ≔ 
begin
    refine all_i (λ A, `∀ B, (A ∧ B) ⇒ (B ∧ A)) _;
    assume A;
    refine all_i (λ B, (A ∧ B) ⇒ (B ∧ A)) _;
    assume B; 
    refine imp_i (A ∧ B) (B ∧ A) _;
    assume pAB;
    refine and_i B _ A _
    {refine and_er A B pAB}
    {refine and_el A B pAB}
end;

opaque symbol and_assoc : Prf (`∀ A, `∀ B, `∀ C, (A ∧ B) ∧ C ⇔ A ∧ B ∧ C) ≔ 
begin
    refine all_i (λ A, `∀ B, `∀ C, (A ∧ B) ∧ C ⇔ A ∧ B ∧ C) _;
    assume A;
    refine all_i (λ B, `∀ C, (A ∧ B) ∧ C ⇔ A ∧ B ∧ C) _;
    assume B;
    refine all_i (λ C, (A ∧ B) ∧ C ⇔ A ∧ B ∧ C) _;
    assume C;
    refine and_i ((A ∧ B) ∧ C ⇒ A ∧ (B ∧ C)) _ (A ∧ (B ∧ C) ⇒ (A ∧ B) ∧ C) _ 
    {refine imp_i ((A ∧ B) ∧ C) (A ∧ (B ∧ C)) _;
    assume pABC;
    refine and_i A _ (B ∧ C) _ 
    {refine and_el A B (and_el (A ∧ B) C pABC)}
    {refine and_i B _ C _ 
    {refine and_er A B (and_el (A ∧ B) C pABC)}
    {refine and_er (A ∧ B) C pABC}}}
    {refine imp_i (A ∧ (B ∧ C)) ((A ∧ B) ∧ C) _;
    assume pABC;
    refine and_i (A ∧ B) _ C _ 
    {refine and_i A _ B _
    {refine and_el A (B ∧ C) pABC}
    {refine and_el B C (and_er A (B ∧ C) pABC)}}
    {refine and_er B C (and_er A (B ∧ C) pABC)}}
end;

opaque symbol prop_and : Prf (`∀ A, `∀ B, `∃ P, (P ⇒ A) ∧ (P ⇒ B)) ≔ 
begin
    refine all_i (λ A, `∀ B, `∃ P, (P ⇒ A) ∧ (P ⇒ B)) _;
    assume A;
    refine all_i (λ B, `∃ P, (P ⇒ A) ∧ (P ⇒ B)) _;
    assume B;
    apply ex_i (λ P, (P ⇒ A) ∧ (P ⇒ B)) (A ∧ B) _;
    apply and_i ((A ∧ B) ⇒ A) _ ((A ∧ B) ⇒ B) _
    {refine imp_i (A ∧ B) A _;
    assume pAB;
    apply and_el A B pAB}
    {refine imp_i (A ∧ B) B _;
    assume pAB;
    apply and_er A B pAB}
end;

opaque symbol or_comm : Prf (`∀ A, `∀ B, (A ∨ B) ⇒ (B ∨ A)) ≔ 
begin
    refine all_i (λ A, `∀ B, (A ∨ B) ⇒ (B ∨ A)) _;
    assume A;
    refine all_i (λ B, (A ∨ B) ⇒ (B ∨ A)) _;
    assume B; 
    refine imp_i (A ∨ B) (B ∨ A) _;
    assume pAB;
    refine or_e A B pAB (B ∨ A) _ _
    {assume pA;
    refine or_ir B A pA}
    {assume pB;
    refine or_il B pB A}
end;

opaque symbol or_assoc : Prf (`∀ A, `∀ B, `∀ C, (A ∨ B) ∨ C ⇔ A ∨ B ∨ C) ≔ 
begin
    refine all_i (λ A, `∀ B, `∀ C, (A ∨ B) ∨ C ⇔ A ∨ B ∨ C) _;
    assume A;
    refine all_i (λ B, `∀ C, (A ∨ B) ∨ C ⇔ A ∨ B ∨ C) _;
    assume B;
    refine all_i (λ C, (A ∨ B) ∨ C ⇔ A ∨ B ∨ C) _;
    assume C;
    refine and_i ((A ∨ B) ∨ C ⇒ A ∨ (B ∨ C)) _ (A ∨ (B ∨ C) ⇒ (A ∨ B) ∨ C) _ 
    {refine imp_i ((A ∨ B) ∨ C) (A ∨ (B ∨ C)) _;
    assume pABC;
    refine or_e (A ∨ B) C pABC (A ∨ B ∨ C) _ _ 
    {assume pAB;
    refine or_e A B pAB (A ∨ B ∨ C) _ _ 
    {assume pA;
    refine or_il A pA (B ∨ C)}
    {assume pB;
    refine or_ir A (B ∨ C) (or_il B pB C)}}
    {assume pC;
    refine or_ir A (B ∨ C) (or_ir B C pC)}}
    {refine imp_i (A ∨ (B ∨ C)) ((A ∨ B) ∨ C) _;
    assume pABC;
    refine or_e A (B ∨ C) pABC ((A ∨ B) ∨ C) _ _ 
    {assume pA;
    refine or_il (A ∨ B) (or_il A pA B) C}
    {assume pBC;
    refine or_e B C pBC ((A ∨ B) ∨ C) _ _ 
    {assume pB;
    refine or_il (A ∨ B) (or_ir A B pB) C}
    {assume pC;
    refine or_ir (A ∨ B) C pC}}}
end;

opaque symbol iff_refl : Prf (`∀ A, A ⇔ A) ≔ 
begin
    refine all_i (λ A, A ⇔ A) _;
    assume A;
    refine and_i (A ⇒ A) _ (A ⇒ A) _ 
    {refine all_e (λ P, P ⇒ P) imp_refl A}
    {refine all_e (λ P, P ⇒ P) imp_refl A}
end;

opaque symbol iff_trans : Prf (`∀ A, `∀ B, `∀ C, ((A ⇔ B) ∧ (B ⇔ C)) ⇒ (A ⇔ C)) ≔ 
begin
    refine all_i (λ A, `∀ B, `∀ C, ((A ⇔ B) ∧ (B ⇔ C)) ⇒ (A ⇔ C)) _;
    assume A;
    refine all_i (λ B, `∀ C, ((A ⇔ B) ∧ (B ⇔ C)) ⇒ (A ⇔ C)) _;
    assume B;
    refine all_i (λ C, ((A ⇔ B) ∧ (B ⇔ C)) ⇒ (A ⇔ C)) _;
    assume C;
    refine imp_i ((A ⇔ B) ∧ (B ⇔ C)) (A ⇔ C) _;
    assume pABBC;
    refine and_i (A ⇒ C) _ (C ⇒ A) _ 
    {refine imp_i A C _;
    assume pA;
    refine imp_e B C (and_el (B ⇒ C) (C ⇒ B) (and_er (A ⇔ B) (B ⇔ C) pABBC)) _;
    refine imp_e A B (and_el (A ⇒ B) (B ⇒ A) (and_el (A ⇔ B) (B ⇔ C) pABBC)) pA}
    {refine imp_i C A _;
    assume pC;
    refine imp_e B A (and_er (A ⇒ B) (B ⇒ A)  (and_el (A ⇔ B) (B ⇔ C) pABBC)) _;
    refine imp_e C B (and_er (B ⇒ C) (C ⇒ B) (and_er (A ⇔ B) (B ⇔ C) pABBC)) pC}
end;

opaque symbol iff_sym : Prf (`∀ A, A ⇔ A) ≔ 
begin
    refine all_i (λ A, A ⇔ A) _;
    assume A;
    refine and_i (A ⇒ A) _ (A ⇒ A) _ 
    {refine all_e (λ P, P ⇒ P) imp_refl A}
    {refine all_e (λ P, P ⇒ P) imp_refl A}
end;
