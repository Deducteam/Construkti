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

symbol iff_i : Π (A B : Prop), Prf(A ⇒ B) → Prf (B ⇒ A) → Prf (A ⇔ B) ≔ 
begin
    assume A B pAB pBA;
    refine and_i (A ⇒ B) pAB (B ⇒ A) pBA
end;

symbol iff_el : Π (A B : Prop), Prf (A ⇔ B) → Prf (A ⇒ B) ≔ 
begin
    assume A B pAB;
    refine and_el (A ⇒ B) (B ⇒ A) pAB
end;

symbol iff_er : Π (A B : Prop), Prf (A ⇔ B) → Prf (B ⇒ A) ≔ 
begin
    assume A B pAB;
    refine and_er (A ⇒ B) (B ⇒ A) pAB
end;

opaque symbol iff_refl_rule : Π A : Prop, Prf (A ⇔ A) ≔ 
begin
    assume A;
    refine and_i (A ⇒ A) _ (A ⇒ A) _ 
    {refine all_e (λ P, P ⇒ P) imp_refl A}
    {refine all_e (λ P, P ⇒ P) imp_refl A}
end;

opaque symbol iff_refl : Prf (`∀ A, A ⇔ A) ≔ 
begin
    refine all_i (λ A, A ⇔ A) _;
    assume A;
    refine iff_refl_rule A
end;

opaque symbol iff_trans_rule : Π (A B C : Prop), Prf (A ⇔ B) → Prf (B ⇔ C) → Prf (A ⇔ C) ≔ 
begin
    assume A B C pAB pBC;
    refine and_i (A ⇒ C) _ (C ⇒ A) _ 
    {refine imp_i A C _;
    assume pA;
    refine imp_e B C (and_el (B ⇒ C) (C ⇒ B) pBC) _;
    refine imp_e A B (and_el (A ⇒ B) (B ⇒ A) pAB) pA}
    {refine imp_i C A _;
    assume pC;
    refine imp_e B A (and_er (A ⇒ B) (B ⇒ A)  pAB) _;
    refine imp_e C B (and_er (B ⇒ C) (C ⇒ B) pBC) pC}
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
    refine iff_trans_rule A B C (and_el (A ⇔ B) (B ⇔ C) pABBC) (and_er (A ⇔ B) (B ⇔ C) pABBC)
end;

opaque symbol iff_sym_rule : Π (A B : Prop), Prf (A ⇔ B) → Prf (B ⇔ A) ≔ 
begin
    assume A B pAB;
    refine and_i (B ⇒ A) _ (A ⇒ B) _ 
    {refine and_er (A ⇒ B) (B ⇒ A) pAB}
    {refine and_el (A ⇒ B) (B ⇒ A) pAB}
end;

opaque symbol iff_sym : Prf (`∀ A, `∀ B, (A ⇔ B) ⇒ (B ⇔ A)) ≔ 
begin
    refine all_i (λ A, `∀ B, (A ⇔ B) ⇒ (B ⇔ A)) _;
    assume A;
    refine all_i (λ B, (A ⇔ B) ⇒ (B ⇔ A)) _;
    assume B;
    refine imp_i (A ⇔ B) (B ⇔ A) _;
    assume pAB;
    refine iff_sym_rule A B pAB
end;

opaque symbol iff_and : Π (A A' B B' : Prop), Prf (A ⇔ A') → Prf (B ⇔ B') → Prf ((A ∧ B) ⇔ (A' ∧ B')) ≔ 
begin
    assume A A' B B' pAA' pBB';
    refine and_i ((A ∧ B) ⇒ (A' ∧ B')) _ ((A' ∧ B') ⇒ (A ∧ B)) _ 
    {refine imp_i (A ∧ B) (A' ∧ B') _;
    assume pAB;
    refine and_i A' _ B' _ 
    {refine imp_e A A' (and_el (A ⇒ A') (A' ⇒ A) pAA') (and_el A B pAB)}
    {refine imp_e B B' (and_el (B ⇒ B') (B' ⇒ B) pBB') (and_er A B pAB)}}
    {refine imp_i (A' ∧ B') (A ∧ B) _;
    assume pAB';
    refine and_i A _ B _ 
    {refine imp_e A' A (and_er (A ⇒ A') (A' ⇒ A) pAA') (and_el A' B' pAB')}
    {refine imp_e B' B (and_er (B ⇒ B') (B' ⇒ B) pBB') (and_er A' B' pAB')}}
end;

opaque symbol iff_or : Π (A A' B B' : Prop), Prf (A ⇔ A') → Prf (B ⇔ B') → Prf ((A ∨ B) ⇔ (A' ∨ B')) ≔ 
begin
    assume A A' B B' pAA' pBB';
    refine and_i ((A ∨ B) ⇒ (A' ∨ B')) _ ((A' ∨ B') ⇒ (A ∨ B)) _ 
    {refine imp_i (A ∨ B) (A' ∨ B') _;
    assume pAB;
    refine or_e A B pAB (A' ∨ B') _ _ 
    {assume pA;
    refine or_il A' _ B';
    refine imp_e A A' (and_el (A ⇒ A') (A' ⇒ A) pAA') pA}
    {assume pB;
    refine or_ir A' B' _;
    refine imp_e B B' (and_el (B ⇒ B') (B' ⇒ B) pBB') pB}}
    {refine imp_i (A' ∨ B') (A ∨ B) _;
    assume pAB';
    refine or_e A' B' pAB' (A ∨ B) _ _ 
    {assume pA';
    refine or_il A _ B;
    refine imp_e A' A (and_er (A ⇒ A') (A' ⇒ A) pAA') pA'}
    {assume pB';
    refine or_ir A B _;
    refine imp_e B' B (and_er (B ⇒ B') (B' ⇒ B) pBB') pB'}}
end;

opaque symbol iff_imp : Π (A A' B B' : Prop), Prf (A ⇔ A') → Prf (B ⇔ B') → Prf ((A ⇒ B) ⇔ (A' ⇒ B')) ≔ 
begin
    assume A A' B B' pAA' pBB';
    refine and_i ((A ⇒ B) ⇒ (A' ⇒ B')) _ ((A' ⇒ B') ⇒ (A ⇒ B)) _ 
    {refine imp_i (A ⇒ B) (A' ⇒ B') _;
    assume pAB;
    refine imp_i  A' B' _;
    assume pA';
    refine imp_e B B' (and_el (B ⇒ B') (B' ⇒ B) pBB') _;
    refine imp_e A B  pAB _;
    refine imp_e A' A (and_er (A ⇒ A') (A' ⇒ A) pAA') pA'}
    {refine imp_i (A' ⇒ B') (A ⇒ B) _;
    assume pAB';
    refine imp_i  A B _;
    assume pA;
    refine imp_e B' B (and_er (B ⇒ B') (B' ⇒ B) pBB') _;
    refine imp_e A' B'  pAB' _;
    refine imp_e A A' (and_el (A ⇒ A') (A' ⇒ A) pAA') pA}
end;

opaque symbol iff_neg : Π (A A' : Prop), Prf (A ⇔ A') → Prf ((¬ A) ⇔ (¬ A')) ≔ 
begin
    assume A A' pAA';
    refine and_i ((¬ A) ⇒ (¬ A')) _ ((¬ A') ⇒ (¬ A)) _ 
    {refine imp_i (¬ A) (¬ A') _;
    assume pNA;
    refine neg_i A' _;
    assume pA';
    refine neg_e A pNA _;
    refine imp_e A' A (and_er (A ⇒ A') (A' ⇒ A) pAA') pA'}
    {refine imp_i (¬ A') (¬ A) _;
    assume pNA';
    refine neg_i A _;
    assume pA;
    refine neg_e A' pNA' _;
    refine imp_e A A' (and_el (A ⇒ A') (A' ⇒ A) pAA') pA}
end;

opaque symbol iff_all : Π a : Set, Π (A A' : El a → Prop), (Π x : El a, Prf (A x ⇔ A' x)) → Prf ((∀ A) ⇔ (∀ A')) ≔ 
begin
    assume a A A' pAA';
    refine and_i ((∀ A) ⇒ (∀ A')) _ ((∀ A') ⇒ (∀ A)) _ 
    {refine imp_i (∀ A) (∀ A') _;
    assume pFA;
    refine all_i A' _;
    assume x;
    refine imp_e (A x) (A' x) (and_el (A x ⇒ A' x) (A' x ⇒ A x) (pAA' x)) _;
    refine all_e A pFA x}
    {refine imp_i (∀ A') (∀ A) _;
    assume pFA';
    refine all_i A _;
    assume x;
    refine imp_e (A' x) (A x) (and_er (A x ⇒ A' x) (A' x ⇒ A x) (pAA' x)) _;
    refine all_e A' pFA' x}
end;

opaque symbol iff_ex : Π a : Set, Π (A A' : El a → Prop), (Π x : El a, Prf (A x ⇔ A' x)) → Prf ((∃ A) ⇔ (∃ A')) ≔ 
begin
    assume a A A' pAA';
    refine and_i ((∃ A) ⇒ (∃ A')) _ ((∃ A') ⇒ (∃ A)) _ 
    {refine imp_i (∃ A) (∃ A') _;
    assume pEA;
    refine ex_e A pEA (∃ A') _;
    assume t pAt;
    refine ex_i A' t _;
    refine imp_e (A t) (A' t) (and_el (A t ⇒ A' t) (A' t ⇒ A t) (pAA' t)) pAt}
    {refine imp_i (∃ A') (∃ A) _;
    assume pEA';
    refine ex_e A' pEA' (∃ A) _;
    assume t pAt';
    refine ex_i A t _;
    refine imp_e (A' t) (A t) (and_er (A t ⇒ A' t) (A' t ⇒ A t) (pAA' t)) pAt'}
end;

opaque symbol iff_iff : Π (A A' B B' : Prop), Prf (A ⇔ A') → Prf (B ⇔ B') → Prf ((A ⇔ B) ⇔ (A' ⇔ B')) ≔ 
begin
    assume A A' B B' pAA' pBB';
    refine and_i ((A ⇔ B) ⇒ (A' ⇔ B')) _ ((A' ⇔ B') ⇒ (A ⇔ B)) _ 
    {refine imp_i (A ⇔ B) (A' ⇔ B') _;
    assume pAB;
    refine and_i (A' ⇒ B') _ (B' ⇒ A') _ 
    {refine imp_i A' B' _;
    assume pA';
    refine imp_e B B' (and_el (B ⇒ B') (B' ⇒ B) pBB') _;
    refine imp_e A B (and_el (A ⇒ B) (B ⇒ A) pAB) _;
    refine imp_e A' A (and_er (A ⇒ A') (A' ⇒ A) pAA') pA'}
    {refine imp_i B' A' _;
    assume pB';
    refine imp_e A A' (and_el (A ⇒ A') (A' ⇒ A) pAA') _;
    refine imp_e B A (and_er (A ⇒ B) (B ⇒ A) pAB) _;
    refine imp_e B' B (and_er (B ⇒ B') (B' ⇒ B) pBB') pB'}}
    {refine imp_i (A' ⇔ B') (A ⇔ B) _;
    assume pAB';
    refine and_i (A ⇒ B) _ (B ⇒ A) _ 
    {refine imp_i A B _;
    assume pA;
    refine imp_e B' B (and_er (B ⇒ B') (B' ⇒ B) pBB') _;
    refine imp_e A' B' (and_el (A' ⇒ B') (B' ⇒ A') pAB') _;
    refine imp_e A A' (and_el (A ⇒ A') (A' ⇒ A) pAA') pA}
    {refine imp_i B A _;
    assume pB;
    refine imp_e A' A (and_er (A ⇒ A') (A' ⇒ A) pAA') _;
    refine imp_e B' A' (and_er (A' ⇒ B') (B' ⇒ A') pAB') _;
    refine imp_e B B' (and_el (B ⇒ B') (B' ⇒ B) pBB') pB}}
end;

opaque symbol double_neg : Π A : Prop, Prf (A ⇒ ¬ ¬ A) ≔ 
begin
    assume A;
    refine imp_i A (¬ ¬ A) _;
    assume pA;
    refine neg_i (¬ A) _;
    assume pNA;
    refine neg_e A _ _ 
    {refine pNA}
    {refine pA}
end;

opaque symbol neg_imp : Π (p q : Prop), Prf ((p ⇒ q) ⇒ (¬ q ⇒ ¬ p)) ≔ 
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

opaque symbol neg_imp1 : Π (p q : Prop), Prf ((¬ ¬ p ⇒ ¬ ¬ q) ⇒ ¬ ¬ (p ⇒ q)) ≔ 
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
    refine imp_e p (¬ ¬ p) (double_neg p) pP}
    {refine neg_i q _;
    assume pQ;
    refine neg_e (p ⇒ q) _ _ 
    {refine pNPQ}
    {refine imp_i p q _;
    assume pP2;
    apply pQ}}}
end;

opaque symbol neg_imp2 : Π (p q : Prop), Prf (¬ ¬ (p ⇒ q) ⇒ (¬ ¬ p ⇒ ¬ ¬ q)) ≔ 
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

opaque symbol neg_and1 : Π (p q : Prop), Prf ((¬ ¬ p ∧ ¬ ¬ q) ⇒ ¬ ¬ (p ∧ q)) ≔ 
begin
    assume p q;
    refine imp_i (¬ ¬ p ∧ ¬ ¬ q) (¬ ¬ (p ∧ q)) _;
    assume pNNPQ;
    refine neg_i (¬ (p ∧ q)) _;
    assume pNPQ;
    refine neg_e (¬ q) _ _
    {refine and_er (¬ (¬ p)) (¬ (¬ q)) pNNPQ}
    {refine neg_i q _;
    assume pQ;
    refine neg_e (¬ p) _ _
    {refine and_el (¬ (¬ p)) (¬ (¬ q)) pNNPQ}
    {refine neg_i p _;
    assume pP;
    refine neg_e (p ∧ q) _ _
    {refine pNPQ}
    {refine and_i p pP q pQ}}}
end;

opaque symbol neg_and2 : Π (p q : Prop), Prf (¬ ¬ (p ∧ q) ⇒ (¬ ¬ p ∧ ¬ ¬ q)) ≔ 
begin
    assume p q; 
    refine imp_i (¬ ¬ (p ∧ q)) (¬ ¬ p ∧ ¬ ¬ q) _;
    assume pNNPQ;
    refine and_i (¬ ¬ p) _ (¬ ¬ q) _
    {refine neg_i (¬ p) _;
    assume pNP;
    refine neg_e (¬ (p ∧ q)) _ _ 
    {refine pNNPQ}
    {refine neg_i (p ∧ q) _;
    assume pPQ;
    refine neg_e p _ _ 
    {refine pNP}
    {apply and_el p q pPQ}}}
    {refine neg_i (¬ q) _;
    assume pNQ;
    refine neg_e (¬ (p ∧ q)) _ _ 
    {refine pNNPQ}
    {refine neg_i (p ∧ q) _;
    assume pPQ;
    refine neg_e q _ _ 
    {refine pNQ}
    {apply and_er p q pPQ}}}
end;

opaque symbol neg_or1 : Π (p q : Prop), Prf (¬ (p ∨ q) ⇒ (¬ p ∧ ¬ q)) ≔ 
begin
    assume p q;
    refine imp_i (¬ (p ∨ q)) (¬ p ∧ ¬ q) _;
    assume pNPQ;
    refine and_i (¬ p) _ (¬ q) _
    {refine neg_i p _;
    assume pP;
    refine neg_e (p ∨ q) _ _ 
    {refine pNPQ}
    {apply or_il p pP q}}
    {refine neg_i q _;
    assume pQ;
    refine neg_e (p ∨ q) _ _ 
    {refine pNPQ}
    {apply or_ir p q pQ}}
end;

opaque symbol neg_or2 : Π (p q : Prop), Prf ((¬ p ∧ ¬ q) ⇒ ¬ (p ∨ q)) ≔ 
begin
    assume p q;
    refine imp_i (¬ p ∧ ¬ q) (¬ (p ∨ q)) _;
    assume pNPQ;
    refine neg_i (p ∨ q) _;
    assume pPQ;
    refine or_e p q pPQ ⊥ _ _ 
    {assume pP;
    refine neg_e p _ pP;
    refine and_el (¬ p) (¬ q) pNPQ}
    {assume pQ;
    refine neg_e q _ pQ;
    refine and_er (¬ p) (¬ q) pNPQ}
end;

opaque symbol neg_all : Π a : Set, Π p : El a → Prop, Prf (¬ ¬ ∀ p ⇒ ∀ (λ x, ¬ ¬ (p x))) ≔ 
begin
    assume a p;
    refine imp_i (¬ ¬ ∀ p) (∀ (λ x, ¬ ¬ (p x))) _;
    assume pNNP;
    refine all_i (λ x, ¬ ¬ (p x)) _;
    assume x;
    refine neg_i (¬ (p x)) _;
    assume pNP;
    refine neg_e (¬ (∀ p)) _ _ 
    {refine pNNP}
    {refine neg_i (∀ p) _;
    assume pP;
    refine neg_e (p x) _ _ 
    {refine pNP}
    {apply all_e  p pP x}}
end;

opaque symbol neg_ex1 : Π a : Set, Π p : El a → Prop, Prf (¬ ∃ p ⇒ ∀ (λ x, ¬ (p x))) ≔ 
begin
    assume a p;
    refine imp_i (¬ ∃ p) (∀ (λ x, ¬ (p x))) _;
    assume pNP;
    refine all_i (λ x, ¬ (p x)) _;
    assume x;
    refine neg_i (p x) _;
    assume pP;
    refine neg_e (∃ p) _ _ 
    {refine pNP}
    {refine ex_i p x pP}
end;

opaque symbol neg_ex2 : Π a : Set, Π p : El a → Prop, Prf (∀ (λ x, ¬ (p x)) ⇒ ¬ ∃ p) ≔ 
begin
    assume a p;
    refine imp_i (∀ (λ x, ¬ (p x))) (¬ ∃ p) _;
    assume pNP;
    refine neg_i (∃ p) _;
    assume pP;
    refine ex_e p pP ⊥ _;
    assume t pPt;
    refine neg_e (p t) _ _ 
    {refine all_e (λ x, ¬ (p x)) pNP t}
    {refine pPt}
end;

opaque symbol triple_neg : Π p : Prop, Prf (¬ ¬ ¬ p ⇒ ¬ p) ≔ 
begin
    assume p;
    refine imp_i (¬ ¬ ¬ p) (¬ p) _;
    assume pNNNP;
    refine neg_i p _;
    assume pP;
    refine neg_e (¬ ¬ p) _ _ 
    {refine pNNNP}
    {refine imp_e p (¬ ¬ p) (double_neg p) pP}
end;

opaque symbol neg_bot : Prf (¬ ¬ ⊥ ⇒ ⊥) ≔ 
begin
    refine imp_i (¬ ¬ ⊥) ⊥ _;
    assume pB;
    refine neg_e (¬ ⊥) _ _ 
    {refine pB}
    {refine neg_i ⊥ _;
    assume pN; 
    refine pN}
end;

opaque symbol neg_top : Prf (¬ ¬ ⊤ ⇒ ⊤) ≔ 
begin
    refine imp_i (¬ ¬ ⊤) ⊤ _;
    assume pT;
    refine top_i
end;

opaque symbol neg_iff : Π (p q : Prop), Prf ((¬ ¬ p ⇔ ¬ ¬ q) ⇒ ¬ ¬ (p ⇔ q)) ≔ 
begin
    assume p q;
    refine imp_i (¬ ¬ p ⇔ ¬ ¬ q) (¬ ¬ (p ⇔ q)) _;
    assume pH;
    refine imp_e (¬ ¬ (p ⇒ q) ∧ ¬ ¬ (q ⇒ p)) (¬ ¬ ((p ⇒ q) ∧ (q ⇒ p))) (neg_and1 (p ⇒ q) (q ⇒ p)) _;
    refine and_i (¬ ¬ (p ⇒ q)) _ (¬ ¬ (q ⇒ p)) _ 
    {refine imp_e (¬ ¬ p ⇒ ¬ ¬ q) (¬ ¬ (p ⇒ q)) (neg_imp1 p q) _;
    refine and_el (¬ ¬ p ⇒ ¬ ¬ q) (¬ ¬ q ⇒ ¬ ¬ p) pH}
    {refine imp_e (¬ ¬ q ⇒ ¬ ¬ p) (¬ ¬ (q ⇒ p)) (neg_imp1 q p) _;
    refine and_er (¬ ¬ p ⇒ ¬ ¬ q) (¬ ¬ q ⇒ ¬ ¬ p) pH}
end;


// Classical results

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

opaque symbol double_neg_iff : Π A : Prop, Prf (A ⇔ ¬ ¬ A) ≔ 
begin
    assume A;
    refine and_i (A ⇒ (¬ ¬ A)) (double_neg A) ((¬ ¬ A) ⇒ A) (double_neg_elim A)
end;

opaque symbol absurd : Π A : Prop, (Prf (¬ A) → Prf ⊥) → Prf A ≔
begin
    assume A pNPF;
    refine imp_e  (¬ ¬ A) A (double_neg_elim A) _;
    refine neg_i (¬ A) pNPF
end;

opaque symbol clavius : Prf (`∀ A, (¬ A ⇒ A) ⇒ A) ≔
begin
    refine all_i (λ A, (¬ A ⇒ A) ⇒ A) _;
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
    refine all_i (λ A, `∀ B, A ∨ (A ⇒ B)) _;
    assume A;
    refine all_i (λ B, A ∨ (A ⇒ B)) _;
    assume B;
    refine or_e A (¬ A) (excluded_middle A) (A ∨ (A ⇒ B)) _ _ 
    {assume pA;
    refine or_il A _ (A ⇒ B);
    refine pA}
    {assume pNA;
    refine or_ir A (A ⇒ B) _;
    refine imp_i A B _;
    assume pA;
    refine bot_e _ B;
    refine neg_e A pNA pA}
end;

opaque symbol weak_peirce : Prf (`∀ A, ((A ⇒ ⊥) ⇒ A) ⇒ A) ≔
begin
    refine all_i (λ A, ((A ⇒ ⊥) ⇒ A) ⇒ A) _;
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
    refine all_i (λ A, `∀ B, ((A ⇒ B) ⇒ A) ⇒ A) _;
    assume A;
    refine all_i (λ B, ((A ⇒ B) ⇒ A) ⇒ A) _;
    assume B;
    refine imp_i ((A ⇒ B) ⇒ A) A _;
    assume pABA;
    refine imp_e ((A ⇒ ⊥) ⇒ A) A _ _ 
    {refine all_e (λ A, ((A ⇒ ⊥) ⇒ A) ⇒ A) weak_peirce A}
    {refine imp_i (A ⇒ ⊥) A _;
    assume pAF;
    refine imp_e (A ⇒ B) A pABA _;
    refine imp_i A B _;
    assume pA;
    refine bot_e _ B;
    refine imp_e A ⊥ pAF pA}
end;

opaque symbol linearity : Prf (`∀ A, `∀ B, `∀ C, (A ⇒ B) ∨ (B ⇒ C)) ≔ 
begin
    refine all_i (λ A, `∀ B, `∀ C, (A ⇒ B) ∨ (B ⇒ C)) _;
    assume A;
    refine all_i (λ B, `∀ C, (A ⇒ B) ∨ (B ⇒ C)) _;
    assume B;
    refine all_i (λ C, (A ⇒ B) ∨ (B ⇒ C)) _;
    assume C;
    refine or_e B (B ⇒ C) _ ((A ⇒ B) ∨ (B ⇒ C)) _ _
    {refine all_e (λ C, B ∨ (B ⇒ C)) _ C;
    refine (all_e (λ B, `∀ C, B ∨ (B ⇒ C)) tarski B)}
    {assume pB;
    refine or_il (A ⇒ B) _ (B ⇒ C);
    refine imp_i A B _;
    assume pA;
    refine pB}
    {assume pBC;
    refine or_ir (A ⇒ B) (B ⇒ C) pBC}
end;

opaque symbol weak_linearity : Prf (`∀ A, `∀ B, (A ⇒ B) ∨ (B ⇒ A)) ≔ 
begin
    refine all_i (λ A, `∀ B, (A ⇒ B) ∨ (B ⇒ A)) _;
    assume A;
    refine all_i (λ B, (A ⇒ B) ∨ (B ⇒ A)) _;
    assume B;
    refine all_e (λ C, (A ⇒ B) ∨ (B ⇒ C)) _ A;
    refine all_e (λ B, `∀ C, (A ⇒ B) ∨ (B ⇒ C)) _ B;
    refine all_e (λ A, `∀ B, `∀ C, (A ⇒ B) ∨ (B ⇒ C)) linearity A
end;

opaque symbol weak_excluded_middle : Prf (`∀ A, ¬ A ∨ ¬ ¬ A) ≔ 
begin
    refine all_i (λ A, ¬ A ∨ ¬ ¬ A) _;
    assume A;
    refine excluded_middle (¬ A)
end;

opaque symbol non_contradiction : Prf (`∀ A, ¬ (A ∧ ¬ A)) ≔ 
begin
    refine all_i (λ A, ¬ (A ∧ ¬ A)) _;
    assume A;
    refine neg_i (A ∧ ¬ A) _;
    assume pANA;
    refine imp_e A ⊥ _ (and_el A (¬ A) pANA);
    refine imp_i A ⊥ _;
    refine neg_e A (and_er A (¬ A) pANA)
end;

opaque symbol entailment : Prf (`∀ A, `∀ B, (A ∧ ¬ A) ⇒ B) ≔ 
begin
    refine all_i (λ A, `∀ B, (A ∧ ¬ A) ⇒ B) _;
    assume A;
    refine all_i (λ B, (A ∧ ¬ A) ⇒ B) _;
    assume B;
    refine imp_i (A ∧ ¬ A) B _;
    assume pANA;
    refine bot_e _ B;
    refine imp_e A ⊥ _ (and_el A (¬ A) pANA);
    refine imp_i A ⊥ _;
    refine neg_e A (and_er A (¬ A) pANA)
end;


// De Morgan's laws

opaque symbol demorgan_and : Π (A B : Prop), Prf (¬ (A ∧ B) ⇔ ¬ A ∨ ¬ B) ≔
begin
    assume A B;
    refine and_i (¬ (A ∧ B) ⇒ (¬ A ∨ ¬ B)) _ ((¬ A ∨ ¬ B) ⇒ ¬ (A ∧ B)) _ 
    {refine imp_i (¬ (A ∧ B)) (¬ A ∨ ¬ B) _;
    assume pNAB;
    refine imp_e (¬ ¬ (¬ A ∨ ¬ B)) (¬ A ∨ ¬ B) (double_neg_elim (¬ A ∨ ¬ B)) _;
    refine neg_i (¬ (¬ A ∨ ¬ B)) _;
    assume pNNANB;
    refine neg_e (A ∧ B) pNAB _;
    refine and_i A _ B _ 
    {refine imp_e (¬ ¬ A) A (double_neg_elim A) _;
    refine neg_i (¬ A) _;
    assume pNA;
    refine neg_e (¬ A ∨ ¬ B) pNNANB _;
    refine or_il (¬ A) pNA (¬ B)}
    {refine imp_e (¬ ¬ B) B (double_neg_elim B) _;
    refine neg_i (¬ B) _;
    assume pNB;
    refine neg_e (¬ A ∨ ¬ B) pNNANB _;
    refine or_ir (¬ A) (¬ B) pNB}}
    {refine imp_i (¬ A ∨ ¬ B) (¬ (A ∧ B)) _;
    assume pNANB;
    refine neg_i (A ∧ B) _;
    assume pAB;
    refine or_e (¬ A) (¬ B) pNANB ⊥ _ _ 
    {assume pNA;
    refine neg_e A pNA (and_el A B pAB)}
    {assume pNB;
    refine neg_e B pNB (and_er A B pAB)}}
end;

opaque symbol demorgan_or : Π (A B : Prop), Prf (¬ (A ∨ B) ⇔ ¬ A ∧ ¬ B) ≔
begin
    assume A B;
    refine and_i (¬ (A ∨ B) ⇒ (¬ A ∧ ¬ B)) _ ((¬ A ∧ ¬ B) ⇒ ¬ (A ∨ B)) _ 
    {refine neg_or1 A B}
    {refine neg_or2 A B}
end;

opaque symbol demorgan_neg_and : Π (A B : Prop), Prf (¬ (¬ A ∧ ¬ B) ⇔ A ∨ B) ≔
begin
    assume A B;
    refine iff_trans_rule (¬ (¬ A ∧ ¬ B)) (¬ ¬ A ∨ ¬ ¬ B) (A ∨ B) _ _ 
    {refine demorgan_and (¬ A) (¬ B)}
    {refine iff_or (¬ (¬ A)) A (¬ (¬ B)) B _ _ 
    {refine iff_sym_rule A (¬ ¬ A) (double_neg_iff A)}
    {refine iff_sym_rule B (¬ ¬ B) (double_neg_iff B)}}
end;

opaque symbol demorgan_neg_or : Π (A B : Prop), Prf (¬ (¬ A ∨ ¬ B) ⇔ A ∧ B) ≔
begin
    assume A B;
    refine iff_trans_rule (¬ (¬ A ∨ ¬ B)) (¬ ¬ A ∧ ¬ ¬ B) (A ∧ B) _ _ 
    {refine demorgan_or (¬ A) (¬ B)}
    {refine iff_and (¬ (¬ A)) A (¬ (¬ B)) B _ _ 
    {refine iff_sym_rule A (¬ ¬ A) (double_neg_iff A)}
    {refine iff_sym_rule B (¬ ¬ B) (double_neg_iff B)}}
end;

opaque symbol demorgan_all : Π (a : Set), Π (p : El a → Prop), Prf (¬ ∀ p ⇔ ∃ (λ x, ¬ (p x))) ≔ 
begin
    assume a p;
    refine and_i (¬ (∀ p) ⇒ (`∃ x, ¬ (p x))) _ ((`∃ x, ¬ (p x)) ⇒ ¬ (∀ p)) _ 
    {refine imp_i (¬ (∀ p)) (`∃ x, ¬ (p x)) _;
    assume pNFP;
    refine imp_e (¬ ¬ (`∃ x, ¬ (p x))) (`∃ x, ¬ (p x)) (double_neg_elim (`∃ x, ¬ (p x))) _;
    refine neg_i (¬ (`∃ x, ¬ (p x))) _;
    assume pNENP;
    refine neg_e (∀ p) pNFP _;
    refine all_i p _;
    assume t;
    refine imp_e (¬ ¬ (p t)) (p t) (double_neg_elim (p t)) _;
    refine neg_i (¬ (p t)) _;
    assume pNPt;
    refine neg_e (`∃ x, ¬ (p x)) pNENP _;
    refine ex_i  (λ x, ¬ (p x)) t pNPt}
    {refine imp_i (`∃ x, ¬ (p x)) (¬ (∀ p)) _;
    assume pENP;
    refine neg_i (∀ p) _;
    assume pFP;
    refine ex_e (λ x, ¬ (p x)) pENP ⊥ _;
    assume t pNPt;
    refine neg_e (p t) pNPt _;
    refine all_e p pFP t}
end;

opaque symbol demorgan_ex : Π (a : Set), Π (p : El a → Prop), Prf (¬ ∃ p ⇔ ∀ (λ x, ¬ (p x))) ≔ 
begin
    assume a p;
    refine and_i (¬ ∃ p ⇒ ∀ (λ x, ¬ (p x))) _ ((∀ (λ x, ¬ (p x))) ⇒ ¬ ∃ p) _ 
    {refine neg_ex1 a p}
    {refine neg_ex2 a p}
end;

opaque symbol demorgan_neg_all : Π (a : Set), Π (p : El a → Prop), Prf (¬ ∀ (λ x, ¬ (p x)) ⇔ ∃ p) ≔ 
begin
    assume a p;
    refine iff_trans_rule (¬ (`∀ x, ¬ (p x))) (∃ (λ x, ¬ ¬ (p x))) (∃ p) _ _ 
    {refine demorgan_all a (λ x, ¬ (p x))}
    {refine iff_ex a (λ x, ¬ (¬ (p x))) p _;
    assume x;
    refine iff_sym_rule (p x) (¬ ¬ p x) (double_neg_iff (p x))}
end;

opaque symbol demorgan_neg_ex : Π (a : Set), Π (p : El a → Prop), Prf (¬ ∃ (λ x, ¬ (p x)) ⇔ ∀ p) ≔ 
begin
    assume a p;
    refine iff_trans_rule (¬ ∃ (λ x, ¬ (p x))) (∀ (λ x, ¬ ¬ (p x))) (∀ p) _ _ 
    {refine demorgan_ex a (λ x, ¬ (p x))}
    {refine iff_all a (λ x, ¬ (¬ (p x))) p _;
    assume x;
    refine iff_sym_rule (p x) (¬ ¬ p x) (double_neg_iff (p x))} 
end;


// Polymorphic equality 

symbol = [a] : El a → El a → Prop;
notation = infix 40;
rule Prf (@= $a $x $y) ↪ Π (P : El $a → Prop), Prf (P $x) → Prf (P $y);

opaque symbol eq_refl_rule : Π (a : Set), Π x : El a, Prf (x = x) ≔
begin
    assume a x ;
    assume P Py;
    refine Py
end;

opaque symbol eq_refl : Π (a : Set), Prf (`∀ x : El a, x = x) ≔
begin
    assume a;
    refine all_i (λ x : El a, x = x) _;
    assume x;
    refine eq_refl_rule a x
end;

opaque symbol eq_sym_rule : Π (a : Set), Π (x y : El a), Prf (x = y) → Prf (y = x) ≔ 
begin
    assume a x y Pxy P;
    refine imp_e (P y) (P x) _;
    refine Pxy (λ z, (P z) ⇒ (P x)) _;
    refine imp_i (P x) (P x) _;
    assume Px;
    refine Px
end;

opaque symbol eq_sym : Π (a : Set), Prf (`∀ x : El a, `∀ y : El a, (x = y) ⇒ (y = x)) ≔ 
begin
    assume a;
    refine all_i (λ x : El a, `∀ y : El a, (x = y) ⇒ (y = x)) _;
    assume x;
    refine all_i (λ y : El a, (x = y) ⇒ (y = x)) _;
    assume y;
    refine imp_i (x = y) (y = x) _;
    refine eq_sym_rule a x y
end;

opaque symbol eq_trans_rule : Π (a : Set), Π (x y z : El a), Prf (x = y) → Prf (y = z) → Prf (x = z) ≔ 
begin
    assume a x y z Pxy Pyz;
    assume P Px;
    refine Pyz P (Pxy P Px)
end;

opaque symbol eq_trans : Π (a : Set), Prf (`∀ x : El a, `∀ y : El a, `∀ z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) ≔ 
begin
    assume a;
    refine all_i (λ x : El a, `∀ y : El a, `∀ z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) _;
    assume x;
    refine all_i (λ y : El a, `∀ z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) _;
    assume y;
    refine all_i (λ z : El a, ((x = y) ∧ (y = z)) ⇒ (x = z)) _;
    assume z;
    refine imp_i ((x = y) ∧ (y = z)) (x = z) _;
    assume Pxyz;
    refine eq_trans_rule a x y z (and_el (x = y) (y = z) Pxyz) (and_er (x = y) (y = z) Pxyz)
end;

opaque symbol eq_fun_rule : Π (a b : Set), Π f : El a → El b, Π (x y : El a), Prf (x = y) → Prf (f x = f y) ≔ 
begin
    assume a b f x y Pxy;
    assume P;
    refine Pxy (λ w : El a, P (f w))
end;

opaque symbol eq_fun : Π (a b : Set), Prf (`∀ f : El a → El b, `∀ x : El a, `∀ y : El a, ((x = y) ⇒ (f x = f y))) ≔ 
begin
    assume a b;
    refine all_i (λ f : El a → El b, `∀ x : El a, `∀ y : El a, ((x = y) ⇒ (f x = f y))) _;
    assume f;
    refine all_i (λ x : El a, `∀ y : El a, ((x = y) ⇒ (f x = f y))) _;
    assume x;
    refine all_i (λ y : El a, ((x = y) ⇒ (f x = f y))) _;
    assume y;
    refine imp_i (x = y) (f x = f y) _;
    assume Pxy;
    refine eq_fun_rule a b f x y Pxy
end;

opaque symbol eq_fun2 : Π (a1 a2 b : Set), Prf (`∀ f : El a1 → El a2 → El b, `∀ x1 : El a1, `∀ x2 : El a2, `∀ y1 : El a1, `∀ y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) ≔ 
begin
    assume a1 a2 b;
    refine all_i (λ f : El a1 → El a2 → El b, `∀ x1 : El a1, `∀ x2 : El a2, `∀ y1 : El a1, `∀ y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume f;
    refine all_i (λ x1 : El a1, `∀ x2 : El a2, `∀ y1 : El a1, `∀ y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume x1;
    refine all_i (λ x2 : El a2, `∀ y1 : El a1, `∀ y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume x2;
    refine all_i (λ y1 : El a1, `∀ y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume y1;
    refine all_i (λ y2 : El a2, ((x1 = y1) ⇒ (x2 = y2) ⇒ (f x1 x2 = f y1 y2))) _;
    assume y2;
    refine imp_i (x1 = y1) ((x2 = y2) ⇒ (f x1 x2 = f y1 y2)) _;
    assume Pxy1;
    refine imp_i (x2 = y2) (f x1 x2 = f y1 y2) _;
    assume Pxy2;
    assume P Pfx;
    refine Pxy1 (λ w : El a1, P (f w y2)) _;
    refine Pxy2 (λ w : El a2, P (f x1 w)) Pfx
end;

opaque symbol eq_comp : Π (a b c : Set), Prf (`∀ f : El b → El c, `∀ g : El a → El b, `∀ x : El a, `∀ y : El a, ((x = y) ⇒ (f (g x) = f (g y)))) ≔ 
begin
    assume a b c;
    refine all_i (λ f : El b → El c, `∀ g : El a → El b, `∀ x : El a, `∀ y : El a, ((x = y) ⇒ (f (g x) = f (g y)))) _;
    assume f;
    refine all_i (λ g : El a → El b, `∀ x : El a, `∀ y : El a, ((x = y) ⇒ (f (g x) = f (g y)))) _;
    assume g;
    refine all_e (λ f : El a → El c, `∀ x : El a, `∀ y : El a, ((x = y) ⇒ (f x = f y))) (eq_fun a c) (λ w, f (g w))
end;


// Peano arithmetic

constant symbol nat : Set;
constant symbol 0 : El nat;
symbol S : El nat → El nat;
symbol + : El nat → El nat → El nat; notation + infix left 45;
symbol * : El nat → El nat → El nat; notation * infix left 50;

rule (S $x = 0) ↪ ⊥;
rule S $x = S $y ↪ $x = $y;
rule $x + 0 ↪ $x;
rule $x + S $y ↪ S ($x + $y);
rule $x * 0 ↪ 0;
rule $x * (S $y) ↪ $x * $y + $x;

constant symbol induction_axiom : Prf (`∀ P, (P 0 ∧ (`∀ n, P n ⇒ P (S n))) ⇒ `∀ n, P n);

opaque symbol induction_rule : Π P : El nat → Prop, Prf (P 0) → (Π n : El nat, Prf (P n) → Prf (P (S n))) → Prf (`∀ n, P n) ≔ 
begin
    assume P H0 IH;
    refine imp_e (P 0 ∧ (`∀ n, P n ⇒ P (S n))) (`∀ n, P n) _ _ 
    {refine all_e (λ P, (P 0 ∧ (`∀ n, P n ⇒ P (S n))) ⇒ `∀ n, P n) _ P;
    refine induction_axiom}
    {refine and_i (P 0) H0 (`∀ n, P n ⇒ P (S n)) _; 
    refine all_i (λ n, P n ⇒ P (S n)) _;
    assume m;
    refine imp_i (P m) (P (S m)) _;
    refine IH m}
end;

opaque symbol Z_pred : Prf (`∀ n, (n = 0) ∨ (`∃ m, n = S m)) ≔
begin
    refine induction_rule (λ n, (n = 0) ∨ (`∃ m, n = S m)) _ _ 
    {refine or_il (0 = 0) _ (`∃ m, 0 = S m);
    refine eq_refl_rule nat 0}
    {assume n pPn;
    refine or_ir (S n = 0) (`∃ m, S n = S m) _;
    refine or_e (n = 0) (`∃ m, n = S m) pPn (`∃ m, S n = S m) _ _ 
    {assume pZ;
    refine ex_i (λ m, S n = S m) 0 _;
    refine eq_fun_rule nat nat (λ w : El nat, S w) n 0 pZ}
    {assume pEm;
    refine ex_e (λ m, n = S m) pEm (`∃ m, S n = S m) _;
    assume t pSt;
    refine ex_i (λ m, S n = S m) (S t) _;
    refine eq_fun_rule nat nat (λ w : El nat, S w) n (S t) pSt}}
end;

opaque symbol add_nZ : Prf (`∀ n, n + 0 = n) ≔ 
begin
    refine eq_refl nat
end;

opaque symbol add_Zn : Prf (`∀ n, 0 + n = n) ≔ 
begin
    refine induction_rule (λ n, 0 + n = n) _ _
    {refine eq_refl_rule  nat 0}
    {assume n pPn;
    refine pPn}
end;

opaque symbol add_Sn : Prf (`∀ n, `∀ m, S n + m = S (n + m)) ≔ 
begin
    refine induction_rule (λ n, `∀ m, S n + m = S (n + m)) _ _
    {refine induction_rule (λ m, S 0 + m = S (0 + m)) _ _
    {refine eq_refl_rule nat (S 0)}
    {assume m pPm;
    refine pPm}}
    {assume n pPn;
    refine induction_rule (λ m, (S (S n) + m) = S (S n + m)) _ _
    {refine eq_refl_rule nat (S n)}
    {assume m pPm;
    refine pPm}}
end;

symbol add_assoc : Prf (`∀ n, `∀ m, `∀ p, (n + m) + p = n + (m + p)) ≔
begin
    refine all_i (λ n, `∀ m, `∀ p, (n + m) + p = n + (m + p)) _;
    assume n;
    refine all_i (λ m, `∀ p, (n + m) + p = n + (m + p)) _;
    assume m;
    refine induction_rule (λ p, (n + m) + p = n + (m + p)) _ _ 
    {refine eq_refl_rule nat (n + m)}
    {assume p pPp;
    refine eq_fun_rule nat nat (λ w : El nat, S w) ((n + m) + p) (n + (m + p)) pPp}
end;

symbol add_assoc_rule : Π (n m p : El nat),  Prf ((n + m) + p = n + (m + p)) ≔
begin
    assume n m p;
    refine all_e (λ p, (n + m) + p = n + (m + p)) _ p;
    refine all_e (λ m, `∀ p, (n + m) + p = n + (m + p)) _ m;
    refine all_e (λ n, `∀ m, `∀ p, (n + m) + p = n + (m + p)) add_assoc n
end;

symbol add_comm : Prf (`∀ n, `∀ m, n + m = m + n) ≔ 
begin
    refine induction_rule (λ n, `∀ m, n + m = m + n) _ _
    {refine add_Zn}
    {assume n pPn;
    refine all_i (λ m, (S n + m) = (m + S n)) _;
    assume m;
    refine eq_trans_rule nat (S n + m) (S (n + m)) (m + S n) _ _ 
    {refine all_e (λ m, S n + m = S (n + m)) _ m;
    refine all_e (λ n, `∀ m, S n + m = S (n + m)) add_Sn n}
    {refine eq_fun_rule nat nat S (n + m) (m + n) _;
    refine all_e (λ m1, (n + m1) = (m1 + n)) pPn m}}
end;

symbol add_comm_rule : Π (n m : El nat), Prf (n + m = m + n) ≔ 
begin
    assume n m;
    refine all_e (λ m, n + m = m + n) _ m;
    refine all_e (λ n, `∀ m, n + m = m + n) add_comm n
end;

symbol add_left_cancel : Prf (`∀ n, `∀ m, (m + n = m) ⇒ (n = 0)) ≔
begin
    refine all_i (λ n, `∀ m, (m + n = m) ⇒ (n = 0)) _;
    assume n;
    refine induction_rule (λ m, (m + n = m) ⇒ (n = 0)) _ _ 
    {refine imp_i (0 + n = 0) (n = 0) _;
    assume Pn;
    refine (all_e (λ x, 0 + x = x) add_Zn n) (λ w, w = 0) Pn}
    {assume m Pm;
    refine (add_comm_rule n (S m)) (λ w, (w = S m) ⇒ (n = 0)) _;
    refine (add_comm_rule m n) (λ w, (S w = S m) ⇒ (n = 0)) Pm}
end;

symbol add_left_cancel_rule : Π (n m : El nat), Prf (m + n = m) → Prf (n = 0) ≔
begin
    assume n m;
    refine imp_e ((m + n) = m) (n = 0) _;
    refine all_e (λ m, ((m + n) = m) ⇒ (n = 0)) _ m;
    refine all_e (λ n, `∀ m, ((m + n) = m) ⇒ (n = 0)) add_left_cancel n;
end;

symbol add_right_cancel_rule : Π (n m : El nat), Prf (n + m = m) → Prf (n = 0) ≔
begin
    assume n m;
    refine imp_e ((n + m) = m) (n = 0) _;
    refine (add_comm_rule m n) (λ w, (w = m) ⇒ (n = 0)) _;
    refine imp_i ((m + n) = m) (n = 0) (add_left_cancel_rule n m)
end;

symbol add_left_cancel_Z : Prf (`∀ n, `∀ m, (n + m = 0) ⇒ (n = 0)) ≔
begin
    refine all_i (λ n, `∀ m, (n + m = 0) ⇒ (n = 0)) _;
    assume n;
    refine induction_rule (λ m, (n + m = 0) ⇒ (n = 0)) _ _ 
    {refine imp_i ((n + 0) = 0) (n = 0) _;
    assume Pn;
    refine Pn}
    {assume m pPm;
    refine imp_i ((n + S m) = 0) (n = 0) _;
    assume PF;
    refine bot_e PF (n = 0)}
end;

symbol add_left_cancel_Z_rule : Π (n m : El nat), Prf (n + m = 0) → Prf (n = 0) ≔
begin
    assume n m;
    refine imp_e ((n + m) = 0) (n = 0) _;
    refine all_e (λ m, (n + m = 0) ⇒ (n = 0)) _ m;
    refine all_e (λ n, `∀ m, (n + m = 0) ⇒ (n = 0)) add_left_cancel_Z n
end;

symbol add_right_cancel_Z_rule : Π (n m : El nat), Prf (m + n = 0) → Prf (n = 0) ≔
begin
    assume n m;
    refine imp_e ((m + n) = 0) (n = 0) _;
    refine (add_comm_rule n m) (λ w, (w = 0) ⇒ (n = 0)) _;
    refine imp_i ((n + m) = 0) (n = 0) (add_left_cancel_Z_rule n m)
end;

opaque symbol mult_nZ : Prf (`∀ n, n * 0 = 0) ≔ 
begin
    refine all_i (λ n, n * 0 = 0) _;
    assume n;
    refine eq_refl_rule nat 0
end;

opaque symbol mult_Zn : Prf (`∀ n, 0 * n = 0) ≔ 
begin
    refine induction_rule (λ n, 0 * n = 0) _ _ 
    {refine eq_refl_rule nat 0}
    {assume n pPn;
    refine pPn}
end;

opaque symbol mult_Sn : Prf (`∀ n, `∀ m, S n * m = n * m + m) ≔ 
begin
    refine induction_rule (λ n, `∀ m, S n * m = n * m + m) _ _
    {refine induction_rule (λ m, S 0 * m = 0 * m + m) _ _
    {refine eq_refl_rule nat 0}
    {assume m pPm;
    refine pPm}}
    {assume n pPn;
    refine induction_rule (λ m, (S (S n) * m) = (S n * m + m)) _ _
    {refine eq_refl_rule nat 0}
    {assume m pPm;
    refine (eq_sym_rule nat ((S n * m) + (S n) + m) ((S n * m) + (S n + m)) (add_assoc_rule (S n * m) (S n) m)) (λ w : El nat, (S (S n) * S m) = S w) _;
    refine (add_comm_rule m (S n)) (λ w : El nat, (S (S n) * S m) = S ((S n * m) + w)) _;
    refine eq_trans_rule nat (S (S n) * S m) (S ((S n * m) + (m + S n))) (S ((S n * m) + S (m + n))) _ _ 
    {refine eq_trans_rule nat (S (S n) * S m) (S ((S n * m) + m + S n)) (S ((S n * m) + (m + S n))) _ _ 
    {refine eq_fun_rule nat nat (λ w : El nat, w + S (S n)) (S (S n) * m) ((S n * m) + m) pPm}
    {refine eq_fun_rule nat nat (λ w : El nat, S w) (((S n * m) + m) + S n) ((S n * m) + (m + S n)) (add_assoc_rule (S n * m) m (S n))}}
    {refine eq_refl_rule nat (S ((S n * m) + (m + S n)))}
    }}
end;

symbol mult_comm : Prf (`∀ n, `∀ m, n * m = m * n) ≔ 
begin
    refine induction_rule (λ n, `∀ m, n * m = m * n) _ _
    {refine mult_Zn}
    {assume n pPn;
    refine all_i (λ m, (S n * m) = (m * S n)) _;
    assume m;
    refine eq_trans_rule nat (S n * m) (n * m + m) (m * (S n)) _ _ 
    {refine all_e (λ m, S n * m = n * m + m) _ m;
    refine all_e (λ n, `∀ m, S n * m = n * m + m) mult_Sn n}
    {refine eq_fun_rule nat nat (λ w : El nat, w + m) (n * m) (m * n) _;
    refine all_e (λ m1, (n * m1) = (m1 * n)) pPn m}}
end;

symbol mult_comm_rule : Π (n m : El nat), Prf (n * m = m * n) ≔ 
begin
    assume n m;
    refine all_e (λ m, n * m = m * n) _ m;
    refine all_e (λ n, `∀ m, n * m = m * n) mult_comm n
end;

symbol distrib_right : Prf (`∀ n, `∀ m, `∀ p, (n + m) * p = n * p + m * p) ≔
begin
    refine all_i (λ n, `∀ m, `∀ p, (n + m) * p = n * p + m * p) _;
    assume n;
    refine all_i (λ m, `∀ p, (n + m) * p = n * p + m * p) _;
    assume m;
    refine induction_rule (λ p, (n + m) * p = n * p + m * p) _ _ 
    {refine eq_refl_rule nat 0}
    {assume p pPp;
    refine (add_assoc_rule (n * p + n) (m * p) m) (λ w, ((n + m) * S p) = w) _;
    refine (eq_sym_rule nat (((n * p) + n) + (m * p)) ((n * p) + (n + (m * p))) (add_assoc_rule (n * p) n (m * p))) (λ w, ((n + m) * S p) = w + m) _;
    refine (add_comm_rule (m * p) n) (λ w, ((n + m) * S p) = (((n * p) + w) + m)) _;
    refine (add_assoc_rule (n * p) (m * p) n) (λ w, ((n + m) * S p) = (w + m)) _;
    refine (eq_sym_rule nat ((((n * p) + (m * p)) + n) + m) (((n * p) + (m * p)) + (n + m)) (add_assoc_rule ((n * p) + (m * p)) n m)) (λ w, ((n + m) * S p) = w) _;
    refine pPp (λ w, ((n + m) * S p) = w + (n + m)) _;
    refine eq_refl_rule nat ((n + m) * S p)}
end;

symbol distrib_right_rule : Π (n m p : El nat),  Prf ((n + m) * p = n * p + m * p) ≔
begin
    assume n m p;
    refine all_e (λ p, (n + m) * p = n * p + m * p) _ p;
    refine all_e (λ m, `∀ p, (n + m) * p = n * p + m * p) _ m;
    refine all_e (λ n, `∀ m, `∀ p, (n + m) * p = n * p + m * p) distrib_right n
end;

symbol distrib_left_rule : Π (n m p : El nat),  Prf (n * (m + p) = n * m + n * p) ≔
begin
    assume n m p;
    refine (mult_comm_rule (m + p)) n (λ w, w = ((n * m) + (n * p))) _;
    refine (mult_comm_rule m n) (λ w, ((m + p) * n) = (w + (n * p))) _;
    refine (mult_comm_rule p n) (λ w, ((m + p) * n) = ((m * n) + w)) _;
    refine distrib_right_rule m p n
end;

symbol mult_assoc : Prf (`∀ n, `∀ m, `∀ p, (n * m) * p = n * (m * p)) ≔
begin
    refine all_i (λ n, `∀ m, `∀ p, (n * m) * p = n * (m * p)) _;
    assume n;
    refine all_i (λ m, `∀ p, (n * m) * p = n * (m * p)) _;
    assume m;
    refine induction_rule (λ p, (n * m) * p = n * (m * p)) _ _ 
    {refine eq_refl_rule nat 0}
    {assume p pPp;
    refine (eq_sym_rule nat ((n * m) * p) (n * (m * p)) pPp) (λ w, (w + n * m) = (n * (m * S p))) _;
    refine ((distrib_left_rule n (m * p) m)) (λ w, w = (n * (m * S p))) _;
    refine eq_refl_rule nat (n * (m * S p))}
end;

symbol mult_assoc_rule : Π (n m p : El nat),  Prf ((n * m) * p = n * (m * p)) ≔
begin
    assume n m p;
    refine all_e (λ p, (n * m) * p = n * (m * p)) _ p;
    refine all_e (λ m, `∀ p, (n * m) * p = n * (m * p)) _ m;
    refine all_e (λ n, `∀ m, `∀ p, (n * m) * p = n * (m * p)) mult_assoc n
end;

symbol exp : El nat → El nat → El nat;
rule exp $b 0 ↪ S 0;
rule exp $b (S $x) ↪ $b * (exp $b $x);

symbol mult_one : Prf (`∀ n, n = n * (S 0)) ≔
begin
    refine all_i (λ n, n = n * (S 0)) _;
    assume n;
    refine (all_e ((λ n, 0 + n = n)) add_Zn n) (λ w, w = (0 + n)) _;
    refine eq_refl_rule nat (0 + n)
end;

symbol exp_add : Prf (`∀ b, `∀ n, `∀ m, exp b (n + m) = (exp b n) * (exp b m)) ≔
begin
    refine all_i (λ b, `∀ n, `∀ m, exp b (n + m) = (exp b n) * (exp b m)) _;
    assume b;
    refine all_i (λ n, `∀ m, exp b (n + m) = (exp b n) * (exp b m)) _;
    assume n;
    refine induction_rule (λ m, exp b (n + m) = (exp b n) * (exp b m)) _ _ 
    {refine (all_e (λ n, n = n * (S 0)) mult_one (exp b n)) (λ w, exp b (n + 0) = w) _;
    refine eq_refl_rule nat (exp b n)}
    {assume m pPm;
    refine (mult_assoc_rule (exp b n) b (exp b m)) (λ w, b * (exp b (n + m)) = w) _;
    refine (mult_comm_rule b (exp b n)) (λ w, (b * exp b (n + m)) = (w * exp b m)) _;
    refine (eq_sym_rule nat (exp b (n + m)) (exp b n * exp b m) pPm) (λ w, (b * w) = ((b * exp b n) * exp b m)) _;
    refine (mult_assoc_rule b (exp b n) (exp b m)) (λ w, w = ((b * exp b n) * exp b m)) _;
    refine eq_refl_rule nat ((b * exp b n) * exp b m)}
end;

symbol exp_add_rule : Π (b n m : El nat), Prf (exp b (n + m) = (exp b n) * (exp b m)) ≔
begin
    assume b n m;
    refine all_e (λ m, exp b (n + m) = (exp b n) * (exp b m)) _ m;
    refine all_e (λ n, `∀ m, exp b (n + m) = (exp b n) * (exp b m)) _ n;
    refine all_e (λ b, `∀ n, `∀ m, exp b (n + m) = (exp b n) * (exp b m)) exp_add b
end;

symbol exp_mult : Prf (`∀ b, `∀ n, `∀ m, exp b (n * m) = exp (exp b n) m) ≔
begin
    refine all_i (λ b, `∀ n, `∀ m, exp b (n * m) = exp (exp b n) m) _;
    assume b;
    refine all_i (λ n, `∀ m, exp b (n * m) = exp (exp b n) m) _;
    assume n;
    refine induction_rule (λ m, exp b (n * m) = exp (exp b n) m) _ _ 
    {refine eq_refl_rule nat (S 0)}
    {assume m pPm;
    refine pPm (λ w, exp b (n * S m) = (exp b n) * w) _;
    refine (exp_add_rule b n (n * m)) (λ w, exp b (n * S m) = w) _;
    refine (add_comm_rule (n * m) n) (λ w, exp b (n * S m) = exp b w) _;
    refine eq_refl_rule nat (exp b (n * S m))}
end;

symbol exp_mult_rule : Π (b n m : El nat), Prf (exp b (n * m) = exp (exp b n) m) ≔
begin
    assume b n m;
    refine all_e (λ m, exp b (n * m) = exp (exp b n) m) _ m;
    refine all_e (λ n, `∀ m, exp b (n * m) = exp (exp b n) m) _ n;
    refine all_e (λ b, `∀ n, `∀ m, exp b (n * m) = exp (exp b n) m) exp_mult b
end;

symbol leq : El nat → El nat → Prop;
rule leq $n $m ↪ `∃ p, $n + p = $m;

symbol leq_refl : Π n : El nat, Prf (leq n n) ≔
begin
    assume n;
    refine ex_i (λ p, n + p = n) 0 _;
    refine eq_refl_rule nat n
end;

symbol leq_trans : Π (n m p : El nat), Prf (leq n m) → Prf (leq m p) → Prf (leq n p) ≔
begin
    assume n m p Pnm Pmp;
    refine ex_e (λ x, n + x = m) Pnm _ _;
    assume x Px;
    refine ex_e (λ y, m + y = p) Pmp _ _;
    assume y Py;
    refine ex_i (λ z, n + z = p) (x + y) _;
    refine Py (λ w, (n + (x + y)) = w) _;
    refine Px (λ w, (n + (x + y)) = (w + y)) _;
    refine eq_sym_rule nat ((n + x) + y) (n + (x + y)) (add_assoc_rule n x y)
end;

symbol leq_antisym : Π (n m : El nat), Prf (leq n m) → Prf (leq m n) → Prf (n = m) ≔
begin
    assume n m Pnm Pmn;
    refine ex_e (λ x, n + x = m) Pnm _ _;
    assume x Px;
    refine ex_e (λ y, m + y = n) Pmn _ _;
    assume y Py;
    refine imp_e (x = 0) (n = m) _ _ 
    {refine imp_i (x = 0) (n = m) _;
    assume PxZ;
    refine PxZ (λ w, n + w = m) Px}
    {refine imp_e (x + y = 0) (x = 0) _ _ 
    {refine all_e (λ m, (x + m = 0) ⇒ (x = 0)) _ y;
    refine all_e (λ n, `∀ m, (n + m = 0) ⇒ (n = 0)) add_left_cancel_Z x}
    {refine add_left_cancel_rule (x + y) n _;
    refine (add_assoc_rule n x y) (λ w, w = n) _;
    refine (eq_sym_rule nat (n + x) m Px) (λ w, w + y = n) Py}}
end;