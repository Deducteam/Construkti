require open Construkti.logic;

opaque symbol theorem1 : Π P : Prop, Prf (P ⇒ P) 
≔ λ P : Prop, imp_i P P (λ pP : Prf P, pP);

opaque symbol theorem2 : Π P : Prop, Prf (P ⇒ P) ≔ 
begin 
    assume P;
    refine imp_i P P (λ pP : Prf P, pP)
end;