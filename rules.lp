require open Logic.Construkti.logic;

rule Prf ($x ⇒ $y) ↪ Prf $x → Prf $y;

rule Prf (∀ $p) ↪ Π x, Prf ($p x);

rule ¬ $p ↪ $p ⇒ ⊥;