variables p q r : Prop

lemma modus_ponens : p → (p → q) → q :=
    λ hp : p, λ hpq : p → q, hpq hp 

variable hp : p
variable hpq : p → q

#check modus_ponens             -- ∀ (p q : Prop), p → (p → q) → q
#check modus_ponens p q         -- p → (p → q) → q
#check modus_ponens p q hp      -- (p → q) → q
#check modus_ponens p q hp hpq  -- q

lemma modus_ponens1 : p → (p → q) → q :=
begin
    intro hp,
    intro hpq,
    apply hpq,
    exact hp,
end

lemma modus_ponens2 : p → (p → q) → q :=
by apply modus_ponens1
