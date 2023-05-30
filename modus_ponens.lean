variables p q r : Prop  -- p, q, and r are propositions

/- define modus_ponens to be an object of type p → (p → q) → q
   that is, modus_ponens is a proof of p → (p → q) → q -/
lemma modus_ponens : p → (p → q) → q :=
    λ hp : p, λ hpq : p → q, hpq hp  -- specifically this object

variable hp : p       -- assume p is true
variable hpq : p → q  -- assume p implies q

#check modus_ponens             -- check what modus_ponens proves
#check modus_ponens p q         -- specify the propositions
#check modus_ponens p q hp      -- give assumption p and get (p → q) → q
#check modus_ponens p q hp hpq  -- give assumption (p → q) and get q

/- define modus_ponens1 to be an object of type p → (p → q) → q
   that is, modus_ponens1 is a proof of p → (p → q) → q -/
lemma modus_ponens1 : p → (p → q) → q :=
begin
    intro hp,   -- introduce the assumption that p is true
    intro hpq,  -- introduce the assumption that p implies q
    apply hpq,  -- apply the assumption hpq to simplify to q
    exact hp,   -- let Lean know we have q to be true
end

/- define modus_ponens2 to be an object of type p → (p → q) → q
   that is, modus_ponens2 is a proof of p → (p → q) → q -/
lemma modus_ponens2 : p → (p → q) → q :=
    by apply modus_ponens -- the same object as modus ponens (same proof)