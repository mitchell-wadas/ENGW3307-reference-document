/- Basic Type Checking -/
        
#check 1     -- 1 is a natural number
#check ℕ     -- ℕ is a Type
#check Type  -- Type is in a larger universe Type 1

/--------------------------------/
constant n    : ℕ  -- define n to be an arbitrary natural number
constants a b : ℕ  -- define a and b to be arbitrary natural numbers 

#check n     -- n is a natural number
#check a     -- a is a natural number
#check b     -- b is a natural number

/--------------------------------/
constants p q : Prop  -- p and q are propositions
constant hp   : p     -- hp is a proof of p

#check p     -- p is a proposition (p : Prop)
#check q     -- q is a proposition (q : Prop)
#check hp    -- hp is proof of p (hp : p)

/--------------------------------/
constant p_imp_q : p → q  -- assume p implies q by defining a proof

#check p_imp_q     -- p_imp_q proves p → q
#check p_imp_q hp  /- apply p_imp_q to a proof of p (hp)
                      to get a proof of q (p_imp_q(hp) : q) -/