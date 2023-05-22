/- Basic Type Checking -/
        
#check 1     -- ℕ 
#check ℕ     -- Type
#check Type  -- Type 1

/--------------------------------/
constant n    : ℕ
constants a b : ℕ

#check n     -- ℕ
#check a     -- ℕ
#check b     -- ℕ

/--------------------------------/
constants p q : Prop
constant hp   : p

#check p     -- Prop
#check q     -- Prop
#check hp    -- p

/--------------------------------/
constant p_imp_q : p → q

#check p_imp_q    -- p → q
#check p_imp_q hp -- q