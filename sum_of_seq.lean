import data.real.basic
import analysis.normed.group.basic

notation `|`x`|` := abs x

/- 
converges_to_L claims that, for some function (f) and a real number (L), for all è > 0,
there is some natural number (M) such that, for all natural numbers (n) greater than 
or equal to M, f(n) is less than è away from L
-/
def converges_to_L (f : ℕ → ℝ) (L : ℝ) : Prop := 
    ∀ ε > 0, ∃ M : ℕ, ∀ n : ℕ, n ≥ M → (|f n - L| < ε)

/- 
sum_of_limits claims that, if functions a and b converge to La and Lb respectively,
then the function a + b converges to La + Lb.
-/
theorem sum_of_limits (a b : ℕ → ℝ) (La Lb : ℝ)     -- take arguments a b La Lb
                      (ha : converges_to_L a La)    -- require proof a goes to La
                      (hb : converges_to_L b Lb) :  -- require proof b goes to Lb
                      converges_to_L (λ n, a n + b n) (La + Lb) := 
                      -- give proof that a + b converges to La + Lb 

begin
    intro ε,       -- introduce epsilon
    intro hε,      -- greater than zero
    simp,          -- evaluate the lambda expression

    specialize ha (ε / 2) (half_pos hε), -- use ε / 2 in place of ε in hypothesis a
    specialize hb (ε / 2) (half_pos hε), -- use ε / 2 in place of ε in hypothesis b

    cases ha with Ma hMa, -- get M such that ha is true, call this hMa (hypothesis Ma)
    cases hb with Mb hMb, -- get M such that hb is true, call this hMb (hypothesis Mb)
    use max Ma Mb,        -- choose the max to be M

    intro n,              -- pick some n
    intro hn,             -- such that n ≥ M

    specialize hMa n (le_of_max_le_left hn),  -- use this n
    specialize hMb n (le_of_max_le_right hn), -- use this n

    rw abs_lt at *, -- rewrite to remove absolute values in all expressions
                    -- this is done by replacing |x| < a with -a < x and x < a
    cases hMa,      -- split hMa into two props (as opposed to one using and)
    cases hMb,      -- split hMb into two props (as opposed to one using and)

    split,          -- our target into two props (as opposed to one using and)
    { linarith },   -- show -ε < a n + b n - (la + lb) using the context
    { linarith },   -- show  a n + b n - (la + lb) < ε using the context
end