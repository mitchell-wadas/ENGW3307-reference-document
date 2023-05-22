import data.real.basic
import analysis.normed.group.basic

notation `|`x`|` := abs x

def converges_to_L (f : ℕ → ℝ) (L : ℝ) : Prop := 
    ∀ ε > 0, ∃ M : ℕ, ∀ n : ℕ, n ≥ M → (|f n - L| < ε)

theorem sum_of_limits (a b : ℕ → ℝ) (La Lb : ℝ) 
                      (ha : converges_to_L a La) 
                      (hb : converges_to_L b Lb) :
                      converges_to_L (λ n, a n + b n) (La + Lb) := 

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