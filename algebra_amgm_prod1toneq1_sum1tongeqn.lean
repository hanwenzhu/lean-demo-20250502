import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

/-- Show that for any real-valued function $a$ on the natural numbers such that $\forall i \in \mathbb{N}, a_i \geq 0$, if $prod_{i=0}^{n-1} a_i = 1$, then $sum_{i=0}^{n-1} a_i \geq n$.-/
theorem algebra_amgm_prod1toneq1_sum1tongeqn (a : ℕ → NNReal) (n : ℕ)
  (h₀ : Finset.prod (Finset.range n) a = 1) : Finset.sum (Finset.range n) a ≥ n := by
  have am_gm_inequality : ∀ (x : ℕ → NNReal) (m : ℕ),
    Finset.sum (Finset.range m) x / m ≥ (Finset.prod (Finset.range m) x) ^ (1 / m) := by
    have step0 : ∀ (x : ℕ → NNReal) (m : ℕ), Finset.sum (Finset.range m) x / m ≥ (Finset.prod (Finset.range m) x) ^ (1 / m) := by
      intro x m
      have h₁ : ∀ T : Type*, T → ℕ → NNReal → NNReal := by
        intro T
        intro t
        intro m
        intro a
        exact a
      -- Apply AM-GM inequality to the sequence \( x_1, x_2, \ldots, x_m \)
      have h₂ : Finset.sum (Finset.range m) x / m ≥ (Finset.prod (Finset.range m) x) ^ (1 / m) := by
        apply?
      exact h₂
    have step1 : ∀ (x : ℕ → NNReal) (m : ℕ), Finset.sum (Finset.range m) x / m ≥ (Finset.prod (Finset.range m) x) ^ (1 / m) := by
      intro x m
      -- Rewrite the inequality in a more manageable form
      rw [ge_iff_le]
      -- Use the given inequality from the problem statement
      have h₁ : Finset.sum (Finset.range m) x / m ≥ (Finset.prod (Finset.range m) x) ^ (1 / m) := step0 x m
      -- Conclude the proof by linear arithmetic
      simpa using h₁

    have step2 : ∀ (x : ℕ → NNReal) (m : ℕ), Finset.sum (Finset.range m) x / m ≥ (Finset.prod (Finset.range m) x) ^ (1 / m) := by
      intro x m
      have h₁ := step0 x m
      have h₂ := step1 x m
      simp_all

    exact step0

  have geometric_mean_eq_one : (Finset.prod (Finset.range n) a) ^ (1 / n) = 1 := by
    have h₁ := am_gm_inequality (fun _ => 1) 0
    have h₂ := am_gm_inequality (fun _ => 1) 1
    have h₃ := am_gm_inequality (fun _ => 1) 2
    have h₄ := am_gm_inequality (fun _ => 1) 3
    have h₅ := am_gm_inequality (fun _ => 1) 4
    simp at h₁ h₂ h₃ h₄ h₅

  have arithmetic_mean_ge_one : Finset.sum (Finset.range n) a / n ≥ 1 := by
    have h₁ : Finset.sum (Finset.range n) a / n ≥ 1 := by
      -- Use the AM-GM inequality with the given product condition
      have h₂ := am_gm_inequality a n
      have h₃ := am_gm_inequality (fun _ => 0) 0
      have h₄ := am_gm_inequality (fun _ => 1) 0
      have h₅ := am_gm_inequality (fun _ => 1) 1
      have h₆ := am_gm_inequality (fun _ => 1) 2
      have h₇ := am_gm_inequality (fun _ => 1) 3
      have h₈ := am_gm_inequality (fun _ => 1) 4
      have h₉ := am_gm_inequality (fun _ => 1) 5
      have h₁₀ := am_gm_inequality (fun _ => 1) 6
      have h₁₁ := am_gm_inequality (fun _ => 1) 7
      have h₁₂ := am_gm_inequality (fun _ => 1) 8
      have h₁₃ := am_gm_inequality (fun _ => 1) 9
      have h₁₄ := am_gm_inequality (fun _ => 1) 10
      -- Simplify the inequalities to show the desired result
      norm_num at h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄
    exact h₁

  have sum_ge_n : Finset.sum (Finset.range n) a ≥ n := by
    have h₁ := am_gm_inequality (fun i => 1) 0
    have h₂ := am_gm_inequality (fun i => 1) 1
    have h₃ := am_gm_inequality a n
    have h₄ := am_gm_inequality (fun i => 1) 2
    have h₅ := am_gm_inequality (fun i => 1) 3
    have h₆ := am_gm_inequality (fun i => 1) 4
    have h₇ := am_gm_inequality (fun i => 1) 5
    have h₈ := am_gm_inequality (fun i => 1) 6
    have h₉ := am_gm_inequality (fun i => 1) 7
    have h₁₀ := am_gm_inequality (fun i => 1) 8
    have h₁₁ := am_gm_inequality (fun i => 1) 9
    have h₁₂ := am_gm_inequality (fun i => 1) 10
    simp at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂

  simpa using sum_ge_n
