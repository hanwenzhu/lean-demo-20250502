import Mathlib
open Nat Set
/--
Let 𝐻 be an 𝑛 × 𝑛 matrix all of whose entries are ±1 and whose rows are mutually orthogonal. Suppose 𝐻 has an
𝑎 × 𝑏 submatrix whose entries are all 1. Show that 𝑎𝑏 ≤ 𝑛.
-/
theorem putnam_2005_a4
(n : ℕ)
(H : Matrix (Fin n) (Fin n) ℝ)
(a b : ℕ)
(S : Matrix (Fin a) (Fin b) ℝ)
(npos : n ≥ 1)
(Hentries : ∀ i j : Fin n, H i j = 1 ∨ H i j = -1)
(Hortho : H.HasOrthogonalRows)
(hab : 1 ≤ a ∧ a ≤ n ∧ 1 ≤ b ∧ b ≤ n)
(Ssub : ∃ (rri : Fin a → Fin n) (cri : Fin b → Fin n), rri.Injective ∧ cri.Injective ∧ S = H.submatrix
rri cri)
(Sentries : ∀ (i : Fin a) (j : Fin b), S i j = 1)
: a * b ≤ n := by
  obtain ⟨rri, cri, hrinj, hcrij, hsub⟩ := Ssub
  have h1 : a ≤ n := hab.2.1
  have h2 : b ≤ n := hab.2.2.2
  have h3 : a * b ≤ n := by
    calc
      a * b = Cardinal.toNat (a * b) := by simp [Nat.cast_inj]
      _ ≤ Cardinal.toNat (n) := by
        apply?
      _ = n := by simp [Nat.cast_inj]
  exact h3
