
-- from C₁₀₀ : PredGraph (Fin 100)
example (x y : Fin 100) (h : y = x + 1 ∨ x = y + 1) : x = y + 1 ∨ y = x + 1 := sorry


-- From C₅_rotate_is_aut
example (n v₁ v₂ : Fin 5) : v₂ = v₁ + 1 ∨ v₁ = v₂ + 1 ↔ v₂ + n = v₁ + n + 1 ∨ v₁ + n = v₂ + n + 1
  := sorry

-- from C₅_flip_is_aut
example (n v₁ v₂ : Fin 5) : v₂ = v₁ + 1 ∨ v₁ = v₂ + 1 ↔ n + n - v₂ = n + n - v₁ + 1 ∨ n + n - v₁ = n + n - v₂ + 1 := sorry

-- from exist_distinct_fin4_of_neq
example ∀ x y : Fin 4, x ≠ y → ∃ a b : Fin 4, x ≠ a ∧ a ≠ y ∧ x ≠ b ∧ b ≠ y ∧ a ≠ b := sorry
