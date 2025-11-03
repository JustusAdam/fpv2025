import AutograderLib
import LoVe.LoVelib
import Mathlib.Data.ZMod.Defs

namespace LoVe

structure ListGraph (V : Type) :=
  (edges : List (V × V))

structure PredGraph (V : Type) :=
  (adj : V → V → Prop)
  (symm : Symmetric adj)
  (loopless : Irreflexive adj)

inductive Quad : Type
| one | two | three | four

def Quad.all : List Quad :=
  [one, two, three, four]

-- Feel free to ignore these lines
deriving instance Repr for ListGraph
deriving instance Repr for Quad

section
open Quad

deriving instance DecidableEq for Quad

def K₄_quad_lg : ListGraph Quad where
  edges := do
    let x <- Quad.all
    let y <- Quad.all
    if x = y then [] else return (x, y)


def K₄_quad_pg : PredGraph Quad where
  adj := fun x y => x ≠ y
  symm := by
    unfold Symmetric
    intros x y h
    apply Ne.symm
    assumption
  loopless := by
    unfold Irreflexive
    simp

end

def C₅ : PredGraph (Fin 5) where
  adj x y := y = (x + 1) ∨ x = y + 1
  symm := by
    unfold Symmetric
    intros x y h
    cases h
    (expose_names; exact Or.inr h)
    (expose_names; exact Or.inl h)
  loopless := by
    unfold Irreflexive
    intros x
    simp


def C₁₀₀ : PredGraph (Fin 100) where
  adj x y := y = (x + 1) ∨ x = y + 1
  symm := by
    unfold Symmetric
    intros x y h
    cases h
    (expose_names; exact Or.inr h)
    (expose_names; exact Or.inl h)
  loopless := by
    unfold Irreflexive
    intros x
    simp

def IsGraphAutomorphism {α : Type} (G : PredGraph α) (A : α → α) : Prop :=
  ∀ (v₁ v₂ : α), G.adj v₁ v₂ ↔ G.adj (A v₁) (A v₂)

structure GraphAutomorphism (α : Type) (G : PredGraph α) :=
  (f : α → α)
  (is_aut : IsGraphAutomorphism G f)

def C₅_rotate (n : Fin 5) : Fin 5 → Fin 5 := (. + n)

example {y n : ℤ} : (0 - (y - n)) + n = 2 * n - y := by
  linarith

def C₅_flip (n : Fin 5) : Fin 5 → Fin 5 :=
  fun y => 2 * n - y

@[autogradedProof 1]
theorem C₅_rotate_is_aut : ∀ n, IsGraphAutomorphism C₅ (C₅_rotate n) := by
  intros n
  unfold IsGraphAutomorphism
  intros v₁ v₂
  constructor
  unfold C₅
  simp
  intros h
  unfold C₅_rotate
  cases h with
  | inl hₗ =>
    apply Or.inl
    rw [hₗ]
    exact add_right_comm v₁ 1 n
    done
  | inr hᵣ =>
    apply Or.inr
    rw [hᵣ]
    exact add_right_comm v₂ 1 n
    done



@[autogradedProof 1]
theorem C₅_flip_is_aut : ∀ n, IsGraphAutomorphism C₅ (C₅_flip n) :=
  sorry
