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
  fun y => n + n - y

@[autogradedProof 1]
theorem C₅_rotate_is_aut : ∀ n, IsGraphAutomorphism C₅ (C₅_rotate n) := by
  intros n
  unfold IsGraphAutomorphism
  intros v₁ v₂
  unfold C₅
  simp
  unfold C₅_rotate
  constructor
  . intros h
    apply h.imp
    . intros hₗ
      rw [hₗ]
      exact add_right_comm v₁ 1 n
    . intros hᵣ
      rw [hᵣ]
      exact add_right_comm v₂ 1 n
  . intros h
    apply h.imp
    . intros hₗ
      rw [add_right_comm] at hₗ
      exact add_right_cancel hₗ
      done
    . intros hᵣ
      rw [add_right_comm] at hᵣ
      exact add_right_cancel hᵣ
      done


@[autogradedProof 1]
theorem C₅_flip_is_aut : ∀ n, IsGraphAutomorphism C₅ (C₅_flip n) := by
  intros n
  unfold IsGraphAutomorphism C₅ C₅_flip
  simp
  intros v₁ v₂
  constructor
  . intros h
    cases h with
    | inl h =>
      rw [h]
      rw [add_sub_assoc, add_sub_assoc, add_assoc, add_assoc]
      rw [add_left_cancel_iff, add_left_cancel_iff]
      rw [sub_add, sub_add, sub_right_inj, add_sub_cancel_right]
      right
      rfl
    | inr h =>
      rw [h]
      rw [sub_add, sub_add]
      rw [sub_right_inj, sub_right_inj]
      left
      rw [add_sub_cancel_right]
      done
  . intros h
    cases h with
    | inl h_r =>
      simp [sub_add] at h_r
      right
      symm
      exact add_eq_of_eq_sub h_r
      done
    | inr h_r =>
      simp [sub_add] at h_r
      left
      symm
      exact add_eq_of_eq_sub h_r
      done

def C₅_rotate_aut (n : Fin 5) : GraphAutomorphism (Fin 5) C₅ := {
  f := C₅_rotate n
  is_aut := C₅_rotate_is_aut n
}

def C₅_flip_aut (n : Fin 5) : GraphAutomorphism (Fin 5) C₅ := {
  f := C₅_flip n
  is_aut := C₅_flip_is_aut n
}

@[autogradedProof 1]
lemma aut_comp_aut {α : Type} (G : PredGraph α) (f g : α → α) :
  IsGraphAutomorphism G f →
  IsGraphAutomorphism G g →
  IsGraphAutomorphism G (f ∘ g) := by
  unfold IsGraphAutomorphism
  intros h1 h2 v1 v2
  apply Iff.trans
  exact h1 v1 v2
  exact (iff_congr (h1 v1 v2) (h1 (g v1) (g v2))).mp (h2 v1 v2)

def aut_comp {α : Type} (G : PredGraph α) :
 GraphAutomorphism α G → GraphAutomorphism α G → GraphAutomorphism α G := by
  intros g1 g2
  constructor
  swap
  exact g1.f ∘ g2.f
  exact aut_comp_aut G g1.f g2.f g1.is_aut g2.is_aut

-- We define convenience notation for the composition operation on the
-- automorphism group of `path₅`
infixl:90 " ∘₅ " => aut_comp C₅

@[autogradedProof 1]
lemma GraphAutomorphism.assoc :
  ∀ (a b c : GraphAutomorphism (Fin 5) C₅), a ∘₅ b ∘₅ c = a ∘₅ (b ∘₅ c) := by
  intros a b c
  unfold aut_comp
  rfl
  done

-- Note: You **do not** need to provide the `is_aut` field for the value you
-- return; feel free to `sorry` that proof.
def GraphAutomorphism.inv :
  GraphAutomorphism (Fin 5) C₅ → GraphAutomorphism (Fin 5) C₅ := by
  intros a
  constructor
  sorry
  let f := a.f
  exact f ∘ f ∘ f ∘ f
  done

inductive IsPath {α : Type} : PredGraph α → α → α → List α → Prop
-- Fill this in!

-- A graph is connected if there is a path between any two distinct vertices
def IsConnected {α : Type} (G : PredGraph α) : Prop :=
  ∀ (v₁ v₂ : α), v₁ ≠ v₂ → ∃ p, IsPath G v₁ v₂ p
