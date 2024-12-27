import Mathlib.Data.Set.Basic
-- set_option diagnostics true

section YonedaPreorder
variable {α : Type*}
variable [Preorder α]

-- Useful upper set definition
def Upper (p : α) : Set α := {q : α | p ≤ q }

theorem UpperIsUpperSet (p : α) : IsUpperSet (Upper p) := by
  dsimp [IsUpperSet]
  intro a b ab aUp
  dsimp [Upper] at *
  apply Preorder.le_trans p a
  apply aUp
  apply ab

-- Mapping from set to its upper set
def ToUpper : α → Set α
  | p => Upper p

-- Proving antimonotonicity of ToUpper
theorem AntitoneOfOpToUp : Antitone ToUpper (α := α) := by
  dsimp [Antitone]
  intro a b ab
  dsimp [ToUpper, Upper]
  simp
  intro x hbx
  exact le_trans ab hbx

theorem YonedaPreorder (p p' : α) : p ≤ p' ↔ Upper p' ⊆ Upper p := by
  constructor
  · intro hp x hxp'
    dsimp [Upper] at *
    exact le_trans hp hxp'
  · intro hp
    dsimp [Upper] at *
    simp at *
    apply hp
    rfl

end YonedaPreorder
