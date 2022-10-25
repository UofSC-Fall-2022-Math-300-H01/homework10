import Hw10
import Sets.Basic
import Functions.Basic
import Lean.Elab.Print
import Lean.Elab.Command

open Set
open Func

variable (α β γ : Type)
variable (f : α → β) (g : β → γ) 
variable (X Y : Set α) (U V : Set β)

theorem desiredType1 (h : U ⊆ V) : f ⁻¹ U ⊆ f ⁻¹ V := by 
  intro a h'
  have : f a ∈ V := h (f a) h'
  exact this 

theorem desiredType2 (h₁ : α ≅ β) (h₂ : β ≅ γ) : α ≅ γ := by
  have ⟨f,u⟩ := h₁ 
  have ⟨g,v⟩ := h₂ 
  have l : Bijective (g ∘ f) := by 
    have (inj : Injective (g ∘ f)) := inj_comp u.left v.left   
    have (surj : Surjective (g ∘ f)) := surj_comp u.right v.right 
    exact ⟨inj,surj⟩ 
  exact ⟨g ∘ f,l⟩ 

theorem desiredType3 (h : Surjective f) : HasRightInv f := by 
  let g : β → α := by 
    intro b 
    have : ∃ a, f a = b := h b 
    have (a : α) := Classical.choose this 
    exact a  
  have (l : f ∘ g = id) := by 
    apply funext 
    intro b 
    have u : g b = Classical.choose (h b) := by rfl 
    have v : f (Classical.choose (h b)) = b := Classical.choose_spec (h b)
    calc 
      f (g b) = f (Classical.choose (h b))  := by rw [u] 
      _       = b                           := by rw [v] 
  exact ⟨g,l⟩ 

theorem desiredType4 (f : α → β) (g : β → γ) (d : LeftInverse f) (e : LeftInverse g) : 
  (d.to_fun ∘ e.to_fun) ∘ (g ∘ f) = id := sorry 

theorem desiredType5 (h : α ≅ β) : β ≅ α := sorry 

open Lean
open Lean.Meta
open Lean.Elab.Command

def n : String := "2"

def problem : String := "problem"++n

def desired : String := "desiredType"++n

def collectAxiomsOf (constName : Name) : MetaM (List String) := do
  let env ← getEnv
  let (_, s) := ((CollectAxioms.collect constName).run env).run {}
  let a := s.axioms.toList.map toString
  return a

#eval isDefEq (Expr.const desired []) (Expr.const problem [])
#eval collectAxiomsOf problem
