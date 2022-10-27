import Sets.Basic 

namespace Func

variable { α β γ : Type }

def Injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂ 

def Surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b 

def Bijective (f : α → β) : Prop :=  Injective f ∧ Surjective f 

structure LeftInverse (f : α → β) where 
  to_fun : β → α  
  invl : to_fun ∘ f = id 

structure RightInverse (f : β → α) where 
  to_fun : α → β 
  invr : f ∘ to_fun = id 

structure Inverse (f : α → β) where 
  to_fun : β → α  
  invl : to_fun ∘ f = id 
  invr : f ∘ to_fun = id 

def HasLeftInv (f : α → β) : Prop := Nonempty (LeftInverse f) 

def HasRightInv (f : α → β) : Prop := Nonempty (RightInverse f) 

def IdInv : LeftInverse (@id α) := ⟨id,by rfl⟩ 

theorem inj_comp {f : α → β} {g : β → γ} (h₁ : Injective f) (h₂ : Injective g) : Injective (g ∘ f) 
  := by 
    intro a₁ a₂ h
    have (l₁ : f a₁ = f a₂) := h₂ h 
    exact h₁ l₁  

theorem surj_comp {f : α → β} {g : β → γ} (h₁ : Surjective f) (h₂ : Surjective g) : Surjective (g ∘ f) 
  := by 
    intro c 
    have ⟨b,l₁⟩ := h₂ c 
    have ⟨a,l₂⟩ := h₁ b 
    have : g (f a) = c := by rw [l₂,l₁] 
    exact ⟨a,this⟩ 

theorem comp_inj { f : α → β } { g : β → γ } (h : Injective (g ∘ f)) : Injective f := by 
  intro a₁ a₂ h₁ 
  have : g (f a₁) = g (f a₂) := congrArg g h₁ 
  exact h this 

theorem comp_surj { f : α → β } { g : β → γ } (h : Surjective (g ∘ f)) : Surjective g := by 
  intro c 
  have ⟨a,h₁⟩ : ∃ a, g (f a) = c := h c 
  exact ⟨f a, h₁⟩ 

theorem has_left_inv_injective (f : α → β) (h : HasLeftInv f) : Injective f := by 
  -- Introduce a pair of arguments and the assumption that 
  -- f evaluates to the same on them 
  intro (a₁:α) (a₂:α) (l₁: f a₁ = f a₂)
  -- Break up the existence of a left-inverse into a function and a proof it is a
  -- left inverse
  have ⟨g,l₂⟩ := h 
  -- A calculation block allows us to more efficiently perform equality manipulations
  calc
    a₁ = id a₁        := by rfl 
    _  = (g ∘ f) a₁   := Eq.symm (congrFun l₂ a₁)
    _  = (g ∘ f) a₂   := congrArg g l₁ 
    _  = id a₂        := congrFun l₂ a₂ 
    _  = a₂           := by rfl 

def InvtoLeftInv { f : α → β } (g : Inverse f) : LeftInverse f := ⟨g.to_fun,g.invl⟩

def InvtoRightInv { f : α → β } (g : Inverse f) : RightInverse f := ⟨g.to_fun,g.invr⟩

theorem left_inv_right_inv_eq { f : α → β } (g : LeftInverse f) (h : RightInverse f) : 
  g.to_fun = h.to_fun := by
    apply funext 
    intro (b: β) 
    calc 
        g.to_fun b = g.to_fun (f (h.to_fun b))  := 
          congrArg g.to_fun (Eq.symm (congrFun h.invr b)) 
        _    = h.to_fun b                       := 
          congrFun g.invl (h.to_fun b)  

theorem inv_unique (f : α → β) (g : Inverse f) (h : Inverse f) : g.to_fun = h.to_fun := by 
  calc 
    g.to_fun = (InvtoLeftInv g).to_fun    := by rfl  
    _        = (InvtoRightInv h).to_fun   := 
      left_inv_right_inv_eq (InvtoLeftInv g) (InvtoRightInv h)   
    _        = h.to_fun                   := by rfl 

noncomputable def Section (f : α → β) (l : Nonempty α) : β → α := by 
  intro (b:β)
  have a₀ : α := Classical.choice l 
  have : Decidable (∃ a, f a = b) := Classical.propDecidable (∃ a, f a = b) 
  exact if h : ∃ a, f a = b then Classical.choose h else a₀ 

theorem inj_has_left_inv (f : α → β) (l : Nonempty α) (h : Injective f) : HasLeftInv f := by 
  let g : β → α := Section f l 
  suffices u : g ∘ f = id from ⟨g,u⟩
  apply funext 
  intro (a:α) 
  have (v : ∃ x, f x = f a) := by exists a 
  have (w : g (f a) = Classical.choose v) := dif_pos v   
  calc 
    g (f a) = Classical.choose v  := w 
    _       = a                   := h (Classical.choose_spec v)

theorem has_right_inv_surjective (f : α → β) (h : HasRightInv f) : Surjective f := by
  have ⟨g,l⟩ := h 
  intro (b:β)
  exact ⟨g b, congrFun l b⟩ 

open Set 

def Image (f : α → β) (X : Set α) : Set β := fun b => ∃ a, a ∈ X ∧ f a = b
-- infix:80 " '' " => Image
--
-- declare_syntax_cat set_image
-- syntax set_image "[" ident "]" : term
--
-- syntax ident : binder_construct
--
-- macro_rules
-- | `({ $var:ident [ $var2:ident ]}) => `(Image ($var : $ty) ($body :term) )) 

def PreImage (f : α → β) (Y : Set β) : Set α := fun a => f a ∈ Y 
infix:80 " ⁻¹ " => PreImage

theorem image_sub (f : α → β) { X X' : Set α } (h : X ⊆ X')  : Image f X ⊆ Image f X' := by 
  intro b h'
  have ⟨a,h''⟩ := h' 
  exact ⟨a,⟨h a h''.left,h''.right⟩⟩  

theorem preimage_sub (f : α → β) { Y Y' : Set β } (h : Y ⊆ Y') : f⁻¹ Y ⊆ f⁻¹ Y' := by 
  intro a h' 
  exact h (f a) h' 

theorem image_preimage_sub (f : α → β) (Y : Set β) : Image f (PreImage f Y) ⊆ Y := by 
  intro b h 
  have ⟨a,h'⟩ := h 
  rw [←h'.right]
  exact h'.left 

theorem sub_preimage_image (f : α → β) (X : Set α) : X ⊆ PreImage f (Image f X) := by 
  intro a h 
  have : f a ∈ Image f X := ⟨a,⟨h,Eq.refl (f a) ⟩⟩ 
  exact this

theorem union_preimage (f : α → β) (Y Y' : Set β) : f⁻¹ (Y ∪ Y') = f⁻¹ Y ∪ f⁻¹ Y' := by rfl 

theorem inter_preimage (f : α → β) (Y Y' : Set β) : f⁻¹ (Y ∩ Y') = f⁻¹ Y ∩ f⁻¹ Y' := by rfl 

theorem union_image (f : α → β) (X X' : Set α) : Image f (X ∪ X') = Image f X ∪ Image f X' := by 
  set_extensionality b 
  · intro h 
    have ⟨a,h'⟩ := h 
    cases h'.left with 
    | inl hl => exact Or.inl ⟨a,hl,h'.right⟩
    | inr hr => exact Or.inr ⟨a,hr,h'.right⟩ 
  · intro h 
    cases h with 
    | inl hl => 
      have ⟨a,h'⟩ := hl 
      exact ⟨a,⟨Or.inl h'.left,h'.right⟩⟩ 
    | inr hr => 
      have ⟨a,h'⟩ := hr 
      exact ⟨a,⟨Or.inr h'.left,h'.right⟩⟩ 

theorem inter_image (f : α → β) (X X' : Set α) : Image f (X ∩ X') ⊆ Image f X ∩ Image f X' := by 
  intro b h 
  have ⟨a,h'⟩ := h 
  exact ⟨⟨a,⟨h'.left.left,h'.right⟩⟩,⟨a,⟨h'.left.right,h'.right⟩⟩⟩  

def InBijection (γ δ : Type) : Prop := ∃ (f : γ → δ), Bijective f 
infixl:60 " ≅ " => InBijection

end Func
