-- Adapted from Hinze's "Generalizing Generalized Tries", via Conal Elliott's blog.
module Trie where

   open import SharedModules hiding (¬_)

   open import Cxt as ᶜ using («Ren; weakenᵣ†);
      open ᶜ.Cxt; open ᶜ.Substitutable ⦃...⦄ hiding (_<$>_; var)
   import Type
   open import VarCxt as ᵛᶜ using (VarCxt; Type); open ᵛᶜ.Type

   -- Trie over X, with domain A. TODO: surface syntax to hide [] argument to shiftable substitution.
   mutual
      {-# NO_POSITIVITY_CHECK #-} -- previously not required
      data Trie (X : VarCxt → Set) : Type → VarCxt → Set where
         ε : ∀ {A Γ} → Γ ⊢ A ⇀ X
         any : ∀ {A Γ} → X (Γ ‚ A) → Γ ⊢ A ⇀ X
         [_] : ∀ {A Γ} → Γ ⊢ A ⇀⁻ X → Γ ⊢ A ⇀ X

      data Trie⁻ (X : VarCxt → Set) : Type → VarCxt → Set where
         nat : ∀ {Γ} → X Γ → Γ ⊢ nat ⇀⁻ X
         〈〉 : ∀ {Γ} → X Γ → Γ ⊢ 𝟏 ⇀⁻ X
         ⟅_,_⟆ : ∀ {A B Γ} → Γ ⊢ A ⇀ X → Γ ⊢ B ⇀ X → Γ ⊢ A + B ⇀⁻ X
         ↥ : ∀ {A B Γ} → Γ ⊢ A ⇀ (λ Γ → Γ ⊢ B ⇀ X) → Γ ⊢ A ⨰ B ⇀⁻ X
         fun : ∀ {A B Γ} → X Γ → Γ ⊢ A ⇾ B ⇀⁻ X
         roll : ∀ {A Γ} → Γ ⊢ ((sub (const (μ A)) * []) A) ⇀ X → Γ ⊢ μ A ⇀⁻ X

   syntax Trie X A Γ = Γ ⊢ A ⇀ X
   syntax Trie⁻ X A Γ = Γ ⊢ A ⇀⁻ X

   {-# TERMINATING #-}
   _<$>_ : ∀ {X Γ Γ′ A} → «Ren X Γ Γ′ → «Ren (λ Γ B → Γ ⊢ A ⇀ flip X B) Γ Γ′
   _<$>⁻_ : ∀ {X Γ Γ′ A} → «Ren X Γ Γ′ → «Ren (λ Γ B → Γ ⊢ A ⇀⁻ flip X B) Γ Γ′

   (ρ <$> A∗) ε = ε
   _<$>_ {X = X} {A = A} ρ A∗ (any a) = any (weakenᵣ† X A∗ ρ (_ ∷ []) a)
   (_<$>_ {X = X} ρ A∗) [ σ ] = [ (_<$>⁻_ {X = X} ρ A∗) σ ]
   (ρ <$>⁻ A∗) (〈〉 a) = 〈〉 (ρ A∗ a)
   (ρ <$>⁻ A∗) (nat a) = nat (ρ A∗ a)
   (_<$>⁻_ {X = X} ρ A∗) ⟅ σ , τ ⟆ = ⟅ (_<$>_ {X = X} ρ A∗) σ , (_<$>_ {X = X} ρ A∗) τ ⟆
   (_<$>⁻_ {X = X} ρ A∗) (↥ {B = B} σ) = ↥ ((_<$>_ {X = λ Γ C → Γ ⊢ B ⇀ flip X C} (_<$>_ ρ) A∗) σ)
   (ρ <$>⁻ A∗) (fun a) = fun (ρ A∗ a)
   (_<$>⁻_ {X = X} ρ A∗) (roll σ) = roll ((_<$>_ {X = X} ρ A∗) σ)

   _⊔[_]_ : ∀ {X A Γ} → Γ ⊢ A ⇀ X → (∀ {Γ} → Op₂ (X Γ)) → Op₁ (Γ ⊢ A ⇀ X)
   _⊔⁻[_]_ : ∀ {X A Γ} → Γ ⊢ A ⇀⁻ X → (∀ {Γ} → Op₂ (X Γ)) → Op₁ (Γ ⊢ A ⇀⁻ X)

   ε ⊔[ _ ] σ = σ
   σ ⊔[ _ ] ε = σ
   any a ⊔[ ∙ ] any a′ = any (a ⟨ ∙ ⟩ a′)
   any a ⊔[ _ ] _ = any a
   _ ⊔[ _ ] any a = any a
   [ σ ] ⊔[ ∙ ] [ τ ] = [ σ ⊔⁻[ ∙ ] τ ]

   {-# TERMINATING #-}
   nat a ⊔⁻[ ∙ ] nat a′ = nat (a ⟨ ∙ ⟩ a′)
   〈〉 a ⊔⁻[ ∙ ] 〈〉 a′ = 〈〉 (a ⟨ ∙ ⟩ a′)
   ⟅ σ , τ ⟆ ⊔⁻[ ∙ ] ⟅ σ′ , τ′ ⟆ = ⟅ σ ⊔[ ∙ ] σ′ , τ ⊔[ ∙ ] τ′ ⟆
   ↥ σ ⊔⁻[ ∙ ] ↥ τ = ↥ (σ ⊔[ flip _⊔[_]_ ∙ ] τ)
   fun a ⊔⁻[ ∙ ] fun a′ = fun (a ⟨ ∙ ⟩ a′)
   roll σ ⊔⁻[ ∙ ] roll τ = roll (σ ⊔[ ∙ ] τ)

   -- σ ⊔ τ, minus τ. In other words, what would be discarded of τ if it were merged with σ.
   -- No need to do ε-propagation; use is-⊥ to test for (equivalence to) ε.
   {-# TERMINATING #-}
   _-[_]_ : ∀ {X Γ A} → Γ ⊢ A ⇀ X → (∀ {Γ} → Op₂ (X Γ)) → Op₁ (Γ ⊢ A ⇀ X)
   ε -[ _ ] _ = ε
   _ -[ _ ] ε = ε
   any a -[ _∙_ ] any a′ = any (a ∙ a′)
   any a -[ _ ] _ = ε
   σ -[ _ ] any _ = σ
   [ nat _ ] -[ _ ] [ nat _ ] = ε
   [ 〈〉 _ ] -[ _ ] [ 〈〉 _ ] = ε
   [ ⟅ σ , τ ⟆ ] -[ ∙ ] [ ⟅ σ′ , τ′ ⟆ ] = [ ⟅ σ -[ ∙ ] σ′ , τ -[ ∙ ] τ′ ⟆ ]
   [ ↥ σ ] -[ ∙ ] [ ↥ τ ] = [ ↥ (σ -[ flip _-[_]_ ∙ ] τ) ]
   [ fun _ ] -[ _ ] [ fun _ ] = ε
   [ roll σ ] -[ ∙ ] [ roll τ ] = [ roll (σ -[ ∙ ] τ) ]

   -- No need to do ε-propagation; use is-⊥ to test for (equivalence to) ε.
   {-# TERMINATING #-}
   filterMap : ∀ {X Y Γ A} → Γ ⊢ A ⇀ X → (∀ {Γ} → X Γ → Maybe (Y Γ)) → Γ ⊢ A ⇀ Y
   filterMap ε _ = ε
   filterMap (any a) p with p a
   ... | just a′ = any a′
   ... | nothing = ε
   filterMap [ nat a ] p with p a
   ... | just a′ = [ nat a′ ]
   ... | nothing = ε
   filterMap [ 〈〉 a ] p with p a
   ... | just a′ = [ 〈〉 a′ ]
   ... | nothing = ε
   filterMap [ ⟅ σ₁ , σ₂ ⟆ ] p = [ ⟅ filterMap σ₁ p , filterMap σ₂ p ⟆ ]
   filterMap [ ↥ σ ] p = [ ↥ (filterMap σ (λ σ′ → case filterMap σ′ p of (λ { ε → nothing; σ″ → just σ″ }))) ]
   filterMap [ fun a ] p with p a
   ... | just a′ = [ fun a′ ]
   ... | nothing = ε
   filterMap [ roll σ ] p = [ roll (filterMap σ p) ]
