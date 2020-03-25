module Term where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Cxt as ᶜ using (Cxt; ∋; Ren; «Ren; «Sub; «-preserves-++; weakenᵣ†; weaken†; Substitutable);
      open ᶜ.Cxt; open ᶜ.Substitutable ⦃...⦄ hiding (var; _<$>_) renaming (_*_ to _*′_)
   open import Trie using (Trie); open Trie.Trie
   import Type
   open import VarCxt as ᵛᶜ using (VarCxt; Type); open ᵛᶜ.Type

   -- Omit projections and unroll, which can be expressed with pattern-matching.
   data Term (X : VarCxt → Type → Set) (Γ : VarCxt) : Type → Set where
      var : ∀ {A} → X Γ A → Term X Γ A
      nat : ℕ → Term X Γ nat
      op : Op₂ ℕ → Op₂ (Term X Γ nat)
      〈〉 : Term X Γ 𝟏
      inl : ∀ {A B} → Term X Γ A → Term X Γ (A + B)
      inr : ∀ {A B} → Term X Γ B → Term X Γ (A + B)
      match_as_ : ∀ {A B} → Term X Γ A → Γ ⊢ A ⇀ flip (Term X) B → Term X Γ B
      〈_,_〉 : ∀ {A B} → Term X Γ A → Term X Γ B → Term X Γ (A ⨰ B)
      fun : ∀ {A B} → Γ ⊢ A ⇀ flip (Term X) B → Term X Γ (A ⇾ B)
      app : ∀ {A B} → Term X Γ (A ⇾ B) → Term X Γ A → Term X Γ B
      roll : ∀ {A} → Term X Γ ((sub (const (μ A)) *′ []) A) → Term X Γ (μ A)

   -- Term over context membership.
   Term₀ : VarCxt → Type → Set
   Term₀ = Term ∋

   syntax Term₀ Γ A = Γ ⊢ A

   ClosedTerm₀ : Type → Set
   ClosedTerm₀ = Term₀ ε

   syntax ClosedTerm₀ A = ⊢ A

   {-# NO_TERMINATION_CHECK #-}
   _<$>_ : ∀ {X Γ Γ′} → «Ren X Γ Γ′ → «Ren (Term X) Γ Γ′
   (ρ <$> A∗) (var x) = var (ρ A∗ x)
   (ρ <$> A∗) (nat n) = nat n
   (ρ <$> A∗) (op ⊕ e₁ e₂) = op ⊕ ((ρ <$> A∗) e₁) ((ρ <$> A∗) e₂)
   (ρ <$> A∗) 〈〉 = 〈〉
   (ρ <$> A∗) (inl e) = inl ((ρ <$> A∗) e)
   (ρ <$> A∗) (inr e) = inr ((ρ <$> A∗) e)
   (_<$>_ {X} ρ A∗) (match e as σ) = match (ρ <$> A∗) e as (Trie._<$>_ {X = Term X} (_<$>_ (weakenᵣ† X A∗ ρ)) []) σ
   (ρ <$> A∗) 〈 e₁ , e₂ 〉 = 〈 (ρ <$> A∗) e₁ , (ρ <$> A∗) e₂ 〉
   (_<$>_ {X} ρ A∗) (fun σ) = fun ((Trie._<$>_ {X = Term X} (_<$>_ (weakenᵣ† X A∗ ρ)) []) σ)
   (ρ <$> A∗) (app e₁ e₂) = app ((ρ <$> A∗) e₁) ((ρ <$> A∗) e₂)
   (ρ <$> A∗) (roll e) = roll ((ρ <$> A∗) e)

   {-# NO_TERMINATION_CHECK #-}
   _*_ : ∀ {X Γ Γ′} → «Sub X Term Γ Γ′ → «Ren (Term X) Γ Γ′
   (θ * A∗) (var x) = θ A∗ x
   (θ * A∗) (nat n) = nat n
   (θ * A∗) (op ⊕ e₁ e₂) = op ⊕ ((θ * A∗) e₁) ((θ * A∗) e₂)
   (θ * A∗) 〈〉 = 〈〉
   (θ * A∗) (inl e) = inl ((θ * A∗) e)
   (θ * A∗) (inr e) = inr ((θ * A∗) e)
   (_*_ {X = X} θ A∗) (match e as σ) = match (θ * A∗) e as (Trie._<$>_ {X = Term X} (_*_ θ) A∗) σ
   (θ * A∗) 〈 e₁ , e₂ 〉 = 〈 (θ * A∗) e₁ , (θ * A∗) e₂ 〉
   (_*_ {X = X} θ A∗) (fun σ) = fun ((Trie._<$>_ {X = Term X} (_*_ θ) A∗) σ)
   (θ * A∗) (app e₁ e₂) = app ((θ * A∗) e₁) ((θ * A∗) e₂)
   (θ * A∗) (roll e) = roll ((θ * A∗) e)

   instance
      substitutable : Substitutable Type
      substitutable = record { Y = Term; _<$>_ = _<$>_; var = var; _*_ = _*_ }
