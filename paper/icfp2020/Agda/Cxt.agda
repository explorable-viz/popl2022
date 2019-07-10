module Cxt where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   -- Contexts are snoc lists over some set.
   data Cxt (𝑨 : Set) : Set where
      ε : Cxt 𝑨
      _‚_ : Cxt 𝑨 → 𝑨 → Cxt 𝑨
   infixl 5 _‚_

   -- Context membership (de Bruijn indices).
   data _∈_ {𝑨 : Set} (a : 𝑨) : Cxt 𝑨 → Set where
      zero : ∀ {Γ} → a ∈ Γ ‚ a
      suc : ∀ {Γ b} → a ∈ Γ → a ∈ Γ ‚ b
   infix 3 _∈_

   -- Abstract notion of term over a set.
   TermType : Set → Set₁
   TermType 𝑨 = Cxt 𝑨 → 𝑨 → Set

   -- Better defined as a prefix operator, since we only pass it as a parameter.
   ∋ : ∀ {𝑨} → TermType 𝑨
   ∋ = flip _∈_

   -- Concatenation of contexts.
   infixr 5 _+++_
   _+++_ : ∀ {𝑨} → Cxt 𝑨 → Cxt 𝑨 → Cxt 𝑨
   Γ +++ ε = Γ
   Γ +++ (Γ′ ‚ A) = (Γ +++ Γ′) ‚ A

   ε-leftZero : ∀ {𝑨} → LeftIdentity _≡_ (ε {𝑨}) _+++_
   ε-leftZero ε = refl
   ε-leftZero (Γ ‚ A) = cong (flip _‚_ A) (ε-leftZero Γ)

   +++-assoc : ∀ {𝑨} → Associative _≡_ (_+++_ {𝑨})
   +++-assoc Γ ε Γ′ = cong (_+++_ Γ) (sym (ε-leftZero Γ′))
   +++-assoc _ _ ε = refl
   +++-assoc ε Γ Γ′ =
      begin
         (ε +++ Γ) +++ Γ′
      ≡⟨ cong (flip _+++_ Γ′) (ε-leftZero Γ) ⟩
         Γ +++ Γ′
      ≡⟨ sym (ε-leftZero (Γ +++ Γ′)) ⟩
         ε +++ (Γ +++ Γ′)
      ∎ where open EqReasoning (setoid _)
   +++-assoc (_ ‚ A) (_ ‚ B) (Γ ‚ C) = cong (flip _‚_ C) (+++-assoc _ _ Γ)

   -- Conor's "friendly fish" <>< operator.
   _«_ : ∀ {𝑨} → Cxt 𝑨 → List 𝑨 → Cxt 𝑨
   Γ « [] = Γ
   Γ « (a ∷ a∗) = Γ ‚ a « a∗
   infixl 4 _«_

   -- « preserves append.
   «-preserves-++ : ∀ {𝑨} Γ (a∗ a∗′ : List 𝑨) → (Γ « a∗ ++ a∗′) ≡ (Γ « a∗ « a∗′)
   «-preserves-++ _ [] _ = refl
   «-preserves-++ Γ (a ∷ a∗) a∗′ = «-preserves-++ (Γ ‚ a) a∗ a∗′

   -- Renaming over X.
   Ren : ∀ {𝑨} → TermType 𝑨 → Cxt 𝑨 → Cxt 𝑨 → Set
   Ren X Γ Γ′ = ∀ {a} → X Γ a → X Γ′ a

   -- Shiftable renaming over X.
   «Ren : ∀ {𝑨} → TermType 𝑨 → Cxt 𝑨 → Cxt 𝑨 → Set
   «Ren X Γ Γ′ = ∀ a∗ → Ren X (Γ « a∗) (Γ′ « a∗)

   -- Substitution over X.
   Sub : ∀ {𝑨} → TermType 𝑨 → (TermType 𝑨 → TermType 𝑨) → Cxt 𝑨 → Cxt 𝑨 → Set
   Sub X Y Γ Γ′ = ∀ {a} → X Γ a → Y X Γ′ a

   -- Substitution which can be shifted under a list of additional binders, a la Conor.
   «Sub : ∀ {𝑨} → TermType 𝑨 → (TermType 𝑨 → TermType 𝑨) → Cxt 𝑨 → Cxt 𝑨 → Set
   «Sub X Y Γ Γ′ = ∀ a∗ → Sub X Y (Γ « a∗) (Γ′ « a∗)

   -- Seems redundant to need these in addition to notions of shiftable renamings/substitutions.
   weakenᵣ† : ∀ {𝑨} X {Γ Γ′} (a∗ : List 𝑨) → «Ren X Γ Γ′ → «Ren X (Γ « a∗) (Γ′ « a∗)
   weakenᵣ† _ {Γ = Γ} {Γ′} a∗ ρ a∗′ rewrite sym («-preserves-++ Γ a∗ a∗′) | sym («-preserves-++ Γ′ a∗ a∗′) = ρ (a∗ ++ a∗′)

   weaken† : ∀ {𝑨} X Y {Γ Γ′} (a∗ : List 𝑨) → «Sub X Y Γ Γ′ → «Sub X Y (Γ « a∗) (Γ′ « a∗)
   weaken† _ _ {Γ = Γ} {Γ′} a∗ θ a∗′ rewrite sym («-preserves-++ Γ a∗ a∗′) | sym («-preserves-++ Γ′ a∗ a∗′) = θ (a∗ ++ a∗′)

   record Substitutable (𝑨 : Set) : Set₁ where
      field
         -- Endofunctor of terms.
         Y : TermType 𝑨 → TermType 𝑨
      field
         -- Notion of renaming used to define weakening for substitutions.
         _<$>_ : ∀ {X Γ Γ′} → «Ren X Γ Γ′ → «Ren (Y X) Γ Γ′
         -- Promote context membership to a term.
         var : ∀ {Γ a} → a ∈ Γ → Y ∋ Γ a
         -- Shiftable substitution.
         _*_ : ∀ {X Γ Γ′} → «Sub X Y Γ Γ′ → «Ren (Y X) Γ Γ′

      weaken : ∀ {Γ Γ′ : Cxt 𝑨} {a : 𝑨} → Sub ∋ Y Γ Γ′ → Sub ∋ Y (Γ ‚ a) (Γ′ ‚ a)
      weaken θ zero = var zero
      weaken θ (suc x) = (ren suc <$> []) (θ x)
         where
            -- Weaken a renaming.
            weakenᵣ : ∀ {𝑨} {Γ Γ′ : Cxt 𝑨} {a : 𝑨} → Ren ∋ Γ Γ′ → Ren ∋ (Γ ‚ a) (Γ′ ‚ a)
            weakenᵣ ρ zero = zero
            weakenᵣ ρ (suc x) = suc (ρ x)

            -- Make a renaming shiftable.
            ren : ∀ {𝑨} {Γ Γ′ : Cxt 𝑨} → Ren ∋ Γ Γ′ → «Ren ∋ Γ Γ′
            ren ρ [] = ρ
            ren ρ (_ ∷ a∗) = ren (weakenᵣ ρ) a∗

      -- Make a substitution shiftable.
      sub : ∀ {Γ Γ′ : Cxt 𝑨} → Sub ∋ Y Γ Γ′ → «Sub ∋ Y Γ Γ′
      sub θ [] = θ
      sub θ (_ ∷ a∗) = sub (weaken θ) a∗

   record Substitutable′ {𝑨 : Set} (Y : TermType 𝑨 → TermType 𝑨) : Set₁ where
      field
         -- Notion of renaming used to define weakening for substitutions.
         _<$>_ : ∀ {X Γ Γ′} → «Ren X Γ Γ′ → «Ren (Y X) Γ Γ′
