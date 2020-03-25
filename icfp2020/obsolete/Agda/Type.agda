-- There is a certain amount of (unneeded) generality in the syntax of types to make substitution uniform. For <$>,
-- it would be enough to Ren ∋; for * we could return just a regular (not shiftable) renaming.
module Type where

   open import SharedModules
   open import Cxt as ᶜ using (TermType; Cxt; _∈_; «Sub; Ren; «Ren; weakenᵣ†; weaken†; Substitutable); open ᶜ.Cxt

   -- Type over X, using de Bruijn indices.
   data Type (X : Cxt ⊤ → Set) (Δ : Cxt ⊤) : Set where
      var : X Δ → Type X Δ
      nat : Type X Δ
      𝟏 : Type X Δ
      _+_ _⨰_ _⇾_ : Type X Δ → Type X Δ → Type X Δ
      μ : Type X (Δ ‚ ⋆) → Type X Δ

   infixl 7 _⨰_
   infixl 6 _+_

   _<$>_ : ∀ {X Δ Δ′} → «Ren (flip (const X)) Δ Δ′ → «Ren (flip (const (Type X))) Δ Δ′
   (ρ <$> ∗) (var x) = var (ρ ∗ x)
   (_ <$> ∗) nat = nat
   (_ <$> ∗) 𝟏 = 𝟏
   (ρ <$> ∗) (A + B) = ((ρ <$> ∗) A) + ((ρ <$> ∗) B)
   (ρ <$> ∗) (A ⨰ B) = ((ρ <$> ∗) A) ⨰ ((ρ <$> ∗) B)
   (ρ <$> ∗) (A ⇾ B) = ((ρ <$> ∗) A) ⇾ ((ρ <$> ∗) B)
   (_<$>_ {X} ρ ∗) (μ A) = μ ((weakenᵣ† (λ Δ _ → X Δ) ∗ ρ <$> (_ ∷ [])) A)

   Y : TermType ⊤ → TermType ⊤
   Y X = flip (const (Type (flip X ⋆)))

   _*_ : ∀ {X Δ Δ′} → «Sub X Y Δ Δ′ → «Ren (Y X) Δ Δ′
   (θ * ∗) (var x) = θ ∗ x
   (_ * ∗) nat = nat
   (_ * ∗) 𝟏 = 𝟏
   (θ * ∗) (A + B) = ((θ * ∗) A) + ((θ * ∗) B)
   (θ * ∗) (A ⨰ B) = ((θ * ∗) A) ⨰ ((θ * ∗) B)
   (θ * ∗) (A ⇾ B) = ((θ * ∗) A) ⇾ ((θ * ∗) B)
   (_*_ {X = X} θ ∗) (μ A) = μ (((weaken† X Y ∗ θ) * (_ ∷ [])) A)

   instance
      substitutable : Substitutable ⊤
      substitutable = record { Y = Y; _<$>_ = _<$>_; var = var; _*_ = _*_ }

   Type₀ : Cxt ⊤ → Set
   Type₀ = Type (_∈_ ⋆)

   ClosedType : (Cxt ⊤ → Set) → Set
   ClosedType X = Type X ε
