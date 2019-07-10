-- We need type equality in order to define term equality. More boilerplate.
module Type.Eq where

   open import SharedModules
   open import Common.Eq using (Eq; module Eq); open Eq ⦃...⦄ renaming (_≟_ to _≟′_)

   open import Cxt using (zero; suc) renaming (∋ to _∋_)
   import Cxt.Eq
   open import Type using (Type₀); open Type

   var-injective : ∀ {Δ α β} → _≡_ {A = Type₀ Δ} (var α) (var β) → α ≡ β
   var-injective refl = refl

   +-injective : ∀ {Δ A B A′ B′} → _≡_ {A = Type₀ Δ} (A + B) (A′ + B′) → A ≡ A′ × B ≡ B′
   +-injective refl = refl , refl

   ⨰-injective : ∀ {Δ A B A′ B′} → _≡_ {A = Type₀ Δ} (A ⨰ B) (A′ ⨰ B′) → A ≡ A′ × B ≡ B′
   ⨰-injective refl = refl , refl

   ⇾-injective : ∀ {Δ A B A′ B′} → _≡_ {A = Type₀ Δ} (A ⇾ B) (A′ ⇾ B′) → A ≡ A′ × B ≡ B′
   ⇾-injective refl = refl , refl

   μ-injective : ∀ {Δ A B} → _≡_ {A = Type₀ Δ} (μ A) (μ B) → A ≡ B
   μ-injective refl = refl

   _≟_ : ∀ {Δ} → Decidable {A = Type₀ Δ} _≡_
   var α ≟ var β with α ≟′ β
   var α ≟ var .α | yes refl = yes refl
   ... | no α≢β = no (α≢β ∘ var-injective)
   var _ ≟ nat = no (λ ())
   var _ ≟ 𝟏 = no (λ ())
   var _ ≟ (_ + _) = no (λ ())
   var _ ≟ (_ ⨰ _) = no (λ ())
   var _ ≟ (_ ⇾ _) = no (λ ())
   var _ ≟ μ - = no (λ ())
   nat ≟ nat = yes refl
   nat ≟ var _ = no (λ ())
   nat ≟ 𝟏 = no (λ ())
   nat ≟ (_ + _) = no (λ ())
   nat ≟ (_ ⨰ _) = no (λ ())
   nat ≟ (_ ⇾ _) = no (λ ())
   nat ≟ μ _ = no (λ ())
   𝟏 ≟ 𝟏 = yes refl
   𝟏 ≟ var _ = no (λ ())
   𝟏 ≟ nat = no (λ ())
   𝟏 ≟ (_ + _) = no (λ ())
   𝟏 ≟ (_ ⨰ _) = no (λ ())
   𝟏 ≟ (_ ⇾ _) = no (λ ())
   𝟏 ≟ μ B = no (λ ())
   (A + B) ≟ (A′ + B′) with A ≟ A′ | B ≟ B′
   (A + B) ≟ (.A + .B) | yes refl | yes refl = yes refl
   ... | yes _ | no B≢B′ = no (B≢B′ ∘ π₂ ∘ +-injective)
   ... | no A≢A′ | yes _ = no (A≢A′ ∘ π₁ ∘ +-injective)
   ... | no A≢A′ | no _ = no (A≢A′ ∘ π₁ ∘ +-injective)
   (_ + _) ≟ var _ = no (λ ())
   (_ + _) ≟ nat = no (λ ())
   (_ + _) ≟ 𝟏 = no (λ ())
   (_ + _) ≟ (_ ⨰ _) = no (λ ())
   (_ + _) ≟ (_ ⇾ _) = no (λ ())
   (_ + _) ≟ μ _ = no (λ ())
   (A ⨰ B) ≟ (A′ ⨰ B′) with A ≟ A′ | B ≟ B′
   (A ⨰ B) ≟ (.A ⨰ .B) | yes refl | yes refl = yes refl
   ... | yes _ | no B≢B′ = no (B≢B′ ∘ π₂ ∘ ⨰-injective)
   ... | no A≢A′ | yes _ = no (A≢A′ ∘ π₁ ∘ ⨰-injective)
   ... | no A≢A′ | no _ = no (A≢A′ ∘ π₁ ∘ ⨰-injective)
   (_ ⨰ _) ≟ var _ = no (λ ())
   (_ ⨰ _) ≟ nat = no (λ ())
   (_ ⨰ _) ≟ 𝟏 = no (λ ())
   (_ ⨰ _) ≟ (_ + _) = no (λ ())
   (_ ⨰ _) ≟ (_ ⇾ _) = no (λ ())
   (_ ⨰ _) ≟ μ _ = no (λ ())
   (A ⇾ B) ≟ (A′ ⇾ B′) with A ≟ A′ | B ≟ B′
   (A ⇾ B) ≟ (.A ⇾ .B) | yes refl | yes refl = yes refl
   ... | yes _ | no B≢B′ = no (B≢B′ ∘ π₂ ∘ ⇾-injective)
   ... | no A≢A′ | yes _ = no (A≢A′ ∘ π₁ ∘ ⇾-injective)
   ... | no A≢A′ | no _ = no (A≢A′ ∘ π₁ ∘ ⇾-injective)
   (_ ⇾ _) ≟ var _ = no (λ ())
   (_ ⇾ _) ≟ nat = no (λ ())
   (_ ⇾ _) ≟ 𝟏 = no (λ ())
   (_ ⇾ _) ≟ (_ + _) = no (λ ())
   (_ ⇾ _) ≟ (_ ⨰ _) = no (λ ())
   (_ ⇾ _) ≟ μ _ = no (λ ())
   μ A ≟ μ B with A ≟ B
   μ A ≟ μ .A | yes refl = yes refl
   ... | no A≢B = no (A≢B ∘ μ-injective)
   μ _ ≟ var _ = no (λ ())
   μ _ ≟ nat = no (λ ())
   μ _ ≟ 𝟏 = no (λ ())
   μ _ ≟ (_ + _) = no (λ ())
   μ _ ≟ (_ ⨰ _) = no (λ ())
   μ _ ≟ (_ ⇾ _) = no (λ ())

   instance
      eq : ∀ {Δ} → Eq (Type₀ Δ)
      eq = record { _≟_ = _≟_ }
