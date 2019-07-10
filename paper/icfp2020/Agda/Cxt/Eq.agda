module Cxt.Eq where

   open import SharedModules
   open import Common.Eq using (Eq)

   open import Cxt as ᶜ using () renaming (∋ to _∋_); open ᶜ.Cxt; open ᶜ._∈_

   suc-injective : ∀ {𝑨 : Set} {a a′ : 𝑨} {Γ x y} → _≡_ {A = (Γ ‚ a) ∋ a′} (suc x) (suc y) → x ≡ y
   suc-injective refl = refl

   _≟_ : ∀ {𝑨 : Set} {a : 𝑨} {Γ} → Decidable {A = Γ ∋ a} _≡_
   zero ≟ zero = yes refl
   zero ≟ suc _ = no (λ ())
   suc _ ≟ zero = no (λ ())
   suc x ≟ suc y with x ≟ y
   suc x ≟ suc .x | yes refl = yes refl
   ... | no x≢y = no (x≢y ∘ suc-injective)

   instance
      eq : ∀ {𝑨 : Set} {a : 𝑨} {Γ} → Eq (Γ ∋ a)
      eq = record { _≟_ = _≟_ }
