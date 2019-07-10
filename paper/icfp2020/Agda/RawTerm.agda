-- Term that makes use of conventional pattern-matching syntax, instead of using tries directly.
module RawTerm where

   open import SharedModules

   open import Cxt as ᶜ using (_+++_) renaming (∋ to _∋_); open ᶜ.Cxt; open ᶜ.Substitutable ⦃...⦄ hiding (var)
   open import Trie as ᵀ using (Trie; _⊔[_]_); open ᵀ.Trie; open ᵀ.Trie⁻
   open import VarCxt as ᵛᶜ using (VarCxt; Type); open ᵛᶜ.Type

   -- A pattern is like a partial value, except that there are no "nat" patterns.
   data Pattern : Type → Set where
      var : ∀ {A} → Pattern A
      〈〉 : Pattern 𝟏
      inl : ∀ {A B} → Pattern A → Pattern (A + B)
      inr : ∀ {A B} → Pattern B → Pattern (A + B)
      〈_,_〉 : ∀ {A B} → Pattern A → Pattern B → Pattern (A ⨰ B)
      roll : ∀ {A} → Pattern ((sub (const (μ A)) * []) A) → Pattern (μ A)

   vars : ∀ {A} → Pattern A → VarCxt
   vars (var {A}) = ε ‚ A
   vars 〈〉 = ε
   vars (inl p) = vars p
   vars (inr p) = vars p
   vars 〈 p₁ , p₂ 〉 = vars p₁ +++ vars p₂
   vars (roll p) = vars p

   mutual
      -- Branch of a match (or "arm" of a case, if you prefer).
      Branch : Type → VarCxt → Type → Set
      Branch A Γ B = Σ[ p ∈ Pattern A ] (RawTerm (Γ ᶜ.+++ vars p) B)

      data RawTerm (Γ : VarCxt) : Type → Set where
         var : ∀ {A} → Γ ∋ A → RawTerm Γ A
         nat : ℕ → RawTerm Γ nat
         〈〉 : RawTerm Γ 𝟏
         inl : ∀ {A B} → RawTerm Γ A → RawTerm Γ (A + B)
         inr : ∀ {A B} → RawTerm Γ B → RawTerm Γ (A + B)
         match_as_ : ∀ {A B} → RawTerm Γ A → List (Branch A Γ B) → RawTerm Γ B
         〈_,_〉 : ∀ {A B} → RawTerm Γ A → RawTerm Γ B → RawTerm Γ (A ⨰ B)
         fst : ∀ {A B} → RawTerm Γ (A ⨰ B) → RawTerm Γ A
         snd : ∀ {A B} → RawTerm Γ (A ⨰ B) → RawTerm Γ B
         fun : ∀ {A B} → List (Branch A Γ B) → RawTerm Γ (A ⇾ B)
         app : ∀ {A B} → RawTerm Γ (A ⇾ B) → RawTerm Γ A → RawTerm Γ B
         roll : ∀ {A} → RawTerm Γ ((sub (const (μ A)) * []) A) → RawTerm Γ (μ A)

   Body : VarCxt → Type → Set
   Body Γ A = Maybe (ℕ × RawTerm Γ A)
