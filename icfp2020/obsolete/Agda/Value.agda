module Value where

   open import SharedModules
   import Level
   open import Category.Monad; open RawMonadZero (monadZero {Level.zero}) hiding (_<$>_)

   open import Cxt as ᶜ; open ᶜ.Cxt; open ᶜ.Substitutable ⦃...⦄ hiding (var)
   open import Term as ᵉ using (Term₀)
   open import Trie as ᵀ using (Trie; Trie⁻); open ᵀ.Trie; open ᵀ.Trie⁻
   open import VarCxt as ᵛᶜ using (VarCxt; Type); open ᵛᶜ.Type

   -- Values are "partial", in that they may have variables binders in place of subtrees.
   data Value : Type → Set where
      var : ∀ {A} → Value A
      nat : ℕ → Value nat
      〈〉 : Value 𝟏
      inl : ∀ {A B} → Value A → Value (A + B)
      inr : ∀ {A B} → Value B → Value (A + B)
      〈_,_〉 : ∀ {A B} → Value A → Value B → Value (A ⨰ B)
      fun : ∀ {A B} → ε ⊢ A ⇀ flip Term₀ B → Value (A ⇾ B)
      roll : ∀ {A} → Value ((sub (const (μ A)) * []) A) → Value (μ A)

   vars : ∀ {A} → Value A → VarCxt
   vars (var {A}) = ε ‚ A
   vars (nat _) = ε
   vars 〈〉 = ε
   vars (inl v) = vars v
   vars (inr v) = vars v
   vars 〈 v₁ , v₂ 〉 = vars v₁ +++ vars v₂
   vars (fun _) = ε
   vars (roll v) = vars v

   -- (Key, codomain element) pair.
   Match : (VarCxt → Type → Set) → Type → VarCxt → Type → Set
   Match X A Γ C = Σ[ p ∈ Value A ] X (Γ +++ vars p) C

   -- Not used explicitly in the semantics, but a useful sanity-check. TODO: in the paper I use this.
   -- Returns the matched prefix of the supplied value in the event of a match, and nothing otherwise.
   lookup : ∀ {X Γ C A} → Value A → Γ ⊢ A ⇀ flip X C → Maybe (Match X A Γ C)
   lookup⁻ : ∀ {X Γ C A} → Value A → Γ ⊢ A ⇀⁻ flip X C → Maybe (Match X A Γ C)

   lookup _ ε = ∅
   lookup v (any a) = return (var , a)
   lookup {X} v [ σ ] = lookup⁻ {X} v σ

   lookup⁻ var σ = ∅
   lookup⁻ (nat n) (nat a) = return (nat n , a)
   lookup⁻ 〈〉 (〈〉 a) = return (〈〉 , a)
   lookup⁻ {X} (inl v) ⟅ σ₁ , _ ⟆ =
      lookup {X} v σ₁ >>= λ { (p , a) →
      return (inl p , a) }
   lookup⁻ {X} (inr v) ⟅ _ , σ₂ ⟆ =
      lookup {X} v σ₂ >>= λ { (p , a) →
      return (inr p , a) }
   lookup⁻ {X} {Γ} {C} 〈 v₁ , v₂ 〉 (↥ σ₁) =
      lookup {λ Γ B → Γ ⊢ B ⇀ flip X C} v₁ σ₁ >>= λ { (p₁ , σ₂) →
      lookup {X} v₂ σ₂ >>= λ { (p₂ , a) →
      return (〈 p₁ , p₂ 〉 , subst (λ Γ → X Γ C) (+++-assoc Γ _ (vars p₂)) a) } }
   lookup⁻ (fun σ) (fun a) = return (fun σ , a)
   lookup⁻ {X} (roll v) (roll σ) = lookup {X} v σ >>= λ { (p , a) → return (roll p , a) }
