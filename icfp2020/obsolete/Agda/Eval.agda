module Eval where

   open import SharedModules hiding (_⇒_)

   open import Cxt as ᶜ using (Sub; ∋); open ᶜ.Cxt; open ᶜ._∈_; open ᶜ.Substitutable ⦃...⦄ hiding (var)
   open import Trie as ᵀ using (Trie); open ᵀ.Trie; open ᵀ.Trie⁻
   open import Term as ᵉ using (Term; Term₀; ClosedTerm₀); open ᵉ.Term
   import Type
   open import Value as ᵛ using (Value; vars); open ᵛ.Value
   open import VarCxt as ᵛᶜ using (VarCxt; Type); open ᵛᶜ.Type

   -- Easier to work with an inductive definition and then relate to the functional definition.
   data Sub† : VarCxt → Set where
      ε : Sub† ε
      _‚_ : ∀ {Γ A} → Sub† Γ → ⊢ A → Sub† (Γ ‚ A)

   -- Also convenient to state the domain of the substitution as ε +++ Γ rather than Γ.
   ⟦_⟧ : ∀ {Γ} → Sub† Γ → Sub ∋ Term (ε ᶜ.+++ Γ) ε
   ⟦ ε ⟧ ()
   ⟦ _ ‚ e ⟧ zero = e
   ⟦ θ ‚ _ ⟧ (suc x) = ⟦ θ ⟧ x

   infixr 5 _+++_
   {-# TERMINATING #-} -- wasn't required previously?
   _+++_ : ∀ {Γ Γ′} → Sub† Γ → Sub† Γ′ → Sub† (Γ ᶜ.+++ Γ′)
   θ +++ ε = θ
   θ +++ (θ′ ‚ v) = θ +++ θ′ ‚ v

   -- Similar to a lookup match, but additionally equipped with a closing substitution for p.
   Result : (VarCxt → Set) → Type → VarCxt → Set
   Result X A Γ = Σ[ v ∈ Value A ] Sub† (vars v) × X (Γ ᶜ.+++ vars v)

   -- Demand-indexed evaluation over X. No rule for ε demand. TODO: sort out all the explicit Xs!
   data _⇒_~_ {X Γ} : ∀ {A} → ⊢ A → Γ ⊢ A ⇀ X → Result X A Γ → Set where
      any : ∀ {A a} {e : ⊢ A} → e ⇒ any a ~ var , (ε ‚ e) , a
      nat : ∀ {a n} → nat n ⇒ [ nat a ] ~ nat n , ε , a
      op : ∀ {a _⊕_ e₁ e₂ n m} {a† a‡ : X Γ} →
           _⇒_~_ {X} e₁ [ nat a† ] (nat n , ε , a†) → _⇒_~_ {X} e₂ [ nat a‡ ] (nat m , ε , a‡) →
           op _⊕_ e₁ e₂ ⇒ [ nat a ] ~ nat (n ⊕ m), ε , a
      〈〉 : ∀ {a} → 〈〉 ⇒ [ 〈〉 a ] ~ 〈〉 , ε , a
      inl : ∀ {A B v a θ σ₁} {e : ⊢ A} {σ₂ : Γ ⊢ B ⇀ X} →
            e ⇒ σ₁ ~ (v , θ , a) → inl e ⇒ [ ⟅ σ₁ , σ₂ ⟆ ] ~ inl v , θ , a
      inr : ∀ {A B v a θ σ₂} {e : ⊢ B} {σ₁ : Γ ⊢ A ⇀ X} →
            e ⇒ σ₂ ~ (v , θ , a) → inr e ⇒ [ ⟅ σ₁ , σ₂ ⟆ ] ~ inr v , θ , a
      match_as_ : ∀ {A B e σ v v′ θ θ′ e′ a} {τ : ε ⊢ A ⇀ flip Term₀ B} →
                  e ⇒ τ ~ (v , θ , e′) → ((sub ⟦ θ ⟧ * []) e′) ⇒ σ ~ (v′ , θ′ , a) →
                  match e as τ ⇒ σ ~ v′ , θ′ , a
      〈_,_〉 : ∀ {A B v₁ σ₁ σ₂ v₂ θ₁ θ₂ a} {e₁ : ⊢ A} {e₂ : ⊢ B} →
              e₁ ⇒ σ₁ ~ (v₁ , θ₁ , σ₂) → e₂ ⇒ σ₂ ~ (v₂ , θ₂ , a) →
              let a′ = subst X (ᶜ.+++-assoc Γ _ (vars v₂)) a in
              〈 e₁ , e₂ 〉 ⇒ [ ↥ σ₁ ] ~ 〈 v₁ , v₂ 〉 , θ₁ +++ θ₂ , a′
      fun : ∀ {A B a} {σ : Trie (flip Term₀ B) A ε} → fun σ ⇒ [ fun a ] ~ fun σ , ε , a
      app : ∀ {A B σ v v′ θ θ′ a e} {e₁ : ⊢ A ⇾ B} {e₂ : ⊢ A} {τ : Trie (flip Term₀ B) A ε} {a† : X Γ} →
            _⇒_~_ {X} e₁ [ fun a† ] (fun τ , ε , a†) → e₂ ⇒ τ ~ (v , θ , e) →
            ((sub ⟦ θ ⟧ * []) e) ⇒ [ σ ] ~ (v′ , θ′ , a) → app e₁ e₂ ⇒ [ σ ] ~ v′ , θ′ , a
      roll : ∀ {A v a e θ} {σ : Trie X ((sub (const (μ A)) * []) A) Γ} →
             e ⇒ σ ~ (v , θ , a) → roll {A = A} e ⇒ [ roll σ ] ~ roll v , θ , a

   infix 0 _⇒_~_

   -- For illustrative purposes, an evaluation judgement for a top-level closed program.
   TopLevelDemand : Type → Set
   TopLevelDemand = flip (Trie (const ⊤)) ε

   _⇒₀_~_ : ∀ {A} → ⊢ A → TopLevelDemand A → Σ[ v ∈ Value A ] Sub† (vars v) → Set
   e ⇒₀ σ ~ v , θ = _⇒_~_ {X = const ⊤} e σ (v , θ , ⋆)

   infix 0 _⇒₀_~_
