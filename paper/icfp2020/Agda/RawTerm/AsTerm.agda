-- Convert well-formed raw term to term.
module RawTerm.AsTerm where

   open import SharedModules
   import Common.Data.Product.Eq
   open import Common.Eq using (Eq; module Eq); open Eq ⦃...⦄ renaming (_≟_ to _≟′_)

   import Cxt as ᶜ; open ᶜ.Cxt; open ᶜ._∈_
   open import RawTerm as ᵉ using (RawTerm; Pattern; Body; Branch; vars); open ᵉ.Pattern; open ᵉ.RawTerm
   import RawTerm.Eq
   open import Term using () renaming (Term₀ to Term); open Term.Term
   open import Trie as ᵀ using (Trie; _⊔[_]_; filterMap; _-[_]_); open ᵀ.Trie; open ᵀ.Trie⁻
   open import Trie.Properties using (trie-is-⊥)

   -- Singleton trie.
   singleton : ∀ {X Γ B A} (p : Pattern B) → X (Γ ᶜ.+++ vars p) A → Trie X B Γ A
   singleton var a = any a
   singleton 〈〉 a = [ 〈〉 a ]
   singleton (inl p) a = [ ⟅ singleton p a , ε ⟆ ]
   singleton (inr p) a = [ ⟅ ε , singleton p a ⟆ ]
   singleton {Γ = Γ} 〈 p₁ , p₂ 〉 a rewrite sym (ᶜ.+++-assoc Γ (vars p₁) (vars p₂)) =
      [ ↥ (singleton p₁ (singleton p₂ a)) ]
   singleton (roll p) a = [ roll (singleton p a) ]

   _⊔_ : ∀ {Γ A} → Op₂ (Body Γ A)
   _⊔_ = _⊓_ _≟′_ where open import Common.Data.Maybe.Properties; open Semilattice

   - : ∀ {Γ A} → Op₂ (Body Γ A)
   - = const (const nothing)

   -- Tag each branch with its position in the sequence, so equal expressions are still distinguished.
   clause : ∀ {A Γ B} → ℕ → Branch A Γ B → Trie Body A Γ B
   clause n (p , e) = singleton p (just (n , e))

   -- If two expressions with the same tag are merged (erased), the branches have overlapping patterns.
   trie : ∀ {A Γ B} → List (Branch A Γ B) → Trie Body A Γ B
   trie [] = ε
   trie (b ∷ b∗) = trie b∗ ⊔[ _⊔_ ] (clause (length b∗) b)

   -- Subsumption is not the same as overlapping (see 0.6.11 notes). Could generalise to arbitrary tries.
   no-subsumption : ∀ {Γ C A} → Trie Body A Γ C → Trie Body A Γ C → Bool
   no-subsumption σ τ = trie-is-⊥ is-nothing (σ -[ - ] τ) ∧ trie-is-⊥ is-nothing (τ -[ - ] σ)

   all-reachable : ∀ {A Γ B} → List (Branch A Γ B) → Bool
   all-reachable [] = true
   all-reachable (b ∷ b∗) = all-reachable b∗ ∧ no-subsumption (clause (length b∗) b) (trie b∗)

   -- Filter a trie to contain only overlapping (erased) clauses.
   overlapping : ∀ {A B} → Trie Body A ε B → Trie Body A ε B
   overlapping σ = filterMap σ (λ { (just _) → nothing; nothing → just nothing })

   -- If the result is empty, the original trie had no overlapping patterns.
   no-overlapping : ∀ {A B} → Trie Body A ε B → Bool
   no-overlapping = trie-is-⊥ is-nothing ∘ overlapping

   {-# NO_TERMINATION_CHECK #-}
   asTerm : ∀ {Γ A} → RawTerm Γ A → Term Γ A
   trie′ : ∀ {A Γ B} → List (Branch A Γ B) → Trie Term A Γ B

   asTerm (var x) = var x
   asTerm (nat n) = nat n
   asTerm 〈〉 = 〈〉
   asTerm (inl e) = inl (asTerm e)
   asTerm (inr e) = inr (asTerm e)
   asTerm (match e as b∗) = match asTerm e as trie′ b∗
   asTerm 〈 e₁ , e₂ 〉 = 〈 asTerm e₁ , asTerm e₂ 〉
   asTerm (fst e) = match (asTerm e) as [ ↥ (any (any (var (suc zero)))) ]
   asTerm (snd e) = match (asTerm e) as [ ↥ (any (any (var zero))) ]
   asTerm (fun b∗) = fun (trie′ b∗)
   asTerm (app e₁ e₂) = app (asTerm e₁) (asTerm e₂)
   asTerm (roll e) = roll (asTerm e)

   trie′ b∗ = filterMap (trie b∗) (λ { (just (_ , e)) → just (asTerm e); nothing → nothing })
