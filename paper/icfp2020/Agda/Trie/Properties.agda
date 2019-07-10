module Trie.Properties where

   open import SharedModules
   open import Common.Algebra.Structures
   import Relation.Binary.EqReasoning as EqReasoning

   open import Trie; open Trie.Trie

   ε-⊔-rightId : ∀ {X Γ C A} (∙ : ∀ {Γ C} → Op₂ (X Γ C)) → RightIdentity _≡_ ε (flip (_⊔[_]_ {X} {Γ} {C} {A}) ∙)
   ε-⊔-rightId ∙ ε = refl
   ε-⊔-rightId ∙ (any _) = refl
   ε-⊔-rightId ∙ [ _ ] = refl

   ⊔-assoc : ∀ {X A Γ C} (∙ : ∀ {Γ C} → Op₂ (X Γ C)) →
             (∀ {Γ C} → Associative _≡_ (∙ {Γ} {C})) → Associative _≡_ (flip (_⊔[_]_ {X} {A} {Γ} {C}) ∙)
   ⊔⁻-assoc : ∀ {X A Γ C} (∙ : ∀ {Γ C} → Op₂ (X Γ C)) →
              (∀ {Γ C} → Associative _≡_ (∙ {Γ} {C})) → Associative _≡_ (flip (_⊔⁻[_]_ {X} {A} {Γ} {C}) ∙)

   ⊔-assoc _ _ ε _ _ = refl
   ⊔-assoc ∙ _ σ₁ ε σ₂ = cong (λ σ → σ ⊔[ ∙ ] σ₂) (ε-⊔-rightId ∙ σ₁)
   ⊔-assoc ∙ _ σ₁ σ₂ ε =
      begin
         (σ₁ ⊔[ ∙ ] σ₂) ⊔[ ∙ ] ε
      ≡⟨ ε-⊔-rightId ∙ _ ⟩
         σ₁ ⊔[ ∙ ] σ₂
      ≡⟨ cong (λ σ → σ₁ ⊔[ ∙ ] σ) (sym (ε-⊔-rightId ∙ _)) ⟩
         σ₁ ⊔[ ∙ ] (σ₂ ⊔[ ∙ ] ε)
      ∎ where open EqReasoning (setoid _)
   ⊔-assoc ∙ ∙-assoc (any _) (any _) (any _) = cong any (∙-assoc _ _ _)
   ⊔-assoc _ _ (any _) (any _) [ _ ] = refl
   ⊔-assoc _ _ (any _) [ _ ] (any _) = refl
   ⊔-assoc _ _ (any _) [ _ ] [ _ ] = refl
   ⊔-assoc _ _ [ _ ] (any _) (any _) = refl
   ⊔-assoc _ _ [ _ ] (any _) [ _ ] = refl
   ⊔-assoc _ _ [ _ ] [ _ ] (any _) = refl
   ⊔-assoc ∙ ∙-assoc [ _ ] [ _ ] [ _ ] = cong [_] (⊔⁻-assoc ∙ ∙-assoc _ _ _)

   {-# NO_TERMINATION_CHECK #-}
   ⊔⁻-assoc ∙ ∙-assoc (nat _) (nat _) (nat _) = cong nat (∙-assoc _ _ _)
   ⊔⁻-assoc ∙ ∙-assoc (〈〉 _) (〈〉 _) (〈〉 _) = cong 〈〉 (∙-assoc _ _ _)
   ⊔⁻-assoc ∙ ∙-assoc ⟅ σ₁ , σ₁′ ⟆ ⟅ σ₂ , σ₂′ ⟆ ⟅ σ₃ , σ₃′ ⟆ =
      cong₂ ⟅_,_⟆ (⊔-assoc ∙ ∙-assoc σ₁ σ₂ σ₃) (⊔-assoc ∙ ∙-assoc σ₁′ σ₂′ σ₃′)
   ⊔⁻-assoc ∙ ∙-assoc (↥ σ₁) (↥ σ₂) (↥ σ₃) = cong ↥ (⊔-assoc (flip _⊔[_]_ ∙) (⊔-assoc ∙ ∙-assoc) σ₁ σ₂ σ₃)
   ⊔⁻-assoc ∙ ∙-assoc (fun _) (fun _) (fun _) = cong fun (∙-assoc _ _ _)
   ⊔⁻-assoc ∙ ∙-assoc (roll σ₁) (roll σ₂) (roll σ₃) = cong roll (⊔-assoc ∙ ∙-assoc σ₁ σ₂ σ₃)

   ⊔-comm : ∀ {X A Γ C} (∙ : ∀ {Γ C} → Op₂ (X Γ C)) →
            (∀ {Γ C} → Commutative _≡_ (∙ {Γ} {C})) → Commutative _≡_ (flip (_⊔[_]_ {X} {A} {Γ} {C}) ∙)
   ⊔⁻-comm : ∀ {X A Γ C} (∙ : ∀ {Γ C} → Op₂ (X Γ C)) →
            (∀ {Γ C} → Commutative _≡_ (∙ {Γ} {C})) → Commutative _≡_ (flip (_⊔⁻[_]_ {X} {A} {Γ} {C}) ∙)

   ⊔-comm ∙ _ ε _ = sym (ε-⊔-rightId ∙ _)
   ⊔-comm ∙ _ (any _) ε = refl
   ⊔-comm ∙ _ (any _) [ _ ] = refl
   ⊔-comm ∙ ∙-comm (any _) (any _) = cong any (∙-comm _ _)
   ⊔-comm ∙ _ [ _ ] ε = refl
   ⊔-comm ∙ _ [ _ ] (any _) = refl
   ⊔-comm ∙ ∙-comm [ σ₁ ] [ σ₂ ] = cong [_] (⊔⁻-comm ∙ ∙-comm σ₁ σ₂)

   {-# NO_TERMINATION_CHECK #-}
   ⊔⁻-comm ∙ ∙-comm (nat a₁) (nat a₂) = cong nat (∙-comm a₁ a₂)
   ⊔⁻-comm ∙ ∙-comm (〈〉 a₁) (〈〉 a₂) = cong 〈〉 (∙-comm a₁ a₂)
   ⊔⁻-comm ∙ ∙-comm ⟅ σ₁ , σ₁′ ⟆ ⟅ σ₂ , σ₂′ ⟆ = cong₂ ⟅_,_⟆ (⊔-comm ∙ ∙-comm σ₁ σ₂) (⊔-comm ∙ ∙-comm σ₁′ σ₂′)
   ⊔⁻-comm ∙ ∙-comm (↥ σ₁) (↥ σ₂) = cong ↥ (⊔-comm (flip _⊔[_]_ ∙) (⊔-comm ∙ ∙-comm) σ₁ σ₂)
   ⊔⁻-comm ∙ ∙-comm (fun a₁) (fun a₂) = cong fun (∙-comm a₁ a₂)
   ⊔⁻-comm ∙ ∙-comm (roll σ₁) (roll σ₂) = cong roll (⊔-comm ∙ ∙-comm σ₁ σ₂)

   ⊔-idem : ∀ {X C Γ A} (∙ : ∀ {Γ C} → Op₂ (X Γ C)) →
            (∀ {Γ C} → Idempotent _≡_ (∙ {Γ} {C})) → Idempotent _≡_ (flip (_⊔[_]_ {X} {A} {Γ} {C}) ∙)
   ⊔⁻-idem : ∀ {X A Γ C} (∙ : ∀ {Γ C} → Op₂ (X Γ C)) →
            (∀ {Γ C} → Idempotent _≡_ (∙ {Γ} {C})) → Idempotent _≡_ (flip (_⊔⁻[_]_ {X} {A} {Γ} {C}) ∙)

   ⊔-idem ∙ _ ε = refl
   ⊔-idem ∙ ∙-idem (any a) = cong any (∙-idem a)
   ⊔-idem ∙ ∙-idem [ σ ] = cong [_] (⊔⁻-idem ∙ ∙-idem σ)

   {-# NO_TERMINATION_CHECK #-}
   ⊔⁻-idem ∙ ∙-idem (nat a) = cong nat (∙-idem a)
   ⊔⁻-idem ∙ ∙-idem (〈〉 a) = cong 〈〉 (∙-idem a)
   ⊔⁻-idem ∙ ∙-idem ⟅ σ₁ , σ₂ ⟆ = cong₂ ⟅_,_⟆ (⊔-idem ∙ ∙-idem σ₁) (⊔-idem ∙ ∙-idem σ₂)
   ⊔⁻-idem ∙ ∙-idem (↥ σ) = cong ↥ (⊔-idem (flip _⊔[_]_ ∙) (⊔-idem ∙ ∙-idem) σ)
   ⊔⁻-idem ∙ ∙-idem (fun a) = cong fun (∙-idem a)
   ⊔⁻-idem ∙ ∙-idem (roll σ) = cong roll (⊔-idem ∙ ∙-idem σ)

   {-# NO_TERMINATION_CHECK #-}
   trie-is-⊥ : ∀ {X C Γ A} → (∀ {Γ C} → X Γ C → Bool) → Trie X Γ C A → Bool
   trie-is-⊥ is-⊥ ε = true
   trie-is-⊥ is-⊥ (any a) = is-⊥ a
   trie-is-⊥ is-⊥ [ nat a ] = is-⊥ a
   trie-is-⊥ is-⊥ [ 〈〉 a ] = is-⊥ a
   trie-is-⊥ is-⊥ [ ⟅ σ , τ ⟆ ] with trie-is-⊥ is-⊥ σ | trie-is-⊥ is-⊥ τ
   ... | true | true = true
   ... | _ | _ = false
   trie-is-⊥ is-⊥ [ ↥ σ ] with trie-is-⊥ (trie-is-⊥ is-⊥) σ
   ... | true = true
   ... | _ = false
   trie-is-⊥ is-⊥ [ fun a ] = is-⊥ a
   trie-is-⊥ is-⊥ [ roll σ ] with trie-is-⊥ is-⊥ σ
   ... | true = true
   ... | _ = false

   instance
      bjs : ∀ {X Γ C A} (∙ : ∀ {Γ C} → Op₂ (X Γ C)) (⊥ : ∀ {Γ C} → X Γ C) →
            (∀ {Γ C} → IsBoundedJoinSemilattice _≡_ (∙ {Γ} {C}) ⊥) →
            IsBoundedJoinSemilattice _≡_ (flip (_⊔[_]_ {X} {Γ} {C} {A}) ∙) ε
      bjs ∙ ⊥ ∙-bjs = record {
            isCommutativeMonoid = record {
                  isSemigroup = record {
                        isEquivalence = isEquivalence;
                        assoc = ⊔-assoc ∙ (assoc ∙-bjs);
                        ∙-cong = cong₂ (flip _⊔[_]_ ∙)
                     };
                  identityˡ = λ _ → refl;
                  comm = ⊔-comm ∙ (comm ∙-bjs) };
            idem = ⊔-idem ∙ (idem ∙-bjs);
            is-⊥ = trie-is-⊥ (is-⊥ ∙-bjs)
         } where open IsBoundedJoinSemilattice hiding (isEquivalence; refl)
