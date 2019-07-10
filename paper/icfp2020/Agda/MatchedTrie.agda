module MatchedTrie where

   open import SharedModules hiding (¬_)
   import Level
   open import Category.Monad; open RawMonadZero (monadZero {Level.zero}) hiding (_<$>_)

   open import Cxt as ᶜ using («Ren; weakenᵣ†);
      open ᶜ.Cxt; open ᶜ.Substitutable ⦃...⦄ hiding (_<$>_; var)
   open import Term as ᵉ using (Term₀)
   open import Trie
   import Type
   open import VarCxt as ᵛᶜ using (VarCxt; Type); open ᵛᶜ.Type
   open import Value

   mutual
      -- This allows arbitrary combinations of live/dead constructors.
      data MatchedTrie (K : VarCxt → Set) : Type → VarCxt → Set where
         ε : ∀ {A Γ} → Γ ⊢ A ⥬ K
         [_] : ∀ {A Γ} → Γ ⊢ A ⇀ K → Γ ⊢ A ⥬ K
         any : ∀ {A Γ} → K (Γ ‚ A) → Γ ⊢ A ⥬ K
         nat : ∀ {Γ} → ℕ → K Γ → Γ ⊢ nat ⥬ K
         〈〉 : ∀ {Γ} → K Γ → Γ ⊢ 𝟏 ⥬ K
         ⟅⟅_,_⟆ : ∀ {A B Γ} → Γ ⊢ A ⥬ K → Γ ⊢ B ⇀ K → Γ ⊢ A + B ⥬ K
         ⟅_,_⟆⟆ : ∀ {A B Γ} → Γ ⊢ A ⇀ K → Γ ⊢ B ⥬ K → Γ ⊢ A + B ⥬ K
         ↥ : ∀ {A B Γ} → Γ ⊢ A ⥬ (λ Γ → Γ ⊢ B ⥬ K) → Γ ⊢ A ⨰ B ⥬ K
         fun : ∀ {A B Γ} → ε ⊢ A ⇀ flip Term₀ B → K Γ → Γ ⊢ A ⇾ B ⥬ K
         roll : ∀ {A Γ} → Γ ⊢ ((sub (const (μ A)) * []) A) ⥬ K → Γ ⊢ μ A ⥬ K

   syntax MatchedTrie K A Γ = Γ ⊢ A ⥬ K
   {-# NO_TERMINATION_CHECK #-}
   mapTrie : ∀ {K K′ : VarCxt → Set} {Γ A} →
          (f : ∀ {Γ} → K Γ → K′ Γ) → Γ ⊢ A ⇀ K → Γ ⊢ A ⇀ K′
   mapTrie f ε = ε
   mapTrie f (any κ) = any (f κ)
   mapTrie f [ nat κ ] = [ nat (f κ) ]
   mapTrie f [ 〈〉 κ ] = [ 〈〉 (f κ) ]
   mapTrie f [ ⟅ σ₁ , σ₂ ⟆ ] = [ ⟅ mapTrie f σ₁ , mapTrie f σ₂ ⟆ ]
   mapTrie f [ ↥ σ ] = [ ↥ (mapTrie (mapTrie f) σ) ]
   mapTrie f [ fun κ ] = [ fun (f κ) ]
   mapTrie f [ roll σ ] = [ roll (mapTrie f σ) ]

   {-# NO_TERMINATION_CHECK #-}
   mapMatch : ∀ {K K′ : VarCxt → Set} {Γ A} →
          (f : ∀ {Γ} → K Γ → K′ Γ) → (g : ∀ {Γ} → K Γ → K′ Γ) → Γ ⊢ A ⥬ K → Γ ⊢ A ⥬ K′
   mapMatch _ _ ε = ε
   mapMatch f g [ σ ] = [ mapTrie g σ ]
   mapMatch f g (any κ) = any (f κ)
   mapMatch f g (nat n κ) = nat n (f κ)
   mapMatch f g (〈〉 κ) = 〈〉 (f κ)
   mapMatch f g ⟅⟅ ξ , σ ⟆ = ⟅⟅ mapMatch f g ξ , mapTrie g σ ⟆
   mapMatch f g ⟅ σ , ξ ⟆⟆ = ⟅ mapTrie g σ , mapMatch f g ξ ⟆⟆
   mapMatch f g (↥ ξ) = ↥ (mapMatch (mapMatch f g) (mapMatch g g) ξ)
   mapMatch f g (fun v κ) = fun v (f κ)
   mapMatch f g (roll ξ) = roll (mapMatch f g ξ)

   match : ∀ {K : VarCxt → Type → Set} {Γ C A} → Value A → Γ ⊢ A ⇀ flip K C → Γ ⊢ A ⥬ flip K C
   match _ ε = ε
   match v (any κ) = any κ
   match {K} var σ = [ σ ] -- should be restricted to a variable trie at this point
   match (nat n) [ nat κ ] = nat n κ
   match 〈〉 [ 〈〉 κ ] = 〈〉 κ
   match {K} (inl u) [ ⟅ σ₁ , σ₂ ⟆ ] = ⟅⟅ match {K} u σ₁ , σ₂ ⟆
   match {K} (inr u) [ ⟅ σ₁ , σ₂ ⟆ ] = ⟅ σ₁ , match {K} u σ₂ ⟆⟆
   match {K} {C = C} 〈 u₁ , u₂ 〉 [ ↥ σ ] =
      ↥ (mapMatch (match {K} u₂) [_] (match {flip (Trie (flip K C))} u₁ σ))
   match (fun σ) [ fun κ ] = fun σ κ
   match {K} (roll u) [ roll σ ] = roll (match {K} u σ)

   -- "var" is essentially bottom, so use that to deal with the "dead" cases.
   {-# NO_TERMINATION_CHECK #-}
   proj : ∀ {K : VarCxt → Type → Set} {Γ C A} → Γ ⊢ A ⥬ flip K C → Value A × (Γ ⊢ A ⇀ flip K C)
   proj ε = var , ε
   proj [ σ ] = var , σ
   proj (any κ) = var , any κ
   proj (nat n κ) = nat n , [ nat κ ]
   proj (〈〉 κ) = 〈〉 , [ 〈〉 κ ]
   proj {K} ⟅⟅ ξ , σ ⟆ = let u , σ₁ = proj {K} ξ in inl u , [ ⟅ σ₁ , σ ⟆ ]
   proj {K} ⟅ σ , ξ ⟆⟆ = let u , σ₂ = proj {K} ξ in inr u , [ ⟅ σ , σ₂ ⟆ ]
   proj {K} {Γ} {C} (↥ ξ) =
     let u₁ , σ′ = proj {flip (MatchedTrie (flip K C))} ξ in
     let σ = mapTrie (π₂ ∘ proj {K}) σ′ in
     let blah = uncurry (lookup {flip (MatchedTrie (flip K C))}) (proj {flip (MatchedTrie (flip K C))} ξ) in
     〈 u₁ , {!!} 〉 , [ ↥ σ ]
   proj (fun v κ) = fun v , [ fun κ ]
   proj {K} (roll ξ) = let v , σ = proj {K} ξ in roll v , [ roll σ ]
