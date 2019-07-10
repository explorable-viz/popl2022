module RawTerm.Eq where

   open import SharedModules
   import Common.Data.List.Eq
   import Common.Data.Product.Eq
   open import Common.Eq using (Eq; module Eq); open Eq ⦃...⦄ renaming (_≟_ to _≟′_)

   open import RawTerm using (Pattern; RawTerm); open RawTerm
   open import Cxt as ᶜ using () renaming (∋ to _∋_); open ᶜ.Substitutable ⦃...⦄ hiding (var)
   import Cxt.Eq
   import Type using (module Type); open Type.Type
   import Type.Eq

   instance
      eqᴾ : ∀ {A} → Eq (Pattern A)
      eqᴾ = record { _≟_ = _≟_ }
         where
         inl-injective : ∀ {A B p p′} → _≡_ {A = Pattern (A + B)} (inl p) (inl p′) → p ≡ p′
         inl-injective refl = refl

         inr-injective : ∀ {A B p p′} → _≡_ {A = Pattern (A + B)} (inr p) (inr p′) → p ≡ p′
         inr-injective refl = refl

         〈_,_〉-injective : ∀ {A B p₁ p₂ p₁′ p₂′} → _≡_ {A = Pattern (A ⨰ B)} 〈 p₁ , p₂ 〉 〈 p₁′ , p₂′ 〉 → p₁ ≡ p₁′ × p₂ ≡ p₂′
         〈_,_〉-injective refl = refl , refl

         roll-injective : ∀ {A p p′} → _≡_ {A = Pattern (μ A)} (roll p) (roll p′) → p ≡ p′
         roll-injective refl = refl

         _≟_ : ∀ {A} → Decidable {A = Pattern A} _≡_
         var ≟ var = yes refl
         var ≟ 〈〉 = no (λ ())
         var ≟ inl _ = no (λ ())
         var ≟ inr _ = no (λ ())
         var ≟ 〈 _ , _ 〉 = no (λ ())
         var ≟ roll _ = no (λ ())
         〈〉 ≟ var = no (λ ())
         〈〉 ≟ 〈〉 = yes refl
         inl p ≟ inl p′ with p ≟ p′
         inl p ≟ inl .p | yes refl = yes refl
         ... | no p≢p′ = no (p≢p′ ∘ inl-injective)
         inl _ ≟ var = no (λ ())
         inl _ ≟ inr _ = no (λ ())
         inr p ≟ inr p′ with p ≟ p′
         inr p ≟ inr .p | yes refl = yes refl
         ... | no p≢p′ = no (p≢p′ ∘ inr-injective)
         inr _ ≟ var = no (λ ())
         inr _ ≟ inl _ = no (λ ())
         〈 _ , _ 〉 ≟ var = no (λ ())
         〈 p₁ , p₂ 〉 ≟ 〈 p₁′ , p₂′ 〉 with p₁ ≟ p₁′ | p₂ ≟ p₂′
         〈 p₁ , p₂ 〉 ≟ 〈 .p₁ , .p₂ 〉 | yes refl | yes refl = yes refl
         ... | yes _ | no p₂≢p₂′ = no (p₂≢p₂′ ∘ π₂ ∘ 〈_,_〉-injective)
         ... | no p₁≢p₁′ | yes _ = no (p₁≢p₁′ ∘ π₁ ∘ 〈_,_〉-injective)
         ... | no p₁≢p₁′ | no _ = no (p₁≢p₁′ ∘ π₁ ∘ 〈_,_〉-injective)
         roll p ≟ roll p′ with p ≟ p′
         roll p ≟ roll .p | yes refl = yes refl
         ... | no p≢p′ = no (p≢p′ ∘ roll-injective)
         roll _ ≟ var = no (λ ())

      {-# NO_TERMINATION_CHECK #-}
      eq : ∀ {Γ A} → Eq (RawTerm Γ A)
      eq = record { _≟_ = _≟_ }
         where
         -- Boilerplate to establish the injectivity of each constructor.
         var-injective : ∀ {Γ A a a′} → _≡_ {A = RawTerm Γ A} (var a) (var a′) → a ≡ a′
         var-injective refl = refl

         nat-injective : ∀ {Γ n m} → _≡_ {A = RawTerm Γ nat} (nat n) (nat m) → n ≡ m
         nat-injective refl = refl

         inl-injective : ∀ {Γ A B e e′} → _≡_ {A = RawTerm Γ (A + B)} (inl e) (inl e′) → e ≡ e′
         inl-injective refl = refl

         inr-injective : ∀ {Γ A B e e′} → _≡_ {A = RawTerm Γ (A + B)} (inr e) (inr e′) → e ≡ e′
         inr-injective refl = refl

         match-as-injective : ∀ {Γ A B e e′} {b∗ b∗′ : List (Branch A Γ B)} →
                              match e as b∗ ≡ match e′ as b∗′ → e ≡ e′ × b∗ ≡ b∗′
         match-as-injective refl = refl , refl

         〈_,_〉-injective : ∀ {Γ A B e₁ e₂ e₁′ e₂′} →
                           _≡_ {A = RawTerm Γ (A ⨰ B)} 〈 e₁ , e₂ 〉 〈 e₁′ , e₂′ 〉 → e₁ ≡ e₁′ × e₂ ≡ e₂′
         〈_,_〉-injective refl = refl , refl

         fst-injective : ∀ {Γ A B} {e e′ : RawTerm Γ (A ⨰ B)} → fst e ≡ fst e′ → e ≡ e′
         fst-injective refl = refl

         snd-injective : ∀ {Γ A B} {e e′ : RawTerm Γ (A ⨰ B)} → snd e ≡ snd e′ → e ≡ e′
         snd-injective refl = refl

         fun-injective : ∀ {Γ A B e e′} → _≡_ {A = RawTerm Γ (A ⇾ B)} (fun e) (fun e′) → e ≡ e′
         fun-injective refl = refl

         app-injective : ∀ {Γ A B} {e₁ e₁′ : RawTerm Γ (A ⇾ B)} {e₂ e₂′} →
                         app e₁ e₂ ≡ app e₁′ e₂′ → e₁ ≡ e₁′ × e₂ ≡ e₂′
         app-injective refl = refl , refl

         roll-injective : ∀ {Γ A e e′} → _≡_ {A = RawTerm Γ (μ A)} (roll e) (roll e′) → e ≡ e′
         roll-injective refl = refl

         -- Lots of boilerplate to eliminate impossible cases.
         _≟_ : ∀ {Γ A} → Decidable {A = RawTerm Γ A} _≡_
         (var a) ≟ (var a′) with a ≟′ a′
         (var _) ≟ (var ._) | yes refl = yes refl
         ... | no a≢a′ = no (a≢a′ ∘ var-injective)
         var _ ≟ nat _ = no (λ ())
         var _ ≟ 〈〉 = no (λ ())
         var _ ≟ inl _ = no (λ ())
         var _ ≟ inr _ = no (λ ())
         var _ ≟ match _ as _ = no (λ ())
         var _ ≟ 〈 _ , _ 〉 = no (λ ())
         var _ ≟ fst _ = no (λ ())
         var _ ≟ snd _ = no (λ ())
         var _ ≟ fun _ = no (λ ())
         var _ ≟ app _ _ = no (λ ())
         var _ ≟ roll _ = no (λ ())
         nat n ≟ nat m with n ≟′ m
         nat _ ≟ nat ._ | yes refl = yes refl
         ... | no n≢m = no (n≢m ∘ nat-injective)
         nat _ ≟ var _ = no (λ ())
         nat _ ≟ fst _ = no (λ ())
         nat _ ≟ snd _ = no (λ ())
         nat _ ≟ match _ as _ = no (λ ())
         nat _ ≟ app _ _ = no (λ ())
         〈〉 ≟ 〈〉 = yes refl
         〈〉 ≟ var _ = no (λ ())
         〈〉 ≟ fst _ = no (λ ())
         〈〉 ≟ snd _ = no (λ ())
         〈〉 ≟ (match _ as _) = no (λ ())
         〈〉 ≟ app _ _ = no (λ ())
         inl e ≟ inl e′ with e ≟ e′
         inl _ ≟ inl ._ | yes refl = yes refl
         ... | no e≢e′ = no (e≢e′ ∘ inl-injective)
         inl _ ≟ var _ = no (λ ())
         inl _ ≟ inr _ = no (λ ())
         inl _ ≟ match _ as _ = no (λ ())
         inl _ ≟ fst _ = no (λ ())
         inl _ ≟ snd _ = no (λ ())
         inl _ ≟ app _ _ = no (λ ())
         inr e ≟ inr e′ with e ≟ e′
         inr _ ≟ inr ._ | yes refl = yes refl
         ... | no e≢e′ = no (e≢e′ ∘ inr-injective)
         inr _ ≟ var _ = no (λ ())
         inr _ ≟ inl _ = no (λ ())
         inr _ ≟ match _ as _ = no (λ ())
         inr _ ≟ fst _ = no (λ ())
         inr _ ≟ snd _ = no (λ ())
         inr _ ≟ app _ _ = no (λ ())
         match_as_ {A = A} _ _ ≟ match_as_ {A = A′} _ _ with A ≟′ A′
         match e as b∗ ≟ match_as_ {A = ._} e′ b∗′ | yes refl with e ≟ e′ | b∗ ≟′ b∗′
         match e as b∗ ≟ match .e as .b∗ | yes refl | yes refl | yes refl = yes refl
         ... | no e≢e′ | yes _ = no (e≢e′ ∘ π₁ ∘ match-as-injective)
         ... | yes _ | no b∗≢b∗′ = no (b∗≢b∗′ ∘ π₂ ∘ match-as-injective)
         ... | no e≢e′ | no _ = no (e≢e′ ∘ π₁ ∘ match-as-injective)
         match _ as _ ≟ match _ as _ | no A≢A′ = no (A≢A′ ∘ type-injective) where
            type-injective : ∀ {Γ A A′} {e : RawTerm Γ A} {e′ : RawTerm Γ A′} {b∗ b∗′} →
                             match e as b∗ ≡ match e′ as b∗′ → A ≡ A′
            type-injective refl = refl
         match _ as _ ≟ var _ = no (λ ())
         match _ as _ ≟ nat _ = no (λ ())
         match _ as _ ≟ 〈〉 = no (λ ())
         match _ as _ ≟ inl _ = no (λ ())
         match _ as _ ≟ inr _ = no (λ ())
         match _ as _ ≟ 〈 _ , _ 〉 = no (λ ())
         match _ as _ ≟ fst _ = no (λ ())
         match _ as _ ≟ snd _ = no (λ ())
         match _ as _ ≟ fun _ = no (λ ())
         match _ as _ ≟ app _ _ = no (λ ())
         match _ as _ ≟ roll _ = no (λ ())
         〈 e₁ , e₂ 〉 ≟ 〈 e₁′ , e₂′ 〉 with e₁ ≟ e₁′ | e₂ ≟ e₂′
         〈 _ , _ 〉 ≟ 〈 ._ , ._ 〉 | yes refl | yes refl = yes refl
         ... | yes _ | no e₂≢e₂′ = no (e₂≢e₂′ ∘ π₂ ∘ 〈_,_〉-injective)
         ... | no e₁≢e₁′ | yes _ = no (e₁≢e₁′ ∘ π₁ ∘ 〈_,_〉-injective)
         ... | no e₁≢e₁′ | no _ = no (e₁≢e₁′ ∘ π₁ ∘ 〈_,_〉-injective)
         〈 _ , _ 〉 ≟ var _ = no (λ ())
         〈 _ , _ 〉 ≟ match _ as _ = no (λ ())
         〈 _ , _ 〉 ≟ fst _ = no (λ ())
         〈 _ , _ 〉 ≟ snd _ = no (λ ())
         〈 _ , _ 〉 ≟ app _ _ = no (λ ())
         fst _ ≟ var _ = no (λ ())
         fst _ ≟ nat _ = no (λ ())
         fst _ ≟ 〈〉 = no (λ ())
         fst _ ≟ inl _ = no (λ ())
         fst _ ≟ inr _ = no (λ ())
         fst _ ≟ (match _ as _) = no (λ ())
         fst _ ≟ 〈 _ , _ 〉 = no (λ ())
         fst _ ≟ snd _ = no (λ ())
         fst _ ≟ fun _ = no (λ ())
         fst _ ≟ app _ _ = no (λ ())
         fst _ ≟ roll _ = no (λ ())
         fst {B = B} _ ≟ fst {B = B′} _ with B ≟′ B′
         fst e ≟ fst {B = ._} e′ | yes refl with e ≟ e′
         fst _ ≟ fst ._ | yes refl | yes refl = yes refl
         ... | no e≢e′ = no (e≢e′ ∘ fst-injective)
         fst _ ≟ fst _ | no B≢B′ = no (B≢B′ ∘ type-injective) where
            type-injective : ∀ {Γ A B B′} {e : RawTerm Γ (A ⨰ B)} {e′ : RawTerm Γ (A ⨰ B′)} → fst e ≡ fst e′ → B ≡ B′
            type-injective refl = refl
         snd _ ≟ var _ = no (λ ())
         snd _ ≟ nat _ = no (λ ())
         snd _ ≟ 〈〉 = no (λ ())
         snd _ ≟ inl _ = no (λ ())
         snd _ ≟ inr _ = no (λ ())
         snd _ ≟ (match _ as _) = no (λ ())
         snd _ ≟ 〈 _ , _ 〉 = no (λ ())
         snd _ ≟ fst _ = no (λ ())
         snd _ ≟ fun _ = no (λ ())
         snd _ ≟ app _ _ = no (λ ())
         snd _ ≟ roll _ = no (λ ())
         snd {A = A} _ ≟ snd {A = A′} _ with A ≟′ A′
         snd e ≟ snd {A = ._} e′ | yes refl with e ≟ e′
         snd _ ≟ snd ._ | yes refl | yes refl = yes refl
         ... | no e≢e′ = no (e≢e′ ∘ snd-injective)
         snd _ ≟ snd _ | no B≢B′ = no (B≢B′ ∘ type-injective) where
            type-injective : ∀ {Γ A A′ B} {e : RawTerm Γ (A ⨰ B)} {e′ : RawTerm Γ (A′ ⨰ B)} → snd e ≡ snd e′ → A ≡ A′
            type-injective refl = refl
         fun b∗ ≟ fun b∗′ with b∗ ≟′ b∗′
         fun _ ≟ fun ._ | yes refl = yes refl
         ... | no e≢e′ = no (e≢e′ ∘ fun-injective)
         fun _ ≟ var x = no (λ ())
         fun _ ≟ match _ as _ = no (λ ())
         fun _ ≟ fst _ = no (λ ())
         fun _ ≟ snd _ = no (λ ())
         fun _ ≟ app _ _ = no (λ ())
         app _ _ ≟ var _ = no (λ ())
         app _ _ ≟ nat _ = no (λ ())
         app _ _ ≟ 〈〉 = no (λ ())
         app _ _ ≟ inl _ = no (λ ())
         app _ _ ≟ inr _ = no (λ ())
         app _ _ ≟ match _ as _ = no (λ ())
         app _ _ ≟ 〈 _ , _ 〉 = no (λ ())
         app _ _ ≟ fst _ = no (λ ())
         app _ _ ≟ snd _ = no (λ ())
         app _ _ ≟ fun _ = no (λ ())
         app _ _ ≟ roll _ = no (λ ())
         app {A = A} _ _ ≟ app {A = A′} _ _ with A ≟′ A′
         app e₁ e₂ ≟ app {A = ._} e₁′ e₂′ | yes refl with e₁ ≟ e₁′ | e₂ ≟ e₂′
         app _ _ ≟ app ._ ._ | yes refl | yes refl | yes refl = yes refl
         ... | yes _ | no e₂≢e₂′ = no (e₂≢e₂′ ∘ π₂ ∘ app-injective)
         ... | no e₁≢e₁′ | yes _ = no (e₁≢e₁′ ∘ π₁ ∘ app-injective)
         ... | no e₁≢e₁′ | no _ = no (e₁≢e₁′ ∘ π₁ ∘ app-injective)
         app _ _ ≟ app _ _ | no A≢A′ = no (A≢A′ ∘ type-injective) where
            type-injective : ∀ {Γ A A′ B} {e₁ : RawTerm Γ (A ⇾ B)} {e₁′ : RawTerm Γ (A′ ⇾ B)} {e₂ e₂′} →
                             app e₁ e₂ ≡ app e₁′ e₂′ → A ≡ A′
            type-injective refl = refl
         roll e ≟ roll e′ with e ≟ e′
         roll _ ≟ roll ._ | yes refl = yes refl
         ... | no e≢e′ = no (e≢e′ ∘ roll-injective)
         roll _ ≟ var _ = no (λ ())
         roll _ ≟ match _ as _ = no (λ ())
         roll _ ≟ fst _ = no (λ ())
         roll _ ≟ snd _ = no (λ ())
         roll _ ≟ app _ _ = no (λ ())
