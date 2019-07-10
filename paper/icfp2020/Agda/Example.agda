module Example where

   open import SharedModules

   open import Cxt as ᶜ using (∋); open ᶜ.Cxt; open ᶜ._∈_
   open import RawTerm as ᵉ using (Pattern; Body; Branch; RawTerm; module RawTerm); open ᵉ.Pattern; open ᵉ.RawTerm
   open import RawTerm.AsTerm using (trie; clause; no-overlapping; all-reachable)
   open import Trie as ᵀ using (Trie; _-[_]_); open ᵀ.Trie; open ᵀ.Trie⁻
   open import Term using (module Term) renaming (Term₀ to Term); open Term.Term
   open import VarCxt as ᵛᶜ using (Type); open ᵛᶜ.Type

   bool : Type
   bool = 𝟏 + 𝟏

   fᵉ : ∀ {Γ} → RawTerm Γ bool
   fᵉ = inl 〈〉

   tᵉ : ∀ {Γ} → RawTerm Γ bool
   tᵉ = inr 〈〉

   inductive-nat : Type
   inductive-nat = μ (𝟏 + var zero)

   z : Pattern inductive-nat
   z = roll (inl 〈〉)

   zᵉ : ∀ {Γ} → RawTerm Γ inductive-nat
   zᵉ = roll (inl 〈〉)

   s : Pattern inductive-nat → Pattern inductive-nat
   s n = roll (inr n)

   sᵉ : ∀ {Γ} → RawTerm Γ inductive-nat → RawTerm Γ inductive-nat
   sᵉ n = roll (inr n)

   list-pair-nat : Type
   list-pair-nat = μ (𝟏 + nat ⨰ nat ⨰ var zero)

   cons : Pattern (nat ⨰ nat) → Pattern list-pair-nat → Pattern list-pair-nat
   cons x xs = roll (inr 〈 x , xs 〉)

   consᵉ : ∀ {Γ} → RawTerm Γ (nat ⨰ nat) → RawTerm Γ list-pair-nat → RawTerm Γ list-pair-nat
   consᵉ x xs = roll (inr 〈 x , xs 〉)

   nil : Pattern list-pair-nat
   nil = roll (inl 〈〉)

   nilᵉ : ∀ {Γ} → RawTerm Γ list-pair-nat
   nilᵉ = roll (inl 〈〉)

   module Test₁ where
      -- match e as {
      --    nil → 0
      --    cons p (cons (y , z) nil) → y
      --    cons p (cons q (cons r rs)) →
      --       match q as {
      --          (y , z) → z
      --       }
      -- }
      example : List (Branch list-pair-nat ε nat)
      example =
         (nil ,
             nat 0) ∷
         (cons var (cons 〈 var , var 〉 nil) ,
             var (suc zero)) ∷
         (cons var (cons var (cons var var)) ,
             match var (suc zero) as (
                (〈 var , var 〉 , var zero) ∷
                []
             )) ∷
         []

      check : no-overlapping (trie example) ∧ not (all-reachable example) ≡ true
      check = refl

   module Test₂ where
      -- match e as {
      --    nil → 0
      --    cons p (cons (y , z) nil) → y
      --    cons p (cons (y , z) (cons r rs)) → z
      -- }
      example : List (Branch list-pair-nat ε nat)
      example =
         (nil ,
             nat 0) ∷
         (cons var (cons 〈 var , var 〉 nil) ,
             var (suc zero)) ∷
         (cons var (cons 〈 var , var 〉 (cons var var)) ,
             var (suc (suc zero))) ∷
         []

      check : no-overlapping (trie example) ∧ all-reachable example ≡ true
      check = refl

   module Test₃ where
      -- See paper for the human-readable version.
      parity : List (Branch (inductive-nat ⨰ inductive-nat) ε bool)
      parity =
         (〈 z , z 〉 , tᵉ ) ∷
         (〈 z , s z 〉 , fᵉ ) ∷
         (〈 z , s (s var) 〉 , {!!} ) ∷
         (〈 s z , z 〉 , fᵉ ) ∷
         (〈 s z , s var 〉 , {!!}) ∷
         (〈 s (s var) , var 〉 , {!!} ) ∷
         []

      check : no-overlapping (trie parity) ∧ all-reachable parity ≡ true
      check = refl

   module Test₄ where
      max : List (Branch (inductive-nat ⨰ inductive-nat) ε inductive-nat)
      max =
         (〈 z , var 〉 , var zero) ∷
         (〈 s var , z 〉 , sᵉ (var zero)) ∷
         (〈 s var , s var 〉 , sᵉ {!!}) ∷
         []

      -- TODO: demonstrate that all-reachable is broken, then fix it.
      check : no-overlapping (trie max) ∧ all-reachable max ≡ true
      check = refl

   module Test₅ where
      append : Trie Body list-pair-nat ε (list-pair-nat ⇾ list-pair-nat)
      append = trie (
            (nil ,
                fun ((var , var zero) ∷ [])) ∷
            (cons var var ,
                fun ((var , consᵉ (var (suc (suc zero))) (app (app {!!} (var (suc zero))) (var zero))) ∷ [])) ∷
            []
         )

      reverse : Trie Body list-pair-nat ε list-pair-nat
      reverse = trie (
            (nil , nilᵉ) ∷
            (cons var nil , consᵉ (var zero) nilᵉ) ∷
            (cons var (cons var var) , {!!} ) ∷
            []
         )
