module Parity where

   open import Data.Bool
   open import Data.Nat

   parity : ℕ → ℕ → Bool
   parity zero zero = true
   parity zero (suc zero) = false
   parity zero (suc (suc n)) = parity zero n
   parity (suc zero) zero = false
   parity (suc (suc n)) zero = parity n zero
   parity (suc n) (suc m) = parity n m

   parity′ : ℕ → ℕ → Bool
   parity′ zero zero = true
   parity′ zero (suc zero) = false
   parity′ zero (suc (suc n)) = parity′ zero n
   parity′ (suc zero) zero = false
   parity′ (suc zero) (suc n) = parity′ zero n
   parity′ (suc (suc n)) m = parity′ n m
