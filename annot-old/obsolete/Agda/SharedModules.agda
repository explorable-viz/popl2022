module SharedModules where

   open import Algebra public
   open import Algebra.FunctionProperties public
   open import Algebra.Structures public
   open import Data.Bool hiding (decSetoid; _≟_) public
   open import Data.Empty public
   open import Data.Maybe public hiding (decSetoid; setoid; Eq; module Eq) public
   open import Data.List using (List; _++_;_∷ʳ_; length) public; open Data.List.List public
   open import Data.Nat using (ℕ) public; import Data.Nat.Properties
   open import Data.Product public hiding (map; zip; _-×-_) renaming (proj₁ to π₁; proj₂ to π₂)
   open import Data.Unit public hiding (decSetoid; setoid; preorder; _≟_) renaming (tt to ⋆)
   open import Function public hiding (_∋_)
   open import Relation.Binary public
   open import Relation.Binary.PropositionalEquality hiding ([_]) public
   open import Relation.Nullary public
   open import Size public
