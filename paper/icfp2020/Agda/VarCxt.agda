module VarCxt where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   -- Client code need not use the Type module directly.
   open import Cxt as ᶜ using (Cxt; _∈_); open ᶜ.Cxt
   open import Type as ᵀ public using (ClosedType; module Type)

   -- Redefine "type" to mean closed type over type-context membership, of kind ⋆.
   Type : Set
   Type = ClosedType (_∈_ ⋆)

   -- A variable context is a context over types.
   VarCxt : Set
   VarCxt = Cxt Type
