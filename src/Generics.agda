{-# OPTIONS --safe #-}
module Generics where

open import Data.Unit                    public using (⊤; tt)
open import Generics.Prelude             public using (liftω; liftω-inst)
open import Generics.HasDesc             public using (HasDesc)
open import Generics.Reflection          public using (deriveDesc)
open import Generics.Helpers             public

open import Generics.Constructions.Case       public using (deriveCase)
open import Generics.Constructions.Cong       public using (deriveCong)
open import Generics.Constructions.DecEq      public using (DecEq; _≟_; deriveDecEq)
open import Generics.Constructions.Elim       public using (deriveElim)
open import Generics.Constructions.Fold       public using (deriveFold)
open import Generics.Constructions.Recursion  public using (rec; Below)
open import Generics.Constructions.Show       public using (Show; show; deriveShow)
