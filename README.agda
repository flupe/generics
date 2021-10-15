module README where

------------------------------------------------------------------------
-- Core definitions
------------------------------------------------------------------------

import Generics.Prelude

-- Generics.Telescope introduces an encoding for telescopes,
-- along with functions to manipulate indexed functions and families.
import Generics.Telescope

-- Generics.Desc introduces the core universe of descriptions for datatypes.
import Generics.Desc

-- Generics.HasDesc defines the HasDesc record,
-- bridging the gap between descriptions of datatypes
-- and their concrete Agda counterpart.
import Generics.HasDesc

-- Generics.Reflection implements the deriveDesc macro
-- to automatically derive an instance of HasDesc for most datatypes.
import Generics.Reflection

------------------------------------------------------------------------
-- Generic constructions
------------------------------------------------------------------------

-- Generic show implemetation
import Generics.Constructions.Show

-- Datatype-generic case analysis principle
import Generics.Constructions.Case

-- Datatype-generic decidable equality
import Generics.Constructions.DecEq

-- Datatype-generic induction principle,
-- on described datatypes only
import Generics.Constructions.Induction

-- Datatype-generic elimination principle
import Generics.Constructions.Elim

-- WIP Datatype-generic injectivity of constructors
import Generics.Constructions.NoConfusion
