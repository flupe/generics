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

import Generics.All

-- Generics.Accessibility introduces the accessibility predicate for datatypes.
import Generics.Accessibility

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

-- Datatype-generic fold
import Generics.Constructions.Fold

-- Datatype-generic recursion
import Generics.Constructions.Recursion

-- Datatype-generic decidable equality
import Generics.Constructions.DecEq

-- Datatype-generic elimination principle
import Generics.Constructions.Elim

-- No Confusion principle
import Generics.Constructions.NoConfusion

-- Conversion to μ types
import Generics.Constructions.Mu

------------------------------------------------------------------------
-- Generic constructions on μ types
------------------------------------------------------------------------

import Generics.Mu
import Generics.Mu.All
import Generics.Mu.Elim
import Generics.Mu.Fold
