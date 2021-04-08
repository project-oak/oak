-- Enable some necessary extensions:
{-# LANGUAGE ScopedTypeVariables, DataKinds, TypeFamilies, DeriveGeneric #-}

module Main ( main ) where

import Data.Foldable ( traverse_ )
import Control.Monad.IO.Class
import GHC.Generics
import Data.Vector
import qualified Language.Souffle.Compiled as Souffle


-- We define a data type representing our datalog program.
data Path = Path

-- Facts are represented in Haskell as simple product types,
-- Numbers map to Int32, unsigned to Word32, floats to Float,
-- symbols to Strings / Text.

data Edge = Edge String String
  deriving (Eq, Show, Generic)

data Reachable = Reachable String String
  deriving (Eq, Show, Generic)

-- By making Path an instance of Program, we provide Haskell with information
-- about the datalog program. It uses this to perform compile-time checks to
-- limit the amount of possible programmer errors to a minimum.
instance Souffle.Program Path where
  type ProgramFacts Path = [Edge, Reachable]
  programName = const "path"

-- By making a data type an instance of Fact, we give Haskell the
-- necessary information to bind to the datalog fact.
instance Souffle.Fact Edge where
  type FactDirection Edge = 'Souffle.Input
  factName = const "edge"

instance Souffle.Fact Reachable where
  type FactDirection Reachable = 'Souffle.Output
  factName = const "reachable"

-- For simple product types, we can automatically generate the
-- marshalling/unmarshalling code of data between Haskell and datalog.
instance Souffle.Marshal Edge
instance Souffle.Marshal Reachable


main :: IO ()
main = Souffle.runSouffle Path $ \maybeProgram -> do  -- Initializes the Souffle program.
  case maybeProgram of
    Nothing -> liftIO $ putStrLn "Failed to load program."
    Just prog -> do
      Souffle.addFact prog $ Edge "d" "i"   -- Adding a single fact from Haskell side
      Souffle.addFacts prog [ Edge "e" "f"  -- Adding multiple facts
                            , Edge "f" "g"
                            , Edge "f" "g"
                            , Edge "f" "h"
                            , Edge "g" "i"
                            ]

      Souffle.run prog  -- Run the Souffle program

      -- NOTE: You can change type param to fetch different relations
      --       Here it requires an annotation since we directly print it
      --       to stdout, but if passed to another function, it can infer
      --       the correct type automatically.
      --       A list of facts can also be returned here.
      results :: Vector Reachable <- Souffle.getFacts prog
      liftIO $ traverse_ print results

      -- We can also look for a specific fact:
      maybeFact <- Souffle.findFact prog $ Reachable "a" "c"
      liftIO $ print $ maybeFact

