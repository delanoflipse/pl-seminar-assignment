-- Hello World in Agda, just to get started
module HelloWorld where

data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

main : IO ⊤
main = putStrLn "Hello world!"
