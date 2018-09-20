
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeFamilies          #-}

module Main where

import           Grenade

import DumpGHCTerms
import Shakespeare
import Tokenizer


main :: IO ()
main = do
--  tokens <- tokenize
--  print tokens
  shakespeare_main 
--  let termsAtOnce = 10000
--  dumpGHCMany termsAtOnce 70 4 (map snd preludeTypes) (map fst preludeTypes) "TestModule.hs"

