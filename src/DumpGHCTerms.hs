module DumpGHCTerms where

import Debug.Trace

import Data.Maybe
import Test.QuickCheck

import System.IO
import Text.Show

import PalkaGenerator

dumpGHCMany listL n ng env l fn = do
  let t = listType (TVar "Int") --> listType (TVar "Int")
  let env' = map (fmap Name) env 
  -- Generate many [Int] -> [Int] functions
  functions <- catMaybes <$> generate (vectorOf (listL + 5) (runMaybeT $ arbExp True n ng env' (fmap Name t)))
  let output = concat $ map (\t -> unparse l t ++ "\n") functions
--        toModuleMany "======" $ showListWith (\t s -> "\n  " ++ unparse l t ++ s) functions "" 
  withFile fn WriteMode $ \h -> hPutStrLn h output


preludeTypes =
  [ (("seq",   False), TYPE (POLY 2 $ \[a, b] -> TVar (Bound a) --> TVar (Bound b) --> TVar (Bound b)))
  , (("id",    False), TYPE (POLY 1 $ \[a] -> TVar (Bound a) --> TVar (Bound a)))
  --, (("(.)",   False), TYPE (POLY 3 $ \[a, b, c] ->
  --    (TVar (Bound b) --> TVar (Bound c)) --> (TVar (Bound a) --> TVar (Bound b)) -->
  --    TVar (Bound a) --> TVar (Bound c)))
  , (("[]",    True),  TYPE (POLY 1 $ \[a] -> listType $ TVar (Bound a)))
  , (("0",     False), monoType $ TVar "Int")
  , (("1",     False), monoType $ TVar "Int")
  , (("2",     False), monoType $ TVar "Int")
  , (("(+)",   False), monoType $ TVar "Int" --> TVar "Int" --> TVar "Int")
  , (("(+1)",  False), monoType $ TVar "Int" --> TVar "Int")
  , (("(-)",   False), monoType $ TVar "Int" --> TVar "Int" --> TVar "Int")
  , (("(:)",   False), TYPE (POLY 1 $ \[a] -> TVar (Bound a) --> listType (TVar (Bound a)) --> listType (TVar (Bound a))))
  , (("(enumFromTo::Int -> Int -> [Int])",
               False), monoType $ TVar "Int" --> TVar "Int" --> listType (TVar "Int"))
  , (("(enumFromTo\'::Int -> Int -> [Int])",
               False), monoType $ TVar "Int" --> TVar "Int" --> listType (TVar "Int"))
  , (("head",  False), TYPE (POLY 1 $ \[a] -> listType (TVar (Bound a)) --> TVar (Bound a)))
  , (("tail",  False), TYPE (POLY 1 $ \[a] -> listType (TVar (Bound a)) --> listType (TVar (Bound a))))
--  , (("replicate",
--               False), TYPE (POLY 1 $ \[a] -> TVar (Free "Int") --> TVar (Bound a) --> listType (TVar (Bound a))))
  , (("take",  False), TYPE (POLY 1 $ \[a] ->
      TVar (Free "Int") --> listType (TVar (Bound a)) --> listType (TVar (Bound a))))
  , (("(!!)",  False), TYPE (POLY 1 $ \[a] -> listType (TVar (Bound a)) --> TVar (Free "Int") --> TVar (Bound a)))
--  , (("length",
--               False), TYPE (POLY 1 $ \[a] -> listType (TVar (Bound a)) --> TVar (Free "Int")))
--  , (("reverse",
--               False), TYPE (POLY 1 $ \[a] -> listType (TVar (Bound a)) --> listType (TVar (Bound a))))
--  , (("concat",
--               False), TYPE (POLY 1 $ \[a] -> listType (listType (TVar (Bound a))) --> listType (TVar (Bound a))))
  , (("filter",
               False), TYPE (POLY 1 $ \[a] ->
      (TVar (Bound a) --> TVar (Free "Bool")) --> listType (TVar (Bound a)) --> listType (TVar (Bound a))))
  , (("map",   False), TYPE (POLY 2 $ \[a, b] ->
      (TVar (Bound a) --> TVar (Bound b)) --> listType (TVar (Bound a)) --> listType (TVar (Bound b))))
--  , (("null",  False), TYPE (POLY 1 $ \[a] -> listType (TVar (Bound a)) --> TVar (Free "Bool")))
  , (("(++)",  False), TYPE (POLY 1 $ \[a] -> listType (TVar (Bound a)) --> listType (TVar (Bound a)) --> listType (TVar (Bound a))))
  , (("odd",   False), monoType $ TVar "Int" --> TVar "Bool")
  , (("even",  False), monoType $ TVar "Int" --> TVar "Bool")
  , (("(&&)",  False), monoType $ TVar "Bool" --> TVar "Bool" --> TVar "Bool")
  , (("(||)",  False), monoType $ TVar "Bool" --> TVar "Bool" --> TVar "Bool")
  , (("not",   False), monoType $ TVar "Bool" --> TVar "Bool")
  , (("True",  False), monoType $ TVar "Bool")
  , (("False",  False), monoType $ TVar "Bool")
--  , (("foldr", False), TYPE (POLY 2 $ \[a, b] ->
--      (TVar (Bound a) --> TVar (Bound b) --> TVar (Bound b)) --> TVar (Bound b) -->
--        listType (TVar (Bound a)) --> TVar (Bound b)))
  --, (("(==)", False), TYPE (POLY 1 $ \[a] -> TVar (Bound a) --> TVar (Bound a) --> TVar (Free "Bool")))
  , (("((==)::Int -> Int -> Bool)",
               False), monoType $ TVar "Int" --> TVar "Int" --> TVar "Bool")
  , (("((==)::Bool -> Bool -> Bool)",
               False), monoType $ TVar "Bool" --> TVar "Bool" --> TVar "Bool")
  , (("((==)::[Int] -> [Int] -> Bool)",
               False), monoType $ listType (TVar "Int") --> listType (TVar "Int") --> TVar "Bool")
  , (("case1",
               False), TYPE (POLY 2 $ \[a, b] ->
      (TVar (Bound a) --> listType (TVar (Bound a)) --> TVar (Bound b)) --> TVar (Bound b) -->
        listType (TVar (Bound a)) --> TVar (Bound b)))
  , (("undefined",  True), undefinedType)
  ]

  -- prop_shrink1 =
--   forAll (runMaybeT $ arbExp True 10 2 (map (fmap Name) $ (map snd preludeTypes)) (fmap Name t)) $ \x ->
--     case x of Nothing -> property (); Just tt -> property $ all (criterion tt) $ shrinkCTerm2 [] tt
--   where
--   t = listType (TVar "Int") --> listType (TVar "Int")
--   criterion tt x = case isJust $ termWF x of
--     True -> True
--     False -> trace ("failed on this: " ++
--         unparse' (map fst preludeTypes) x ++
--           "\n\n" ++ show x ++ "\noriginal:\n" ++
--         unparse' (map fst preludeTypes) tt ++
--           "\n\n" ++ show tt ++ "\n\noriginal" ++ show (isJust $ termWF tt) ++ "\n") False
--  
-- prop_wf =
--   forAll (runMaybeT $ arbExp True 25 2 (map (fmap Name) $ (map snd preludeTypes)) (fmap Name t)) $ \x ->
--     case x of Nothing -> property (); Just t -> property $ criterion t
--   where
--   t = listType (TVar "Int") --> listType (TVar "Int")
--   criterion x = case isJust $ termWF x of
--     True -> True
--     False -> trace ("failed on this: " ++ unparse' (map fst preludeTypes) x ++ "\n\n" ++ show x ++ "\n\n") False

