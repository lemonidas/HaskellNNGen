module Tokenizer (tokenize, tokenMap, revTokenMap) where

import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace

import Text.ParserCombinators.Parsec

allTokens =
  [ "seq"
  , "id"
  , "->"
  , "::"
  , "Int"
  , "Bool"
  , "[]"
  , "0"
  , "1"
  , "2"
  , "(+)"
  , "(+1)"
  , "(-)"
  , "(:)"
  , "(enumFromTo::Int -> Int -> [Int])"
  , "(enumFromTo\'::Int -> Int -> [Int])"
  , "head"
  , "tail"
  , "take"
  , "(!!)"
  , "filter"
  , "map"
  , "(++)"
  , "odd"
  , "even"
  , "(&&)"
  , "(||)"
  , "not"
  , "True"
  , "False"
  , "((==)::Int -> Int -> Bool)"
  , "((==)::Bool -> Bool -> Bool)"
  , "((==)::[Int] -> [Int] -> Bool)"
  , "case1"
  , "undefined"
  , "\\a" 
  , "\\b"
  , "\\c"
  , "\\d"
  , "\\e"
  , "\\f"
  , "\\g"
  , "a"
  , "b"
  , "c"
  , "d"
  , "e"
  , "f"
  , "g"
  , "("
  , ")"
  ]

look :: Map String Int -> String -> Int
look m x =
  case Map.lookup x m of
    Just a  -> a
    Nothing -> error ("Couldn't find" ++ (show x))

tokenMap :: Map String Int
tokenMap = Map.fromList $ zip allTokens [0..]

revTokenMap :: Map Int String
revTokenMap = Map.fromList $ zip [0..] allTokens

tokenParser :: CharParser st Int
tokenParser = choice $ map (\s -> try $ do
                               t <- string s
                               return $ tokenMap `look` t
                           ) allTokens

fileParser :: CharParser st [Int]
fileParser = do
  tokens <- manyTill (tokenParser <* spaces) eof
  return tokens

tokenize :: String -> [Int]
tokenize s = do
  let tokens = parse fileParser "(stdin)" s
  case tokens of
    Left e -> error $ show e
    Right s -> s


