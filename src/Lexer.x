{
module Lexer (doLex, tokenMap) where

import Data.Map (Map)
import qualified Data.Map as Map
import Debug.Trace

}

%wrapper "basic"

$digit = 0-9			-- digits
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-

  "seq" { \s -> tokenMap `look` s }
  "id"  { \s -> look tokenMap s }
  "[]"  { \s -> tokenMap `look` s }
  "0"   { \s -> tokenMap `look` s }
  "1"   { \s -> tokenMap `look` s }
  "2"   { \s -> tokenMap `look` s }
  "(+)" { \s -> tokenMap `look` s }
  "(+1)"  { \s -> tokenMap `look` s }
  "(-)"   { \s -> tokenMap `look` s }
  "(:)"   { \s -> tokenMap `look` s }
  "(enumFromTo::Int -> Int -> [Int])"  { \s -> tokenMap `look` s }
  "(enumFromTo\'::Int -> Int -> [Int])"
  "head"              { \s -> tokenMap `look` s }
  "tail"              { \s -> tokenMap `look` s }
  "take"              { \s -> tokenMap `look` s }
  "(!!)"              { \s -> tokenMap `look` s }
  "filter"            { \s -> tokenMap `look` s }
  "map"               { \s -> tokenMap `look` s }
  "(++)"              { \s -> tokenMap `look` s }
  "odd"               { \s -> tokenMap `look` s }
  "even"              { \s -> tokenMap `look` s }
  "(&&)"              { \s -> tokenMap `look` s }
  "(||)"              { \s -> tokenMap `look` s }
  "not"               { \s -> tokenMap `look` s }
  "True"              { \s -> tokenMap `look` s }
  "False"             { \s -> tokenMap `look` s }
  "((==)::Int -> Int -> Bool)"              { \s -> tokenMap `look` s }
  "((==)::Bool -> Bool -> Bool)"            { \s -> tokenMap `look` s }
  "((==)::[Int] -> [Int] -> Bool)"          { \s -> tokenMap `look` s }
  "case1"       { \s -> tokenMap `look` s }
  "undefined"   { \s -> tokenMap `look` s }
  "\\a" { \s -> tokenMap `look` s }
  "\\b" { \s -> tokenMap `look` s }
  "\\c" { \s -> tokenMap `look` s }
  "\\d" { \s -> tokenMap `look` s }
  "\\e" { \s -> tokenMap `look` s }
  "\\f" { \s -> tokenMap `look` s }
  "\\g" { \s -> tokenMap `look` s }
  "("  { \s -> tokenMap `look` s }
  ")"  { \s -> tokenMap `look` s }
  $white+				;

{

allTokens =
  [ "seq"
  , "id"
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
  , "\a" 
  , "\\b"
  , "\\c"
  , "\\d"
  , "\\e"
  , "\\f"
  , "\\g"
  , "("
  , ")"
  ]

look :: Map String Int -> String -> Int
look m x =
  case Map.lookup x m of
    Just a  -> a
    Nothing -> error ("Couldn't find" ++ (show x))

tokenMap = Map.fromList $ zip allTokens [0..]

alexScanTokens' str = go ('\n',[],str)
  where go inp__@(_,_bs,s) =
          case alexScan inp__ 0 of
                AlexEOF -> []
                AlexError (c,bs,r) -> error $ show (c, bs,take 10 r)
                AlexSkip  inp__' _ln     -> go inp__'
                AlexToken inp__' len act ->
                   traceShow ("parsing", take len s) $ act (take len s) : go inp__'

doLex = do
  s <- getContents
  let tokens = alexScanTokens' s
  print tokens
  return tokens
}
