{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE LambdaCase            #-}
module Shakespeare where

import           Control.Monad.Random
import           Control.Monad.Trans.Except

import           Data.Char ( isUpper, toUpper, toLower )
import           Data.List ( foldl' )
import           Data.Maybe ( fromMaybe )
import           Data.Semigroup ( (<>) )

import qualified Data.Vector as V
import           Data.Vector ( Vector )

import qualified Data.Map as M
import           Data.Proxy ( Proxy (..) )

import qualified Data.ByteString as B
import           Data.Serialize

import           Data.Singletons.Prelude
import           GHC.TypeLits

import           Numeric.LinearAlgebra.Static ( konst )

import           Options.Applicative

import           Grenade
import           Grenade.Recurrent
import           Grenade.Utils.OneHot

import           System.IO.Unsafe ( unsafeInterleaveIO )

import Tokenizer

-- Based on the Shakespeare neural net example of Grenade.
-- This is a first class recurrent net.
--
-- The F and R types are tagging types to ensure that the runner and
-- creation function know how to treat the layers.

type F = FeedForward
type R = Recurrent

-- The definition of our network
type Shakespeare =
  RecurrentNetwork
    '[ R (LSTM 50 100), R (LSTM 100 50), F (FullyConnected 50 50), F Logit ]
    '[ 'D1 50        , 'D1 100        , 'D1 50                  , 'D1 50  , 'D1 50 ]

-- The definition of the "sideways" input, which the network is fed recurrently.
type Shakespearian =
  RecurrentInputs  '[ R (LSTM 50 100), R (LSTM 100 50), F (FullyConnected 50 50), F Logit]

randomNet :: MonadRandom m => m Shakespeare
randomNet = randomRecurrent

-- | Load and vectorize the Haskell input into a compressed int representation.
-- Map the prelude functions and Haskell lexer tokens to a different int for
-- better granularity.
loadHaskell :: FilePath -> ExceptT String IO (Vector Int, M.Map Int Int, Vector Int)
loadHaskell path = do
  contents <- lift $ readFile path
  let tokens = tokenize contents
  (m,cs)       <- ExceptT . return $ hotMap (Proxy :: Proxy 50) tokens
  hot          <- ExceptT . return . note "Couldn't generate hot values" $ traverse (`M.lookup` m) tokens
  return (V.fromList hot, m, cs)

-- | Load the data files and prepare a map of characters to a compressed int representation.
loadShakespeare :: FilePath -> ExceptT String IO (Vector Int, M.Map Char Int, Vector Char)
loadShakespeare path = do
  contents     <- lift $ readFile path
  let annotated = annotateCapitals contents
  (m,cs)       <- ExceptT . return $ hotMap (Proxy :: Proxy 41) annotated
  hot          <- ExceptT . return . note "Couldn't generate hot values" $ traverse (`M.lookup` m) annotated
  return (V.fromList hot, m, cs)

trainSlice :: LearningParameters -> Shakespeare -> Shakespearian -> Vector Int -> Int -> Int -> (Shakespeare, Shakespearian)
trainSlice !rate !net !recIns input offset size =
  let e = fmap (x . oneHot) . V.toList $ V.slice offset size input
  in case reverse e of
    (o : l : xs) ->
      let examples = reverse $ (l, Just o) : ((,Nothing) <$> xs)
      in  trainRecurrent rate net recIns examples
    _ -> error "Not enough input"
    where
      x = fromMaybe (error "Hot variable didn't fit.")

runShakespeare :: ShakespeareOpts -> ExceptT String IO ()
runShakespeare ShakespeareOpts {..} = do
  (shakespeare, oneHotMap, oneHotDictionary) <- loadShakespeare trainingFile
  (net0, i0) <- lift $
    case loadPath of
      Just loadFile -> netLoad loadFile
      Nothing -> (,0) <$> randomNet

  (trained, bestInput) <- lift $ foldM (\(!net, !io) size -> do
    xs <- take (iterations `div` 10) <$> getRandomRs (0, length shakespeare - size - 1)
    let (!trained, !bestInput) = foldl' (\(!n, !i) offset -> trainSlice rate n i shakespeare offset size) (net, io) xs
    results <- take 1000 <$> generateParagraph trained bestInput temperature oneHotMap oneHotDictionary ( S1D $ konst 0)
    putStrLn ("TRAINING STEP WITH SIZE: " ++ show size)
    putStrLn (unAnnotateCapitals results)
    return (trained, bestInput)
    ) (net0, i0) $ replicate 10 sequenceSize

  case savePath of
    Just saveFile -> lift . B.writeFile saveFile $ runPut (put trained >> put bestInput)
    Nothing -> return ()

runHaskell :: ShakespeareOpts -> ExceptT String IO ()
runHaskell ShakespeareOpts {..} = do
  (shakespeare, oneHotMap, oneHotDictionary) <- loadHaskell trainingFile
  (net0, i0) <- lift $
    case loadPath of
      Just loadFile -> netLoad loadFile
      Nothing -> (,0) <$> randomNet

  (trained, bestInput) <- lift $ foldM (\(!net, !io) size -> do
    xs <- take (iterations `div` 10) <$> getRandomRs (0, length shakespeare - size - 1)
    let (!trained, !bestInput) = foldl' (\(!n, !i) offset -> trainSlice rate n i shakespeare offset size) (net, io) xs
    results <- take 1000 <$> generateParagraph trained bestInput temperature oneHotMap oneHotDictionary ( S1D $ konst 0)
    putStrLn ("TRAINING STEP WITH SIZE: " ++ show size)
    putStrLn (unwords $ map (revTokenMap M.!) results)
    return (trained, bestInput)
    ) (net0, i0) $ replicate 10 sequenceSize

  case savePath of
    Just saveFile -> lift . B.writeFile saveFile $ runPut (put trained >> put bestInput)
    Nothing -> return ()


generateParagraph :: forall layers shapes n a. (Last shapes ~ 'D1 n, Head shapes ~ 'D1 n, KnownNat n, Ord a)
  => RecurrentNetwork layers shapes
  -> RecurrentInputs layers
  -> Double
  -> M.Map a Int
  -> Vector a
  -> S ('D1 n)
  -> IO [a]
generateParagraph n s temperature hotmap hotdict =
  go s
    where
  go x y =
    do let (_, ns, o) = runRecurrent n x y
       un            <- sample temperature hotdict o
       Just re       <- return $ makeHot hotmap un
       rest          <- unsafeInterleaveIO $ go ns re
       return (un : rest)

data ShakespeareOpts = ShakespeareOpts {
    trainingFile :: FilePath
  , iterations   :: Int
  , rate         :: LearningParameters
  , sequenceSize :: Int
  , temperature  :: Double
  , loadPath     :: Maybe FilePath
  , savePath     :: Maybe FilePath
  }

shakespeare' :: Parser ShakespeareOpts
shakespeare' = ShakespeareOpts <$> argument str (metavar "TRAIN")
                               <*> option auto (long "examples" <> short 'e' <> value 1000000)
                               <*> (LearningParameters
                                    <$> option auto (long "train_rate" <> short 'r' <> value 0.01)
                                    <*> option auto (long "momentum" <> value 0.95)
                                    <*> option auto (long "l2" <> value 0.000001)
                                    )
                               <*> option auto (long "sequence-length" <> short 's' <> value 50)
                               <*> option auto (long "temperature" <> short 't' <> value 0.4)
                               <*> optional (strOption (long "load"))
                               <*> optional (strOption (long "save"))


netLoad :: FilePath -> IO (Shakespeare, Shakespearian)
netLoad modelPath = do
  modelData <- B.readFile modelPath
  either fail return $ runGet get modelData

-- Replace capitals with an annotation and the lower case letter
-- http://fastml.com/one-weird-trick-for-training-char-rnns/
annotateCapitals :: String -> String
annotateCapitals (x : rest)
    | isUpper x
    = '^' : toLower x : annotateCapitals rest
    | otherwise
    = x : annotateCapitals rest
annotateCapitals []
    = []

unAnnotateCapitals :: String -> String
unAnnotateCapitals ('^' : x : rest)
    = toUpper x : unAnnotateCapitals rest
unAnnotateCapitals (x : rest)
    =  x : unAnnotateCapitals rest
unAnnotateCapitals []
    = []

-- | Tag the 'Nothing' value of a 'Maybe'
note :: a -> Maybe b -> Either a b
note a = maybe (Left a) Right

shakespeare_main :: IO ()
shakespeare_main = do
    shopts <- execParser (info (shakespeare' <**> helper) idm)
    res <- runExceptT $ runHaskell shopts
    case res of
      Right () -> pure ()
      Left err -> putStrLn err

