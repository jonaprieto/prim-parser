{-# LANGUAGE OverloadedStrings, BangPatterns #-}
module Main where
import qualified Data.ByteString as BS
import qualified Data.Attoparsec.ByteString.Char8 as A
import Data.Attoparsec.ByteString.Char8 (Parser)
import Control.Applicative ((<|>))
import System.Environment (getArgs)
import GHC.Clock (getMonotonicTimeNSec)
import Data.IORef

ws :: Parser ()
ws = A.skipWhile (\c -> c==' '||c=='\n'||c=='\r'||c=='\t')

-- Same logic as the Lean gJson: fold child-counts (no list), frequency-ordered
-- ordered choice (num, arr, obj, str, keyword). Node count only, no AST.
value :: Parser Int
value = ws *> (num <|> arr <|> obj <|> str <|> keyword)
  where
    num = 1 <$ A.takeWhile1 (\c -> (c>='0'&&c<='9')||c=='-'||c=='+'||c=='.'||c=='e'||c=='E')
    str = 1 <$ (A.char '"' *> A.takeWhile (/= '"') *> A.char '"')
    keyword = 1 <$ A.takeWhile1 (\c -> c>='a'&&c<='z')
    arr = do _ <- A.char '['; n <- sepFold value; ws; _ <- A.char ']'; pure (1 + n)
    obj = do _ <- A.char '{'; n <- sepFold pair; ws; _ <- A.char '}'; pure (1 + n)
    pair = do ws; _ <- A.char '"'; _ <- A.takeWhile (/= '"'); _ <- A.char '"'; ws; _ <- A.char ':'; value
    sepFold p = (do x <- p; go x) <|> pure 0
      where go !acc = (do _ <- A.char ','; y <- p; go (acc + y)) <|> pure acc

run1 :: BS.ByteString -> Int
run1 bs = case A.parseOnly value bs of Right n -> n; Left _ -> -1

{-# NOINLINE opaque #-}
opaque :: Int -> BS.ByteString -> BS.ByteString
opaque _ b = b

main :: IO ()
main = do
  args <- getArgs
  bs <- BS.readFile "bench-data/canada.json"
  if "time" `elem` args
    then do
      best <- newIORef (1/0 :: Double)
      let loop :: Int -> IO ()
          loop 0 = pure ()
          loop k = do
            t0 <- getMonotonicTimeNSec
            let !n = run1 (opaque k bs)
            t1 <- getMonotonicTimeNSec
            modifyIORef' best (min (fromIntegral (t1 - t0) / 1e6))
            n `seq` loop (k - 1)
      loop 100
      b <- readIORef best
      putStrLn ("count=" ++ show (run1 bs) ++ " parse_ms=" ++ show b)
    else print (run1 bs)
