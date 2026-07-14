{-# LANGUAGE OverloadedStrings #-}
module Main where

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Text (Text)
import qualified Data.Text.IO as TIO
import Data.Void (Void)
import Data.Char (isAlphaNum, isDigit)
import Control.Exception (evaluate)
import Control.Monad (replicateM)
import System.CPUTime (getCPUTime)
import Text.Printf (printf)

type P = Parsec Void Text

dataDir :: String
dataDir = "../bench-data/"

natP :: P Int
natP = L.decimal

alnum1 :: P ()
alnum1 = () <$ takeWhile1P Nothing isAlphaNum

-- integers: sum of comma-separated nats
pInts :: P Int
pInts = sum <$> sepBy1 natP (char ',')

-- sexp: atom count.  atom | '(' ws S (ws S)* ws ')'
pSexp :: P Int
pSexp = (1 <$ takeWhile1P Nothing isAlphaNum) <|> lst
  where lst = do _ <- char '('; space
                 x  <- pSexp
                 xs <- many (try (space *> pSexp))
                 space; _ <- char ')'
                 pure (x + sum xs)

-- csv: total cell count
pCsv :: P Int
pCsv = sum <$> sepBy1 pRow (char '\n')
  where pRow = length <$> sepBy1 natP (char ',')

-- json: validate flat [nat,nat,...] -> 1
pJson :: P Int
pJson = do _ <- char '['; space
           _ <- sepBy natP (char ',' >> space)
           space; _ <- char ']'
           pure 1

-- lambda: node count in `\v. body | v`
pLam :: P Int
pLam = absL <|> var
  where var  = 1 <$ (takeWhile1P Nothing isAlphaNum <* space)
        absL = do _ <- char '\\'; space
                  _ <- takeWhile1P Nothing isAlphaNum; space
                  _ <- char '.'; space
                  n <- pLam
                  pure (n + 1)

-- words: count space-separated alnum tokens
pWords :: P Int
pWords = do _ <- takeWhile1P Nothing isAlphaNum
            xs <- many (char ' ' *> (takeWhile1P Nothing isAlphaNum))
            pure (1 + length xs)

-- brackets: nesting depth of `nat | '[' B ']'`
pBr :: P Int
pBr = (0 <$ natP) <|> (do _ <- char '['; d <- pBr; _ <- char ']'; pure (d + 1))

-- full RFC-JSON: node count. dispatch number|string|keyword|array|object
isNumCh :: Char -> Bool
isNumCh c = isDigit c || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'
isLet :: Char -> Bool
isLet c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
pJsonV :: P Int
pJsonV = space *> (jnum <|> jstr <|> jkw <|> jarr <|> jobj)
  where jnum = 1 <$ takeWhile1P Nothing isNumCh
        jstr = 1 <$ (char '"' *> takeWhileP Nothing (/= '"') *> char '"')
        jkw  = 1 <$ takeWhile1P Nothing isLet
        jarr = char '[' *> space *> ((\xs -> 1 + sum xs) <$> sepBy pJsonV (char ',')) <* space <* char ']'
        pair = space *> (char '"' *> takeWhileP Nothing (/= '"') *> char '"') *> space *> char ':' *> pJsonV
        jobj = char '{' *> space *> ((\xs -> 1 + sum xs) <$> sepBy pair (char ',')) <* space <* char '}'

-- netstring: LEN:DATA, — needs monadic bind (do-notation)
pNet :: P Int
pNet = fmap sum (some netOne)
  where netOne = do { n <- natP; _ <- char ':'; _ <- takeP Nothing n; _ <- char ','; pure 1 }

runP :: P Int -> Text -> Int
runP p input = either (const (-1)) id (parse (p <* eof) "" input)

bench :: String -> P Int -> IO ()
bench name p = do
  input <- TIO.readFile (dataDir ++ name ++ ".txt")
  let v = runP p input
  if v < 0 then printf "  %-8s: PARSE FAIL\n" name
  else do
    let reps = 200 :: Int
    times <- replicateM reps $ do
      t0 <- getCPUTime
      r  <- evaluate (runP p input)
      t1 <- getCPUTime
      pure (fromIntegral (t1 - t0) / 1e9 :: Double)  -- picoseconds -> ms
    printf "  %-8s: %.3f ms (chk %d)\n" name (minimum times) v

main :: IO ()
main = do
  putStrLn "megaparsec (GHC -O2), same input files:"
  bench "integers" pInts
  bench "sexp"     pSexp
  bench "csv"      pCsv
  bench "json"     pJson
  bench "lambda"   pLam
  bench "words"    pWords
  bench "brackets" pBr
  bench "net"      pNet
  -- industrial: real 2.3MB canada.json
  input <- TIO.readFile (dataDir ++ "canada.json")
  let v = either (const (-1)) id (parse (pJsonV <* space <* eof) "" input)
  times <- replicateM 20 $ do
    t0 <- getCPUTime
    r  <- evaluate (either (const (-1)) id (parse (pJsonV <* space <* eof) "" input))
    t1 <- getCPUTime
    pure (fromIntegral (t1 - t0) / 1e9 :: Double)
  printf "  canada.json: %.3f ms (nodes %d)\n" (minimum times) v
