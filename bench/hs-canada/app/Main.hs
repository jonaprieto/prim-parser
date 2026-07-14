{-# LANGUAGE OverloadedStrings #-}
module Main where
import Text.Megaparsec
import Text.Megaparsec.Char
import Data.Text (Text)
import qualified Data.Text.IO as TIO
import Data.Void
import Data.Char (isDigit)
type P = Parsec Void Text
isNumCh c = isDigit c || c `elem` ("-+.eE"::String)
isLet c = (c>='a'&&c<='z')||(c>='A'&&c<='Z')
pJsonV :: P Int
pJsonV = space *> (jnum <|> jstr <|> jkw <|> jarr <|> jobj)
  where jnum = 1 <$ takeWhile1P Nothing isNumCh
        jstr = 1 <$ (char '"' *> takeWhileP Nothing (/='"') *> char '"')
        jkw = 1 <$ takeWhile1P Nothing isLet
        jarr = char '[' *> space *> ((\xs -> 1+sum xs) <$> sepBy pJsonV (char ',')) <* space <* char ']'
        pr = space *> (char '"' *> takeWhileP Nothing (/='"') *> char '"') *> space *> char ':' *> pJsonV
        jobj = char '{' *> space *> ((\xs -> 1+sum xs) <$> sepBy pr (char ',')) <* space <* char '}'
main :: IO ()
main = do
  s <- TIO.readFile "bench-data/canada.json"
  print (either (const (-1)) id (parse (pJsonV <* space) "" s))
