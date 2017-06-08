{-# LANGUAGE OverloadedStrings #-}

module Main where

import Prelude      as P
import Data.Text    as T
import Data.Text.IO as TIO
import System.FilePath
import System.Environment

altName :: String
altName = ""

cleanup :: Text -> Text
cleanup = T.unlines
        . P.dropWhile (T.null . T.filter (/= ' '))
        . P.concatMap T.lines
        . fmap (P.head . splitOn "\\end{code}")
        . P.tail
        . splitOn "\\begin{code}"

alterName :: Text -> Text
alterName txt =
  let (modName, whereRest) = T.breakOn "where" txt
      (mod    , name)      = T.breakOnEnd "module" modName
  in T.concat [ mod, stripEnd name, T.pack altName, " ", whereRest ]

main :: IO ()
main = do
  (fp : _)  <- getArgs
  cleanedUp <- alterName . cleanup <$> TIO.readFile fp
  let (name, _) = splitExtension fp
  TIO.writeFile (name ++ altName ++ ".agda") cleanedUp
