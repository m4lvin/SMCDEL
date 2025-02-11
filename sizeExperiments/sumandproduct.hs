{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables #-}
module Main (main) where

import Data.List
import System.IO

import SMCDEL.Examples.SumAndProduct.General
import SMCDEL.Language
import qualified SMCDEL.Symbolic.S5_CUDD as S5_CUDD
import qualified SMCDEL.Symbolic.S5 as S5_CAC
import qualified SMCDEL.Internal.MyHaskCUDD as MyHaskCUDD
import SMCDEL.Internal.MyHaskCUDD

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  gatherSizeData [50,64,75,100,125,128,150,175,200,225,250,256,275,300,325,350]

genSapSizesCac :: Int -> [Int]
genSapSizesCac n = map (\(S5_CAC.KnS _ lawb _) -> S5_CAC.size lawb) $
  updateSequence (genSapKnStruct n) [ genSapForm1 n, genSapForm2 n, genSapForm3 n ]

genSapSizesCudd :: forall a b c . DdCtx a b c => Int -> IO [Int]
genSapSizesCudd n = do
  start <- genSapKnStructCudd @a @b @c n -- also creates manager!
  return $ map (\(S5_CUDD.KnS mgr _ lawb _) -> MyHaskCUDD.size mgr lawb) $
    updateSequence start  [ genSapForm1 n, genSapForm2 n, genSapForm3 n ]

genSapSizesCuddViaConvert :: forall b c . (Convert b c) => Int -> IO [Int]
genSapSizesCuddViaConvert n = do
  start <- genSapKnStructCudd @B @O1 @I1 n -- also creates manager!
  let context = map fromEnum $ vocabOf start
  return $ map (\(S5_CUDD.KnS mgr _ lawb _) -> MyHaskCUDD.size mgr (convertToZDD mgr context lawb :: Dd Z b c)) $
    updateSequence start  [ genSapForm1 n, genSapForm2 n, genSapForm3 n ]

gatherSizeData :: [Int] -> IO ()
gatherSizeData ns = do
  putStrLn $ "Running SAP benchmark for ns=" ++ show ns ++ " and writing results to sap.dat ..."
  writeFile "sap.dat" $ "# Note: round -1 indicates the average.\n" ++ firstLine ++ "\n"
  mapM_ linesFor ns
  putStrLn "Done."
  where
    firstLine = intercalate "\t" $ ["n","round"] ++ map fst variants
    variants =
      -- label result columns with elimination rules, not i/o complements:
      [ ("BDD", return . genSapSizesCac)
      , ("BDDc",  genSapSizesCudd @B @O1 @I1)
      -- via conversion, fast:
      , ("T0", genSapSizesCuddViaConvert @O1 @I1)
      , ("T1", genSapSizesCuddViaConvert @O0 @I1)
      , ("E0", genSapSizesCuddViaConvert @O1 @I0)
      , ("E1", genSapSizesCuddViaConvert @O0 @I0)
      -- directly on ZDDs, slow:
      -- , ("T0", genSapSizesCudd @Z @O1 @I1)
      -- , ("T1", genSapSizesCudd @Z @O0 @I1)
      -- , ("E0", genSapSizesCudd @Z @O1 @I0)
      -- , ("E1", genSapSizesCudd @Z @O0 @I0)
      ]
    linesFor n = do
      putStrLn $ "Running for n = " ++ show n
      results <- mapM (`snd` n) variants
      appendFile "sap.dat" $ unlines $
        [ intercalate "\t" (show n : show k : map (\xs -> show (xs !! k)) results)
        | k <- [0..3] ]
        ++
        [ intercalate "\t" (show n : "-1" : map (\xs -> show (fromIntegral (sum xs) / 4 :: Double)) results) ]
