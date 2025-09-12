{-# LANGUAGE StandaloneDeriving #-}

module Main
  ( main
  ) where

import           Hyperdual.Isabelle.CodeExport (fa_test, hyp_fa_test_safe,
                                                itsqrt)
import qualified Hyperdual.Isabelle.Hyperdual  as H

deriving instance Eq a => Eq (H.Hyperdual a)
deriving instance Ord a => Ord (H.Hyperdual a)

main :: IO ()
main = do
  let x = H.Hyperdual 1.5 1.0 1.0 0.0
  putStrLn ("x = " ++ show x)
  let r = fa_test (H.base x)
  putStrLn ("real only: " ++ show r)
  let h = hyp_fa_test_safe x
  putStrLn ("hyp. ext.: " ++ show h)
  let paper = H.Hyperdual 4.4978 4.0534 4.0534 9.4631
  putStrLn ("paper minus ours: " ++ show (H.minus_hyperdual paper h))
  putStrLn "==="
  let x = H.Hyperdual 10000.0 1.0 1.0 0.0
  putStrLn ("x = " ++ show x)
  let h = itsqrt x
  putStrLn ("hyp. iterative sqrt: " ++ show h)
