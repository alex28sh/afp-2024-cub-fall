{-# LANGUAGE NoMonomorphismRestriction #-}

module Final where

import Common
import Control.Monad.State hiding (fix)
import Text.Printf
import Prelude hiding (compare)
import qualified Data.Function

-- Finally tagless, partially evaluated
-- Oleg Kiselyov

-- data Dsl env t where
--   IntConst :: Int -> Dsl env Int
--   BoolConst :: Bool -> Dsl env Bool

--   IntBin  :: BinOp (Int -> Int -> Int)    -> Dsl env Int  -> Dsl env Int  -> Dsl env Int
--   BoolBin :: BinOp (Bool -> Bool -> Bool) -> Dsl env Bool -> Dsl env Bool -> Dsl env Bool
--   Compare :: BinOp (Int -> Int -> Bool)   -> Dsl env Int  -> Dsl env Int  -> Dsl env Bool
--   IfE :: Dsl env Bool -> Dsl env t -> Dsl env t -> Dsl env t

--   Var :: env t -> Dsl env t
--   Lam :: (Dsl env t1 -> Dsl env t2) -> Dsl env (t1 -> t2)
--   App :: Dsl env (t1 -> t2) -> Dsl env t1 -> Dsl env t2
--   Fix :: (Dsl env t -> Dsl env t) -> Dsl env t

class Calc repr where
  intConst :: Int -> repr Int
  intBin :: BinOp (Int -> Int -> Int) -> repr Int -> repr Int -> repr Int

class Cond repr where
  boolConst :: Bool -> repr Bool
  boolBin :: BinOp (Bool -> Bool -> Bool) -> repr Bool -> repr Bool -> repr Bool
  compare :: BinOp (Int -> Int -> Bool) -> repr Int -> repr Int -> repr Bool
  ifExpr :: repr Bool -> repr t -> repr t -> repr t

class Lam repr where
  lam :: (repr a -> repr b) -> repr (a -> b)
  app :: repr (a -> b) -> repr a -> repr b
  fix :: (repr a -> repr a) -> repr a

newtype Box a = Box { unbox :: a }

instance Calc Box where 
  intConst = Box 
  intBin cond l r = Box $ getOp cond (unbox l) (unbox r)

instance Cond Box where 
  boolConst = Box 
  boolBin cond l r = Box $ getOp cond (unbox l) (unbox r)
  compare cond l r = Box $ getOp cond (unbox l) (unbox r)
  ifExpr x l r = if unbox x then l else r 

instance Lam Box where 
  lam f = Box $ \x -> unbox $ f $ Box x 
  app f = Box . unbox f . unbox 
  fix f = Box $ Data.Function.fix (unbox . f . Box)

instance Calc S where 
  intConst x = S $ return $ show x 
  intBin cond l r = S $
    unS l >>= \al -> 
    unS r >>= \ar -> 
    return $ formatBinOp cond al ar

instance Cond S where 
  boolConst x = S $  
    return $ show x 
  boolBin cond l r = S $ 
    unS l >>= \al -> 
    unS r >>= \ar -> 
    return $ formatBinOp cond al ar
  compare cond l r = S $  
    unS l >>= \al -> 
    unS r >>= \ar -> 
    return $ formatBinOp cond al ar
  ifExpr x l r = S $ 
    unS l >>= \al -> 
    unS r >>= \ar -> 
    unS x >>= \ax ->
    return $ printf "if %s then %s else %s" ax al ar
  
instance Lam S where 
  lam f = S $ do
    x <- newVar
    let sx = show x 
    body <- unS (f (S $ return sx)) 
    return $ printf "(lam \\%s -> %s)" sx body
  app f a = S $ 
    unS f >>= \uf -> 
    unS a >>= \ua -> 
    return $ printf "(%s %s)" uf ua
  fix f = S $ do 
    x <- newVar
    let sx = show x 
    body <- unS (f (S $ return sx)) 
    return $ printf "(fix \\%s -> %s)" sx body

eval :: Box a -> a
eval = unbox

view :: S a -> String
view x = evalState (unS x) (VarState 0)

andOp :: (Cond repr) => repr Bool -> repr Bool -> repr Bool
andOp = boolBin (BinOp "&&" (&&))

mulOp :: (Calc repr) => repr Int -> repr Int -> repr Int
mulOp = intBin (BinOp "*" (*))

addOp :: (Calc repr) => repr Int -> repr Int -> repr Int
addOp = intBin (BinOp "+" (+))

leqOp :: (Cond repr) => repr Int -> repr Int -> repr Bool
leqOp = compare (BinOp "<=" (<=))

tipow :: (Cond repr, Calc repr, Lam repr) => repr (Int -> Int -> Int)
tipow =
  lam
    ( \x ->
        fix
          ( \self ->
              lam
                ( \n ->
                    ifExpr
                      (leqOp n (intConst 0))
                      (intConst 1)
                      (mulOp x (app self (addOp n (intConst (-1)))))
                )
          )
    )

tipowApplied :: (Cond repr, Calc repr, Lam repr) => Int -> Int -> repr Int
tipowApplied x y = app (app tipow (intConst x)) (intConst y)

main = do
  let expr = tipowApplied 4 2
  putStrLn $ view expr
  print $ eval expr