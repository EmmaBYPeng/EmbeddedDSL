{-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances -XNoMonomorphismRestriction -XDeriveFunctor #-}

module DependentAlgebras where

import Prelude hiding (print)

data ArithF r = Lit Int | Add r r deriving (Show, Functor)

newtype Eval = Eval {eval' :: Int}

evalAlg :: (Eval :<: r) => ArithF r -> Eval
evalAlg (Lit x)      = Eval x
evalAlg (Add e1 e2)  = Eval $ eval e1 + eval e2

newtype Print = Print {print' :: String}

printAlg :: (Print :<: r) => ArithF r -> Print
printAlg (Lit x)       = Print $ show x
printAlg (Add e1 e2)   = Print $ print e1 ++ " + " ++ print e2

printAlg2 :: (Eval :<: r, Print :<: r) => ArithF r -> Print
printAlg2 (Lit x)       = Print $ show x
printAlg2 (Add e1 e2)   = Print $ print e1 ++ " + " ++ print e2 ++ " = " ++ show (eval e1 + eval e2)

type GAlg r a = ArithF r -> a

(<+>) :: (a :<: r, b :<: r) => GAlg r a -> GAlg r b -> GAlg r (a,b)
(<+>) a1 a2 fa = (a1 fa, a2 fa)

-- test :: (Print :<: r, Eval :<: r) => GAlg r (Eval,Print)
comp = evalAlg <+> printAlg2

data Fix f = In {out :: f (Fix f)}

fold :: Functor f => (f a -> a) -> Fix f -> a
fold alg = alg . fmap (fold alg) . out

test = print $ fold comp (In (Add (In (Lit 2)) (In (Lit 3))))

-- Solution: generic interpretations!

type Compose i1 i2 = (i1,i2)

class i :<: e where -- not doing DTC on products, but on the 
   inter :: e -> i 

instance i :<: i where 
   inter = id

instance i :<: (Compose i i2) where
   inter = fst

instance (i :<: i2) => i :<: (Compose i1 i2) where
   inter = inter . snd

eval :: (Eval :<: e) => e -> Int -- robust! works as long there is an Eval in e
eval = eval' . inter

print :: (Print :<: e) => e -> String -- robust! works as long there is an Eval in e
print = print' . inter
