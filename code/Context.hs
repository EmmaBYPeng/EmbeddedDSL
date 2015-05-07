{-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances -XNoMonomorphismRestriction -XDeriveFunctor #-}

module Context where

data Circuit inn out = Circuit {
  identity :: Int -> out,
  fan      :: Int -> out,
  above    :: inn -> inn -> out,
  beside   :: inn -> inn -> out,
  stretch  :: [Int] -> inn -> out
}

newtype Width     = Width     {width :: Int}
newtype Depth     = Depth     {depth :: Int}
newtype WellSized = WellSized {wellSized :: Bool}
newtype Layout    = Layout    {layout :: (Int -> Int) -> [[(Int, Int)]]}

type Compose i1 i2 = (i1, i2)

widthAlg :: (Width :<: inn) => Circuit inn Width 
widthAlg = Circuit {
  identity = \w    -> Width w,
  fan      = \w    -> Width w,
  above    = \x y  -> Width (gwidth x),
  beside   = \x y  -> Width (gwidth x + gwidth y),
  stretch  = \xs x -> Width (sum xs)
}

depthAlg :: (Depth :<: inn) => Circuit inn Depth 
depthAlg = Circuit {
  identity = \w    -> Depth 0,
  fan      = \w    -> Depth 1,
  above    = \x y  -> Depth (gdepth x + gdepth y),
  beside   = \x y  -> Depth (gdepth x `max` gdepth y),
  stretch  = \xs x -> Depth (gdepth x)
}

wsAlg :: (Width :<: inn, WellSized :<: inn) => Circuit inn WellSized
wsAlg = Circuit {
  identity = \w    -> WellSized True,
  fan      = \w    -> WellSized True,
  above    = \x y  -> WellSized (gwellSized x && gwellSized y && 
                                 gwidth x == gwidth y),
  beside   = \x y  -> WellSized (gwellSized x && gwellSized y),
  stretch  = \xs x -> WellSized (gwellSized x && length xs == gwidth x)
}

layoutAlg :: (Width :<: inn, Layout :<: inn) => Circuit inn Layout
layoutAlg = Circuit {
  identity = \w   -> Layout (\f -> []), 
  fan      = \w   -> Layout (\f -> [[(f 0, f i) | i <- [1..w-1]]]),
  above    = \x y -> Layout (\f -> (glayout x f ++ glayout y f)),
  beside   = \x y -> 
    Layout (\f -> lzw (++) (glayout x f) (glayout y (((gwidth x)+) . f))),
  stretch  = \xs x -> 
    Layout (\f -> glayout x (pred . ((scanl1 (+) xs)!!) . f))
}

lzw :: (a -> a -> a) -> [a] -> [a] -> [a]
lzw f [] ys         = ys
lzw f xs []         = xs
lzw f (x:xs) (y:ys) = f x y : lzw f xs ys

(<+>) :: (inn1 :<: inn, inn2 :<: inn) => 
         Circuit inn inn1 -> Circuit inn inn2 -> Circuit inn (Compose inn1 inn2)
(<+>) a1 a2 = Circuit {
  identity = \w    -> (identity a1 w, identity a2 w),
  fan      = \w    -> (fan a1 w, fan a2 2),
  above    = \x y  -> (above a1 (inter x) (inter y), above a2 (inter x) (inter y)),
  beside   = \x y  -> (beside a1 (inter x) (inter y), beside a2 (inter x) (inter y)),
  stretch  = \xs x -> (stretch a1 xs (inter x), stretch a2 xs (inter x))
}

class i :<: e where
  inter :: e -> i

instance i :<: i where
  inter = id

instance i :<: (Compose i i2) where
  inter = fst

instance (i :<: i2) => i :<: (Compose i1 i2) where
  inter = inter . snd

gwidth :: (Width :<: e) => e -> Int
gwidth = width . inter

gdepth :: (Depth :<: e) => e -> Int
gdepth = depth . inter

gwellSized :: (WellSized :<: e) => e -> Bool
gwellSized = wellSized . inter

glayout :: (Layout :<: e) => e -> ((Int -> Int) -> [[(Int, Int)]])
glayout = layout . inter

-- Test
-- Need explicit type annotation here!
cAlg :: Circuit (Compose Depth (Compose Layout (Compose Width WellSized))) 
                (Compose Depth (Compose Layout (Compose Width WellSized)))
cAlg = depthAlg <+> (layoutAlg <+> (widthAlg <+> wsAlg))

cidentity = identity cAlg
cfan = fan cAlg
cabove = above cAlg
cbeside = beside cAlg
cstretch = stretch cAlg

c = (cfan 2 `cbeside` cfan 2) `cabove`
    cstretch [2,2] (cfan 2) `cabove`
    (cidentity 1 `cbeside` cfan 2 `cbeside` cidentity 1)

test1 = gwidth c
test2 = gwellSized c
test3 = gdepth c
test4 = (glayout c) id

