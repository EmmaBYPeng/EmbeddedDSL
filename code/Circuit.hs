{-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances #-}

module Circuit where

class Circuit circuit where
  identity :: Int -> circuit
  fan      :: Int -> circuit
  above    :: circuit -> circuit -> circuit
  beside   :: circuit -> circuit -> circuit
  stretch  :: [Int] -> circuit -> circuit

-- Alternative 1
{-
data GCircuit inn out = GCircuit {
  gidentity :: Int -> out, 
  gfan      :: Int -> out, 
  gabove    :: inn -> inn -> out, 
  gbeside   :: inn -> inn -> out, 
  gstretch  :: [Int] -> inn -> out
}-}

newtype Width     = Width     {width :: Int}
newtype Depth     = Depth     {depth :: Int}
newtype WellSized = WellSized {wellSized :: Bool}
newtype Layout1   = Layout1   {layout1 :: [[(Int, Int)]]}
newtype Layout2   = Layout2   {layout2 :: (Int -> Int) -> [[(Int, Int)]]}

type Compose i1 i2 = (i1, i2)

instance Circuit Width where
  identity w   = Width w
  fan w        = Width w
  above x y    = x
  beside x y   = Width (width x + width y)
  stretch xs x = Width (sum xs)

instance Circuit Depth where
  identity w   = Depth 0
  fan w        = Depth 1
  above x y    = Depth (depth x + depth y)
  beside x y   = Depth (depth x `max` depth y)
  stretch xs x = x

-- Dependent case 1
instance (Circuit width, Width :<: width) => 
          Circuit (Compose WellSized width) where
  identity w   = (WellSized True, identity w)
  fan w        = (WellSized True, fan w)
  above x y    = (WellSized (gwellSized x && gwellSized y 
                             && (gwidth x == gwidth y)),
                  above (inter x) (inter y))
  beside x y   = (WellSized (gwellSized x && gwellSized y),
                  beside (inter x) (inter y))
  stretch xs x = (WellSized (gwellSized x && length xs == gwidth x),
                  stretch xs (inter x))

{-
instance (Circuit inn, Width :<: inn, WellSized :<: inn) => Circuit inn WellSized where
  identity w   = WellSized True
  fan w        = WellSized True
  above x y    = WellSized (gwellSized x && gwellSized y && (gwidth x == gwidth y))
  beside x y   = WellSized (gwellSized x && gwellSized y)
  stretch xs x = WellSized (gwellSized x && length xs == gwidth x)
-}

-- Dependent case 2
instance Circuit (Compose Layout1 Width) where
  identity w   = (Layout1 [], identity w)
  fan w        = (Layout1 [[(0,i) | i <- [1..w-1]]], identity w)
  above x y    = (Layout1 (lo1 x ++ lo1 y) 
                  , above (inter x) (inter y)) 
  beside x y   = (Layout1 (lzw (++) (lo1 x) (shift (gwidth x) (lo1 y)))
                  , beside (inter x) (inter y))
  stretch xs x = (Layout1 (map (map (connect xs)) (lo1 x))
                  , stretch xs (inter x))

lzw :: (a -> a -> a) -> [a] -> [a] -> [a]
lzw f [] ys         = ys
lzw f xs []         = xs
lzw f (x:xs) (y:ys) = f x y : lzw f xs ys

shift w = map (map (pmap (w+)))
connect gwellSized = pmap (pred . ((scanl1 (+) gwellSized)!!))

pmap :: (a -> b) -> (a, a) -> (b, b)
pmap f (x,y) = (f x, f y)

-- Context sensitive case
instance Circuit (Compose Layout2 Width) where
  identity w   = (Layout2 (\f -> []), identity w) 
  fan w        = (Layout2 (\f -> [[(f 0, f i) | i <- [1..w-1]]]), fan w) 
  above x y    = (Layout2 (\f -> (lo2 x f ++ lo2 y f)) 
                  , above (inter x) (inter y))
  beside x y   = (Layout2 (\f -> lzw (++) (lo2 x f) (lo2 y (((gwidth x)+) . f)))
                  , beside (inter x) (inter y)) 
  stretch xs x = (Layout2 (\f -> lo2 x (pred . (vs!!) . f))
                  , stretch xs (inter x))
    where vs = scanl1 (+) xs

instance (Circuit i1, Circuit i2) => Circuit (Compose i1 i2) where
  identity w   = (identity w, identity w) 
  fan w        = (fan w, fan w)
  above x y    = (above (inter x) (inter y), above (inter x) (inter y))
  beside x y   = (beside (inter x) (inter y), beside (inter x) (inter y))
  stretch xs x = (stretch xs (inter x), stretch xs (inter x))

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

lo1 :: (Layout1 :<: e) => e -> [[(Int, Int)]]
lo1 = layout1 . inter

lo2 :: (Layout2 :<: e) => e -> ((Int -> Int) -> [[(Int, Int)]])
lo2 = layout2 . inter

-- Equivalent to lo1
lo2_id :: (Layout2 :<: e) => e -> [[(Int, Int)]]
lo2_id = flip lo2 id
  
c1 :: Circuit circuit => circuit
c1 = (fan 2 `beside` fan 2) `above`
     stretch [2,2] (fan 2) `above`
     (identity 1 `beside` fan 2 `beside` identity 1)

test1 = gwidth (c1 :: Width)
test2 = gdepth (c1 :: Compose Width Depth)
test3 = gdepth (c1 :: Compose Depth Width)
test4 = gwellSized (c1 :: Compose WellSized Width) 
test5 = lo1 (c1 :: Compose Layout1 Width)
test6 = lo2_id (c1 :: Compose Layout2 Width)



