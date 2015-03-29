{-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances -XNoMonomorphismRestriction -XDeriveFunctor -XUndecidableInstances -XTypeFamilies #-}

module CircuitTF where

type Compose i1 i2 = (i1, i2) 

class Circuit inn out where
  type Super inn out :: *
  identity :: Int -> out
  fan      :: Int -> out
  above    :: Super inn out -> Super inn out -> out
  beside   :: Super inn out -> Super inn out -> out
  stretch  :: [Int] -> Super inn out -> out

-- id2 :: Circuit inn out => Int -> out
-- id2 = identity

newtype Width     = Width     {width :: Int}
newtype WellSized = WellSized {wellSized :: Bool}

instance (Width :<: inn) => Circuit inn Width where
  type Super inn Width = inn
  identity w   = Width w
  fan w        = Width w
  above x y    = Width (gwidth x)
  beside x y   = Width (gwidth x + gwidth y)
  stretch xs x = Width (sum xs)

instance (Width :<: inn, WellSized :<: inn) => Circuit inn WellSized where
  type Super inn WellSized = inn
  identity w   = WellSized True
  fan w        = WellSized True
  above x y    = WellSized (gwellSized x && gwellSized y && gwidth x == gwidth y)
  beside x y   = WellSized (gwellSized x && gwellSized y)
  stretch xs x = WellSized (gwellSized x && length xs == gwidth x)

instance (Circuit inn out1, Circuit inn out2) => Circuit inn (Compose out1 out2) where
  type Super inn (Compose out1 out2) = inn
  identity w = undefined
  fan w = undefined
  above x y = ((above (inter x) (inter y)) :: out1, 
               (above (x :: Super inn out2) (y :: Super inn out2)) :: out2)
  beside x y = undefined
  stretch xs x = undefined

 
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

gwellSized :: (WellSized :<: e) => e -> Bool
gwellSized = wellSized . inter

{-
-- Closed type family
-- How to represent (i :<: i2) in the first instance??
-- How to define inter? Type class?

type family (:<:) i e where
  i :<: (Compose i1 i2) = i
  i :<: (Compose i i2) = i
  i :<: i = i
-}

{-
-- Open type family, doesn't support overlapping types
class (:<:) e where
  type Sub e :: * 
  inter :: e -> Sub e 

instance (:<:) i where
  type Sub i = i
  inter = id

instance (:<:) (Compose i i2) where
  type Sub (Compose i i2) = i
  inter = fst
-}
