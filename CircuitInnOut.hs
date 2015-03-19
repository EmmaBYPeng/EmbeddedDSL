{-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances -XScopedTypeVariables -XUndecidableInstances #-}

module CircuitInnOut where

data Proxy a = Proxy

-- All types must appear in the function in the type class (Haskell limitation)
class Circuit inn out where
  identity :: Proxy inn -> Int -> out
  fan      :: Proxy inn -> Int -> out
  above    :: inn -> inn -> out
  beside   :: inn -> inn -> out
  stretch  :: [Int] -> inn -> out

newtype Width     = Width     {width :: Int}
newtype Depth     = Depth     {depth :: Int}
newtype WellSized = WellSized {wellSized :: Bool}

type Compose i1 i2 = (i1, i2)

instance (Circuit inn Width, Width :<: inn) => Circuit inn Width where
  identity (Proxy :: Proxy inn) w = Width w
  fan      (Proxy :: Proxy inn) w = Width w
  above x y                       = Width (gwidth x)
  beside x y                      = Width (gwidth x + gwidth y)
  stretch xs x                    = Width (sum xs)

instance (Circuit inn Depth, Depth :<: inn) => Circuit inn Depth where
  identity (Proxy :: Proxy inn) w = Depth 0
  fan      (Proxy :: Proxy inn) w = Depth 1
  above x y                       = Depth (gdepth x + gdepth y)
  beside x y                      = Depth (gdepth x `max` gdepth y)
  stretch xs x                    = Depth (gdepth x)

instance (Circuit inn WellSized, Width :<: inn, WellSized :<: inn)
         => Circuit inn WellSized where
  identity (Proxy :: Proxy inn) w = WellSized True
  fan      (Proxy :: Proxy inn) w = WellSized True
  above x y    = WellSized (gwellSized x && gwellSized y && gwidth x == gwidth y)
  beside x y   = WellSized (gwellSized x && gwellSized y)
  stretch xs x = WellSized (gwellSized x && length xs == gwidth x)

-- x, y :: inn, no need to use inter here
instance (Circuit inn inn1, Circuit inn inn2) => Circuit inn (Compose inn1 inn2) where
  identity (Proxy :: Proxy inn) w = ((identity (Proxy :: Proxy inn) w) :: inn1,
                                     (identity (Proxy :: Proxy inn) w) :: inn2)
  fan      (Proxy :: Proxy inn) w = ((fan (Proxy :: Proxy inn) w)      :: inn1,
                                     (fan (Proxy :: Proxy inn) w)      :: inn2)
  above x y    = ((above x y)    :: inn1, (above x y)    :: inn2)
  beside x y   = ((beside x y)   :: inn1, (beside x y)   :: inn2)
  stretch xs x = ((stretch xs x) :: inn1, (stretch xs x) :: inn2)

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

-- Test
type ComposedType = Compose Depth (Compose Width WellSized)

gfan w        = fan (Proxy :: Proxy ComposedType) w      :: ComposedType
gidentity w   = identity (Proxy :: Proxy ComposedType) w :: ComposedType 
gbeside x y   = (beside x y)                             :: ComposedType
gabove x y    = (above x y)                              :: ComposedType
gstretch xs x = (stretch xs x)                           :: ComposedType

c = (gfan 2 `gbeside` gfan 2) `gabove`
    gstretch [2,2] (gfan 2) `gabove`
    (gidentity 1 `gbeside` gfan 2 `gbeside` gidentity 1)

test1 = gwidth c
test2 = gdepth c
test3 = gwellSized c



