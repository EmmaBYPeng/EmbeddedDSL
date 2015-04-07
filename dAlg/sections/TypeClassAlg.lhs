%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\subsection{Type Class with Proxies}
\label{sec:type-class-proxies}

%if False

> {-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators 
>  -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances 
>  -XScopedTypeVariables -XUndecidableInstances #-}

%endif

> data Proxy a = Proxy

> class Circuit inn out where
>   identity :: Proxy inn -> Int -> out
>   fan      :: Proxy inn -> Int -> out
>   above    :: inn       -> inn -> out
>   beside   :: inn       -> inn -> out
>   stretch  :: [Int]     -> inn -> out

%if False

> newtype Width2     = Width2     {width :: Int}
> newtype WellSized2 = WellSized2 {wellSized :: Bool}

> type Compose i1 i2 = (i1, i2)

%endif

> instance (Circuit inn Width2, Width2:<: inn) => 
>           Circuit inn Width2 where
>   identity (Proxy :: Proxy inn) w = Width2 w
>   fan      (Proxy :: Proxy inn) w = Width2 w
>   above x y                       = Width2(gwidth x)
>   beside x y                      = Width2(gwidth x + gwidth y)
>   stretch xs x                    = Width2(sum xs)

> instance (Circuit inn WellSized2, 
>           Width2:<: inn, 
>           WellSized2:<: inn) => Circuit inn WellSized2 where
>   identity (Proxy :: Proxy inn) w = WellSized2 True
>   fan      (Proxy :: Proxy inn) w = WellSized2 True
>   above x y    = WellSized2(gwellSized x && gwellSized y && 
>                             gwidth x == gwidth y)
>   beside x y   = WellSized2(gwellSized x && gwellSized y)
>   stretch xs x = WellSized2(gwellSized x && 
>                             length xs == gwidth x)

> instance (Circuit inn inn1, Circuit inn inn2) => 
>           Circuit inn (Compose inn1 inn2) where
>   identity (Proxy :: Proxy inn) w = 
>            ((identity (Proxy :: Proxy inn) w) :: inn1,
>             (identity (Proxy :: Proxy inn) w) :: inn2)
>   fan      (Proxy :: Proxy inn) w = 
>            ((fan (Proxy :: Proxy inn) w)      :: inn1,
>             (fan (Proxy :: Proxy inn) w)      :: inn2)
>   above x y    = ((above x y)    :: inn1, (above x y)    :: inn2)
>   beside x y   = ((beside x y)   :: inn1, (beside x y)   :: inn2)
>   stretch xs x = ((stretch xs x) :: inn1, (stretch xs x) :: inn2)

%if False

> class i :<: e where
>   inter :: e -> i

> instance i :<: i where
>   inter = id

> instance i :<: (Compose i i2) where
>   inter = fst

> instance (i :<: i2) => i :<: (Compose i1 i2) where
>   inter = inter . snd
 
> gwidth :: (Width2 :<: e) => e -> Int
> gwidth = width . inter

> gwellSized :: (WellSized2 :<: e) => e -> Bool 
> gwellSized = wellSized . inter

%endif

> type ComposedType = Compose Width2 WellSized2

> gfan w        = 
>   fan (Proxy :: Proxy ComposedType) w      :: ComposedType
> gidentity w   = 
>   identity (Proxy :: Proxy ComposedType) w :: ComposedType 
> gbeside x y   = (beside x y)   :: ComposedType
> gabove x y    = (above x y)    :: ComposedType
> gstretch xs x = (stretch xs x) :: ComposedType

> c = (gfan 2 `gbeside` gfan 2) `gabove`
>     gstretch [2,2] (gfan 2) `gabove`
>     (gidentity 1 `gbeside` gfan 2 `gbeside` gidentity 1)

> width4 :: (Width2 :<: e) => e -> Int
> width4 = gwidth

> wellSized4 :: (WellSized2 :<: e) => e -> Bool
> wellSized4 = gwellSized




