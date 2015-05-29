%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{Extensibility in Both Dimensions}
\label{sec:extensibility}

%if False

> {-# OPTIONS
>  -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses
>  -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
>  -XNoMonomorphismRestriction -XDeriveFunctor -XExistentialQuantification
>  -XRankNTypes -XUndecidableInstances #-}

> module Extensibility where 
>

> type Size = Int
> newtype Width = Width {unwidth :: Size}
> newtype Depth = Depth {undepth :: Size}
> newtype WellSized = WellSized {unwellSized :: Bool}

> type Compose i1 i2 = (i1, i2)

> class i :<: e where
>   inter :: e -> i

> instance i :<: i where
>   inter = id

> instance i :<: (Compose i i2) where
>   inter = fst

> instance (i :<: i2) => i :<: (Compose i1 i2) where
>   inter = inter . snd

> gwidth :: (Width :<: e) => e -> Size
> gwidth = unwidth . inter

> gwellSized :: (Width :<: e, WellSized :<: e) => e -> Bool
> gwellSized = unwellSized . inter

%endif

> data IdentityF' r  = IdentityF' Size     deriving Functor
> data FanF' r       = FanF' Size          deriving Functor
> data AboveF' r     = AboveF' r r         deriving Functor
> data BesideF' r    = BesideF' r r        deriving Functor
> data StretchF' r   = StretchF' [Size] r  deriving Functor

> data (f :+: g) e = Inl (f e) | Inr (g e) deriving Functor
> infixr :+:

> type CircuitF' = IdentityF' :+: FanF' :+: AboveF' :+: BesideF' :+: StretchF'
> data Fix f = In (f (Fix f))
> type Circuit' = Fix CircuitF'

> class (Functor f, Functor g) => f :< g where
>   inj :: f a -> g a
>
> instance Functor f => f :< f where
>   inj = id
>
> instance (Functor f, Functor g) => f :< (f :+: g) where
>   inj = Inl
>
> instance (Functor f, Functor g, Functor h, f :< g) => f :< (h :+: g) where
>   inj = Inr . inj

> fold :: Functor f => (f a -> a) -> Fix f -> a
> fold alg (In x) = alg (fmap (fold alg ) x)

> class (Functor f, Width :<: r) => WidthAlg f r where
>   widthAlg' :: f r -> Width
> 
> instance (Width :<: r, WidthAlg f r, WidthAlg g r) => WidthAlg (f :+: g) r where
>   widthAlg' (Inl x) = widthAlg' x
>   widthAlg' (Inr y) = widthAlg' y
>
> instance (Width :<: r) => WidthAlg IdentityF' r where
>   widthAlg' (IdentityF' w)    = Width w
> 
> instance (Width :<: r) => WidthAlg FanF' r where
>   widthAlg' (FanF' w)         = Width w
> 
> instance (Width :<: r) => WidthAlg AboveF' r where
>   widthAlg' (AboveF' x y)     = Width (gwidth x)
> 
> instance (Width :<: r) => WidthAlg BesideF' r where
>   widthAlg' (BesideF' x y)    = Width (gwidth x + gwidth y)
>
> instance (Width :<: r) => WidthAlg StretchF' r where
>   widthAlg' (StretchF' ws x)  = Width (sum ws)


> class (Functor f, WellSized :<: r, Width :<: r) => WellSizedAlg f r where
>   wsAlg' :: f r -> WellSized
> 
> instance (WellSized :<: r, Width :<: r, WellSizedAlg f r, WellSizedAlg g r) 
>   => WellSizedAlg (f :+: g) r where
>   wsAlg' (Inl x) = wsAlg' x
>   wsAlg' (Inr y) = wsAlg' y

> instance (WellSized :<: r, Width :<: r) => WellSizedAlg IdentityF' r where
>   wsAlg' (IdentityF' w)    = WellSized True
>
> instance (WellSized :<: r, Width :<: r) => WellSizedAlg FanF' r where
>   wsAlg' (FanF' w)         = WellSized True
> 
> instance (WellSized :<: r, Width :<: r) => WellSizedAlg AboveF' r where
>   wsAlg' (AboveF' x y)     = WellSized (gwellSized x && gwellSized y && gwidth x == gwidth y)
> 
> instance (WellSized :<: r, Width :<: r) => WellSizedAlg BesideF' r where
>   wsAlg' (BesideF' x y)    = WellSized (gwellSized x && gwellSized y)
>
> instance (WellSized :<: r, Width :<: r) => WellSizedAlg StretchF' r where
>   wsAlg' (StretchF' ws x)  = WellSized (gwellSized x && length ws == gwidth x)

%if False

> identity' :: (IdentityF' :< f) => Size -> Fix f
> identity' w    = In (inj (IdentityF' w))
> 
> fan' :: (FanF' :< f) => Size -> Fix f
> fan' w         = In (inj (FanF' w))
>
> above' :: (AboveF' :< f) => Fix f -> Fix f -> Fix f
> above' x y     = In (inj (AboveF' x y))
>
> beside' :: (BesideF' :< f) => Fix f -> Fix f -> Fix f
> beside' x y    = In (inj (BesideF' x y))
>
> stretch' :: (StretchF' :< f) => [Size] -> Fix f -> Fix f
> stretch' ws x  = In (inj (StretchF' ws x))

%endif

> class (Functor f) => Comb f where
>   (<+>) :: (a :<: r, b :<: r) => (f r -> a) -> (f r -> b) -> (f r -> (Compose a b))
>
> instance (Comb f, Comb g) => Comb (f :+: g) where
>   (<+>) a1 a2 (Inl f)  = (a1 (Inl f), a2 (Inl f))
>   (<+>) a1 a2 (Inr g)  = (a1 (Inr g), a2 (Inr g))
>
> instance Comb IdentityF' where
>   (<+>) a1 a2 f = (a1 f, a2 f)
>
> instance Comb FanF' where
>   (<+>) a1 a2 f = (a1 f, a2 f)
>
> instance Comb AboveF' where
>   (<+>) a1 a2 f = (a1 f, a2 f)
>
> instance Comb BesideF' where
>   (<+>) a1 a2 f = (a1 f, a2 f)
>
> instance Comb StretchF' where
>   (<+>) a1 a2 f = (a1 f, a2 f)

> compAlg' = widthAlg' <+> wsAlg'

> eval' = fold compAlg'
>
> width'      = gwidth . eval'
> wellSized'  = gwellSized . eval'

> c3 :: Circuit'
> c3 = 
>   (fan' 2 `beside'` fan' 2) `above'`
>   stretch' [2, 2] (fan' 2) `above'`
>   (identity' 1 `beside'` fan' 2 `beside'` identity' 1)

> test1 = width' (c3 :: Circuit')
> test2 = wellSized' (c3 :: Circuit')

