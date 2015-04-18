%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\subsection{Records}
\label{sec:records}

Alternatively, circuits can be represented using records. 

%if False

> {-# OPTIONS -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators 
>  -XMultiParamTypeClasses -XFlexibleContexts -XOverlappingInstances 
>  -XIncoherentInstances -XNoMonomorphismRestriction -XDeriveFunctor #-}

> newtype Width2     = Width2     {width :: Int}
> newtype WellSized2 = WellSized2 {wellSized :: Bool}

> type Compose i1 i2 = (i1, i2)

%endif

\noindent We define the following datatype with record syntax for circuit 
constructions:

> data Circuit inn out = Circuit {
>   identity :: Int -> out,
>   fan      :: Int -> out,
>   above    :: inn -> inn -> out,
>   beside   :: inn -> inn -> out,
>   stretch  :: [Int] -> inn -> out
> }

Each interpretation corresponds to a value of the datatype. For example, for 
{\em width} and {\em wellSized} interpretations, we define two values {\em widthAlg} 
and {\em wsAlg}:

> widthAlg :: (Width2 :<: inn) => Circuit inn Width2 
> widthAlg = Circuit {
>   identity = \w    -> Width2 w,
>   fan      = \w    -> Width2 w,
>   above    = \x y  -> Width2 (gwidth x),
>   beside   = \x y  -> Width2 (gwidth x + gwidth y),
>   stretch  = \xs x -> Width2 (sum xs)
> }

> wsAlg :: (Width2 :<: inn, WellSized2 :<: inn) => 
>           Circuit inn WellSized2
> wsAlg = Circuit {
>   identity = \w    -> WellSized2 True,
>   fan      = \w    -> WellSized2 True,
>   above    = \x y  -> WellSized2 (gwellSized x && gwellSized y && 
>                                   gwidth x == gwidth y),
>   beside   = \x y  -> WellSized2 (gwellSized x && gwellSized y),
>   stretch  = \xs x -> WellSized2 (gwellSized x && 
>                                   length xs == gwidth x)
> }

Circuit composition is also defined as a value of the datatype:

> (<+>) :: (inn1 :<: inn, inn2 :<: inn) => 
>           Circuit inn inn1 -> Circuit inn inn2 -> 
>           Circuit inn (Compose inn1 inn2)
> (<+>) a1 a2 = Circuit {
>   identity = \w    -> (identity a1 w, identity a2 w),
>   fan      = \w    -> (fan a1 w, fan a2 2),
>   above    = \x y  -> (above a1 (inter x) (inter y), 
>                        above a2 (inter x) (inter y)),
>   beside   = \x y  -> (beside a1 (inter x) (inter y),
>                        beside a2 (inter x) (inter y)),
>   stretch  = \xs x -> (stretch a1 xs (inter x), 
>                        stretch a2 xs (inter x))
> }

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

Now we can compose interpretations smoothly. For example, {\em widthAlg} and 
{\em wsAlg} can be composed together as follows:

> cAlg :: Circuit (Compose Width2 WellSized2) 
>                 (Compose Width2 WellSized2)
> cAlg = widthAlg <+> wsAlg

Each construct is associated with the corresponding field in cAlg:

> cidentity = identity cAlg
> cfan = fan cAlg
> cabove = above cAlg
> cbeside = beside cAlg
> cstretch = stretch cAlg

The Brent-Kung circuit in Figure 1 can be constructed as follows:

> c = 
>   (cfan 2 `cbeside` cfan 2) `cabove`
>   cstretch [2,2] (cfan 2) `cabove`
>   (cidentity 1 `cbeside` cfan 2 `cbeside` cidentity 1)

%if False

> width4 :: (Width2 :<: e) => e -> Int
> width4 = gwidth

> wellSized4 :: (WellSized2 :<: e) => e -> Bool
> wellSized4 = gwellSized

%endif

It can be evaluated directly using {\em gwidth} and {\em gwellSized}.



