%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt
%include Paper.fmt

\section{Two-dimensional Extensibility}
\label{sec:extensibility}

%if False

> {-# OPTIONS
>  -XTypeSynonymInstances -XFlexibleInstances -XTypeOperators -XMultiParamTypeClasses
>  -XFlexibleContexts -XOverlappingInstances -XIncoherentInstances 
>  -XNoMonomorphismRestriction -XDeriveFunctor -XExistentialQuantification
>  -XRankNTypes -XUndecidableInstances #-}

> module Extensibility where 

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

For an embedded DSL, it is desirable if one can assemble the language and its 
interpretations from parts. On the one hand, we want to add new cases to a datatype
without modifying the existing code. On the other hand, we want to define new 
functions over the datatype modularly.

Swiestra's ``\emph{Datatypes \`a la Carte}"~\cite{swierstra08} 
provides a way for one to add new language constructs modularly. For the circuit DSL, 
the idea is to define a functor for each data variant separately, and it is
straightforward to add new data variants:

> data IdentityF' r  = IdentityF' Size     deriving Functor
> data FanF' r       = FanF' Size          deriving Functor
> data AboveF' r     = AboveF' r r         deriving Functor
> data BesideF' r    = BesideF' r r        deriving Functor
> data StretchF' r   = StretchF' [Size] r  deriving Functor

The following binary operator is used to combine different data variants together:

> data (f :+: g) e = Inl (f e) | Inr (g e) deriving Functor
> infixr :+:

By combining the above functors, we can obtain the composite functor 
$CircuitF'$, which is equivalent to $CircuitF$ we define in 
section~\ref{sec:f-algebra}:

> type CircuitF' = IdentityF' :+: FanF' :+: AboveF' :+: BesideF' :+: StretchF'

The composite circuit datatype $Circuit'$ can be recovered as:

> data Fix f = In (f (Fix f))
> type Circuit' = Fix CircuitF'

With the following type class expressing a subtyping relationship between functors,
smart constructors $identity'$, $fan'$, $above'$, $beside'$ and $stretch'$ are 
defined for convenient constructions of circuits:

> class (Functor f, Functor g) => f :< g where
>   inj :: f a -> g a

For example, the smart constructor for $Identity$ is:

> identity' :: (IdentityF' :< f) => Size -> Fix f
> identity' w = In (inj (IdentityF' w))

Other smart constructors can be defined in the exact same way.
One possible construction of the circuit in Figure~\ref{fig:circuit2} is as follows.
It is equivalent to $c_1$ we defined in section~\ref{sec:f-algebra}:

> c3 :: Circuit'
> c3 = 
>   (fan' 2 `beside'` fan' 2) `above'`
>   stretch' [2, 2] (fan' 2) `above'`
>   (identity' 1 `beside'` fan' 2 `beside'` identity' 1)


%if False

> instance Functor f => f :< f where
>   inj = id
>
> instance (Functor f, Functor g) => f :< (f :+: g) where
>   inj = Inl
>
> instance (Functor f, Functor g, Functor h, f :< g) => f :< (h :+: g) where
>   inj = Inr . inj

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

\noindent On the other hand, for modular interpretations, we first define the fold:

> fold :: Functor f => (f a -> a) -> Fix f -> a
> fold alg (In x) = alg (fmap (fold alg ) x)

Each interpretation corresponds to a type class of all data variants. For instance,
the following type class is defined for the interpretation of 'width':

> class (Functor f, Width :<: r) => WidthAlg f r where
>   widthAlg' :: f r -> Width

Restrictions on the input type of |widthAlg'| is explicitly stated such that |width|
is a member of the input type |r|. It is straigthforward to lift interpretations
over functors of composite type:

> instance (Width :<: r, WidthAlg f r, WidthAlg g r) => WidthAlg (f :+: g) r where
>   widthAlg' (Inl x)  = widthAlg' x
>   widthAlg' (Inr y)  = widthAlg' y

Interpretations for different constructors correspond to different instances of the
type class, and are defined in the same way as before. For example, following 
is the interpretation of 'width' for |IdentityF'|:

> instance (Width :<: r) => WidthAlg IdentityF' r where
>   widthAlg' (IdentityF' w)    = Width w

%if False

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

%endif

\noindent One may also want to have the dependent interpretation for 'wellSized':

> class (Functor f, WellSized :<: r, Width :<: r) => WellSizedAlg f r where
>   wsAlg' :: f r -> WellSized

%if False
> instance (WellSized :<: r, Width :<: r, WellSizedAlg f r, WellSizedAlg g r) => WellSizedAlg (f :+: g) r where
>   wsAlg' (Inl x) = wsAlg' x
>   wsAlg' (Inr y) = wsAlg' y
>
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

%endif

Now that we have separate interpretations defined for each functor, one last step
towards modularity is to have a composition operator that combines algebras 
together to allow dependent interpertations. In order to accomodate open datatypes,
composition operation is represented by the following type class:

> class (Functor f) => Comb f where
>   (<+>) :: (a :<: r, b :<: r) => (f r -> a) -> (f r -> b) -> (f r -> (Compose a b))

For each functor f that belongs to type class $Comb$, given that type |a| and |b| are
both members of type |r|, the binary operator |<+>| will compose an algebra of f from 
type |r| to |a| and another from type |r| to |b|, and returns a composed algebra 
from type |r| to |Compose a b|. First we define the operation for composite functors:

> instance (Comb f, Comb g) => Comb (f :+: g) where
>   (<+>) a1 a2 (Inl f)  = (a1 (Inl f), a2 (Inl f))
>   (<+>) a1 a2 (Inr g)  = (a1 (Inr g), a2 (Inr g))

Composition operation for each data variant corresponds to an instance of the
type class. For example, in the following instance we define the |<+>| operator for
$Identity$:

> instance Comb IdentityF' where
>   (<+>) a1 a2 f = (a1 f, a2 f)

%if False

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

%endif

Finally, we compose |widthAlg'| with |wsAlg'|, and form the compositional 
interpretation |eval'| with fold:

> compAlg' = widthAlg' <+> wsAlg'
>
> eval' = fold compAlg'

The following |width'| and |wellSized'| functions work for any flexibly typed
cirucits: 

> width'      = gwidth . eval'
> wellSized'  = gwellSized . eval'

For example, they can be applied to $c_3$ with its type explicitly stated:

%if False

> test1 = width' (c3 :: Circuit')
> test2 = wellSized' (c3 :: Circuit')

%endif

< >  width' (c3 :: Circuit')
< 4
<
< >  wellSized' (c3 :: Circuit')
< True

\noindent Therefore, while Swiestra's ``\emph{Datatypes \`a la Carte}"
~\cite{swierstra08} 
provides extensibility by allowing modular definition of datatypes, our techique 
works as its dual, providing a second dimensional extensibility by supporting fully
modular and compositional interpretations over modularly defined datatypes.
