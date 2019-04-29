{-# LANGUAGE DataKinds, KindSignatures, DefaultSignatures, DeriveFunctor, FlexibleInstances, FunctionalDependencies, RankNTypes, UndecidableInstances, TypeFamilies, TypeApplications, ScopedTypeVariables, TypeOperators, PolyKinds, GADTs, ConstraintKinds, FlexibleInstances, FlexibleContexts, AllowAmbiguousTypes #-}
module Control.Effect.Carrier
( HFunctor(..)
, Effect(..)
, Carrier(..)
, Union
, Member
, handlePure
, handleCoercible
, send
, inj
, prj
, collapse
, decomp
) where

import Data.Coerce
import Data.Typeable

class HFunctor h where
  -- | Functor map. This is required to be 'fmap'.
  --
  --   This can go away once we have quantified constraints.
  fmap' :: (a -> b) -> (h m a -> h m b)
  default fmap' :: Functor (h m) => (a -> b) -> (h m a -> h m b)
  fmap' = fmap
  {-# INLINE fmap' #-}

  -- | Higher-order functor map of a natural transformation over higher-order positions within the effect.
  hmap :: (forall x . m x -> n x) -> (h m a -> h n a)

-- | The class of effect types, which must:
--
--   1. Be functorial in their last two arguments, and
--   2. Support threading effects in higher-order positions through using the carrier’s suspended state.
class HFunctor sig => Effect sig where
  -- | Handle any effects in a signature by threading the carrier’s state all the way through to the continuation.
  handle :: Functor f
         => f ()
         -> (forall x . f (m x) -> n (f x))
         -> sig m (m a)
         -> sig n (n (f a))

-- | An extensible, type-safe union. The @r@ type parameter is a type-level
-- list of effects, any one of which may be held within the 'Union'.
data Union (r :: [(* -> *) -> * -> *]) (m :: * -> *) a where
  Union
      :: Effect (IndexOf r n)
      => SNat n
         -- ^ A proof that the effect is actually in @r@.
      -> (IndexOf r n) m a
         -- ^ The effect to wrap. The functions 'prj' and 'decomp' can help
         -- retrieve this value later.
      -> Union r m a

instance Functor (Union r m) where
  fmap f (Union w t) = Union w (fmap' f t)

instance HFunctor (Union r) where
  fmap' f (Union w t) = Union w (fmap' f t)
  hmap h (Union w t) = Union w (hmap h t)

instance Effect (Union r) where
  handle s f (Union w e) = Union w $ handle s f e

-- | A proof that the effect @e@ is available somewhere inside of the effect
-- stack @r@.
type Member e r = Member' e r

type Member' e r =
  ( Find r e
  , e ~ IndexOf r (Found r e)
  )

data Dict c where Dict :: c => Dict c

induceTypeable :: SNat n -> Dict (Typeable n)
induceTypeable SZ = Dict
induceTypeable (SS _) = Dict
{-# INLINE induceTypeable #-}

-- | The kind of type-level natural numbers.
data Nat = Z | S Nat

-- | A singleton for 'Nat'.
data SNat :: Nat -> * where
  SZ :: SNat 'Z
  SS :: Typeable n => SNat n -> SNat ('S n)


type family IndexOf (ts :: [k]) (n :: Nat) :: k where
  IndexOf (k ': _) 'Z = k
  IndexOf (_ ': ks) ('S n) = IndexOf ks n


type family Found (ts :: [k]) (t :: k) :: Nat where
  Found (t ': _) t = 'Z
  Found (_ ': ts) t = 'S (Found ts t)


class Typeable (Found r t) => Find (r :: [k]) (t :: k) where
  finder :: SNat (Found r t)

instance {-# OVERLAPPING #-} Find (t ': z) t where
  finder = SZ
  {-# INLINE finder #-}

instance ( Find z t
         , Found (_1 ': z) t ~ 'S (Found z t)
         ) => Find (_1 ': z) t where
  finder = SS $ finder @_ @z @t
  {-# INLINE finder #-}

-- | Decompose a 'Union'. Either this union contains an effect @e@---the head
-- of the @r@ list---or it doesn't.
decomp :: Union (e ': r) m a -> Either (Union r m a) (e m a)
decomp (Union p a) =
  case p of
    SZ   -> Right a
    SS n -> Left $ Union n a
{-# INLINE decomp #-}

------------------------------------------------------------------------------
-- | Attempt to take an @e@ effect out of a 'Union'.
prj :: forall e r a m
     . ( Member e r
       )
    => Union r m a
    -> Maybe (e m a)
prj (Union (s :: SNat n) a) =
  case induceTypeable s of
    Dict ->
      case eqT @n @(Found r e) of
        Just Refl -> Just a
        Nothing -> Nothing
{-# INLINE prj #-}


------------------------------------------------------------------------------
-- | Like 'decomp', but allows for a more efficient
-- 'Polysemy.Interpretation.reinterpret' function.
-- decompCoerce
--     :: Union (e ': r) m a
--     -> Either (Union (f ': r) m a) (e m a)
-- decompCoerce (Union p a) =
--   case p of
--     SZ -> Right a
--     SS n -> Left (Union (SS n) a)
-- {-# INLINE decompCoerce #-}


------------------------------------------------------------------------------
-- | Retrieve the last effect in a 'Union'.
collapse :: Union '[e] m a -> e m a
collapse (Union SZ a) = a
collapse _ = error "impossible"
-- {-# INLINE extract #-}


------------------------------------------------------------------------------
-- | An empty union contains nothing, so this function is uncallable.
-- absurdU :: Union '[] m a -> b
-- absurdU = absurdU


------------------------------------------------------------------------------
-- | Weaken a 'Union' so it is capable of storing a new sort of effect.
-- weaken :: Union r m a -> Union (e ': r) m a
-- weaken (Union n a) =
--   case induceTypeable n of
--     Dict -> Union (SS n) a
-- {-# INLINE weaken #-}


------------------------------------------------------------------------------
-- | Lift an effect @e@ into a 'Union' capable of holding it.
inj :: forall r e a m. (Effect e, Member e r) => e m a -> Union r m a
inj e = Union (finder @_ @r @e) e
{-# INLINE inj #-}

-- | The class of carriers (results) for algebras (effect handlers) over signatures (effects), whose actions are given by the 'eff' method.
class (Monad m) => Carrier (sig :: [(* -> *) -> * -> *])  m | m -> sig where
  -- | Construct a value in the carrier for an effect signature (typically a sum of a handled effect and any remaining effects).
  eff :: Union sig m (m a) -> m a

-- | Apply a handler specified as a natural transformation to both higher-order and continuation positions within an 'HFunctor'.
handlePure :: HFunctor sig => (forall x . f x -> g x) -> sig f (f a) -> sig g (g a)
handlePure handler = hmap handler . fmap' handler
{-# INLINE handlePure #-}

-- | Thread a 'Coercible' carrier through an 'HFunctor'.
--
--   This is applicable whenever @f@ is 'Coercible' to @g@, e.g. simple @newtype@s.
handleCoercible :: (HFunctor sig, Coercible f g) => sig f (f a) -> sig g (g a)
handleCoercible = handlePure coerce
{-# INLINE handleCoercible #-}

send :: (Effect effect, Member effect sig, Carrier sig m) => effect m (m a) -> m a
send = eff . inj
{-# INLINE send #-}
