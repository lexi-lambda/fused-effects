{-# LANGUAGE DeriveFunctor, FlexibleInstances, MultiParamTypeClasses, TypeOperators, UndecidableInstances #-}
module Control.Carrier.Empty.Maybe
( -- * Empty effect
  module Control.Effect.Empty
  -- * Empty carrier
, runEmpty
, EmptyC(..)
  -- * Re-exports
, Carrier
, Member
, run
) where

import Control.Applicative (Alternative (..), liftA2)
import Control.Carrier.Class
import Control.Effect.Empty
import Control.Monad (MonadPlus (..))
import Control.Monad.Fail
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Prelude hiding (fail)

-- | Run an 'Empty' effect, returning 'Nothing' for aborted computations, or 'Just' the result otherwise.
--
--   prop> run (runError empty)    === Nothing
--   prop> run (runError (pure a)) === Just a
runEmpty :: EmptyC m a -> m (Maybe a)
runEmpty = runEmptyC

newtype EmptyC m a = EmptyC { runEmptyC :: m (Maybe a) }
  deriving (Functor)

instance Applicative m => Applicative (EmptyC m) where
  pure = EmptyC . pure . Just
  EmptyC f <*> EmptyC a = EmptyC (liftA2 (<*>) f a)

-- $
--   prop> run (runEmpty empty) === Nothing
instance Applicative m => Alternative (EmptyC m) where
  empty = EmptyC (pure Nothing)
  EmptyC a <|> EmptyC b = EmptyC (liftA2 (<|>) a b)

instance Monad m => Monad (EmptyC m) where
  EmptyC a >>= f = EmptyC (a >>= maybe (pure Nothing) (runEmptyC . f))

instance MonadFix m => MonadFix (EmptyC m) where
  mfix f = EmptyC (mfix (runEmpty . maybe (error "mfix (EmptyC): function returned failure") f))

instance MonadFail m => MonadFail (EmptyC m) where
  fail = lift . fail

instance MonadIO m => MonadIO (EmptyC m) where
  liftIO = lift . liftIO

instance (Alternative m, Monad m) => MonadPlus (EmptyC m)

instance MonadTrans EmptyC where
  lift = EmptyC . fmap Just

instance (Carrier sig m, Effect sig) => Carrier (Empty :+: sig) (EmptyC m) where
  eff (L Empty) = EmptyC (pure Nothing)
  eff (R other) = EmptyC (eff (handle (Just ()) (maybe (pure Nothing) runEmptyC) other))


-- $setup
-- >>> :seti -XFlexibleContexts
-- >>> import Test.QuickCheck