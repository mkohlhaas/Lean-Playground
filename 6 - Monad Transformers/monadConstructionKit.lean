-- ------------------------ --
-- A Monad Construction Kit --
-- ------------------------ --

-- -------------------- --
-- Failure with OptionT --
-- -------------------- --

-- OptionT IO String, aka IO (Option String)
def getSomeInput : OptionT IO String := do -- in OptionT IO (basically in IO monad)
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trimAscii.copy
  if trimmed == ""
    then failure
    else pure trimmed

structure UserInfo where
  name           : String
  favoriteBeetle : String

-- OptionT IO UserInfo, aka IO (Option UserInfo)
def getUserInfo : OptionT IO UserInfo := do -- in OptionT IO (basically in IO monad)
  IO.println "What is your name?"                         -- IO
  let name ← getSomeInput                                 -- OptionT IO String
  IO.println "What is your favorite species of beetle?"   -- IO
  let beetle ← getSomeInput                               -- OptionT IO String
  pure ⟨name, beetle⟩                                     -- OptionT IO UserInfo

def interact : IO Unit := do -- in IO monad
  match ← getUserInfo with
  | none                => IO.eprintln "Missing info"
  | some ⟨name, beetle⟩ => IO.println s!"Hello {name}, whose favorite beetle is {beetle}."

-- ------------------ --
-- The Monad Instance --
-- ------------------ --

-- Errors:
-- instance [Monad m] : Monad (OptionT m) where
--   pure x           := pure $ some x
--   bind action next := do
--                       match (← action) with
--                       | none   => pure none
--                       | some v => next v

-- with noisy, ugly type annotations
instance [Monad m] : Monad (OptionT m) where
  pure x           := (pure (some x) : m (Option _))
  bind action next := (do
                       match (← action) with
                       | none   => pure none
                       | some v => next v : m (Option _))

-- with OptionT.mk
instance [Monad m] : Monad (OptionT m) where
  pure x           := OptionT.mk $ pure $ some x
  bind action next := OptionT.mk do
                                 match ← action with
                                 | none   => pure none
                                 | some v => next v
 
-- ----------------------- --
-- An Alternative Instance --
-- ----------------------- --

instance [Monad m] : Alternative (OptionT m) where
 failure    := OptionT.mk $ pure none
 orElse x y := OptionT.mk do
                          match ← x with
                          | none        => y ()
                          | some result => pure $ some result

-- ------- --
-- Lifting --
-- ------- --

instance [Monad m] : MonadLift m (OptionT m) where
  monadLift action := OptionT.mk do -- in `m (Option α)`
                                 pure $ some (← action)

-- ---------- --
-- Exceptions --
-- ---------- --

instance {ε : Type u} {m : Type u → Type v} [Monad m] : Monad (ExceptT ε m) where
  pure x           := ExceptT.mk $ pure (Except.ok x)
  bind result next := ExceptT.mk do
                                 match ← result with
                                 | .error e => pure $ .error e
                                 | .ok x    => next x
 
instance [Monad m] : MonadLift (Except ε) (ExceptT ε m) where
  monadLift action := ExceptT.mk $ pure action                                
